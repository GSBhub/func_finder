#!/usr/bin/python
import sys
import argparse
import json
import jsongraph
import pprint
import r2pipe
import os
import logging
import re
import subprocess
import networkx as nx
import pygraphviz
import md5
import pprint
import collections
from collections import OrderedDict
from networkx.drawing import nx_agraph
from subprocess import check_call
from datetime import datetime

# template for all function data types

visited = {}
last_visited = {}
functions = []

class instruction:

    def __init__(self, base_addr, opcode):
        self.base_addr = hex(base_addr)
        params = opcode.split()
        self.opcode = params[0]
        self.params = params[1:]

    def __str__(self):
        if self.params:
            ret = "OP: {}\nParams: {}\n".format(self.opcode, self.params)
        else:
            ret = "OP: {}\n".format(self.opcode)
        return ret

class block:
    base_addr = 0x0
    fail = None
    jump = None

    def __init__(self, base_addr, seq_json):
        self.base_addr = hex(base_addr)
        self.seq_inst = OrderedDict()

        for op in seq_json:

            self.seq_inst[op[u'offset']] = instruction(op[u'offset'], op[u'opcode'])

    # returns a hash of the instructions
    def get_seq_inst(self): 
        temp = ur""
        for instruction in self.seq_inst.values():
            temp = temp + ur"{}".format(instruction.opcode)
        #logging.debug("block addr: {}, temp: {}\n".format(self.base_addr, temp))
        return [(md5.new(temp).hexdigest())]
    
    def ret_instruct_list(self):
        temp = ur""
        for instruction in self.seq_inst.values():
            temp = temp + ur"{}".format(instruction.opcode)
        #logging.debug("block addr: {}, temp: {}\n".format(self.base_addr, temp))
        return [temp]

    def print_inst(self):
        for instruction in self.seq_inst.itervalues():
            print(instruction)

    def __str__(self):
        ret = "Base_addr: 0x{:04x}\n".format(self.base_addr)
        if self.fail:
            ret += "\tFail: 0x{:04x}\n".format(self.fail.base_addr)
        if self.jump:
            ret += "\tJump: 0x{:04x}\n".format(self.jump.base_addr)
        return ret

class CFG:
    first = None 

    def __init__(self, json):
        if json:
            self.json = json[0]
        else:
            self.json = ""
        if u'offset' in self.json:
            self.base_addr = hex(json[0][u'offset'])
            if u'blocks' in json[0]:
                blocks = json[0][u'blocks']
                dict_block = {}
                # pass addr of first block, ops of first block, and pointers of first block

                self.first = block(blocks[000][u'offset'], blocks[000][u'ops'])

                # create a dictionary of all blocks
                for blk in blocks:
                    dict_block [blk[u'offset']] = [block(
                    blk[u'offset'], 
                    blk[u'ops']), blk]

                # match up all the block objects to their corresponding jump, fail addresses
                for key, pair in dict_block.items():
                    block_obj = pair[0]
                    block_json = pair[1]
                    # really, really sloppy method for now
                    # JSON has some weird errors where functions don't match up to the jump addresses
                    # might be an issue with the r2 debugger, but this is just a sloppy work-around
                    if u'fail' in block_json:
                        try:
                            block_obj.fail = dict_block[block_json[u'fail']][0]
                        except KeyError:
                            continue

                    if u'jump' in block_json:
                        try:
                            block_obj.jump = dict_block[block_json[u'jump']][0]
                        except KeyError:
                            continue
                self.first = dict_block[blocks[000][u'offset']][0]
            #else:      
                #raise KeyError()
        #else: 
            #raise KeyError()

    def __str__(self):
        ret = ""
        node = self.first
        while node is not None:
            ret += "{}\n".format(node)
            if node.fail:
                node = node.fail
            else:
                node = node.jump

        return ret              

    def get_feature(self):
        return "WIP"

class function:
    base_addr = 0x0 # address of the function
    json = ""      # json representation of function pointed to
    dot = ""       # dot representation of function pointed to

    def __init__(self, base_addr, cfg):
        self.base_addr = hex(base_addr)
        self.children = {}
        self.parents = {}
        self.cfg = cfg

    def __str__(self):
        
        ret = "0x{:04x}\n".format(self.base_addr)
        for child in self.children.values():
            ret += "\t{}".format(child)
        return ret

    def push_child(self, func):
        self.children[func.base_addr] = func


# locates the reset vector address from a valid M7700 binary
# using a currently open radare2 session
def get_rst(r2):
    r2.cmd("s 0xfffe")     # seek to the address for the reset vector (const for all of our binaries)
    logging.debug("R2 Command used: 's 0xfffe'")

    big_endian = str(r2.cmd("px0")) # print last two bytes of rst vector
    logging.debug("R2 Command used: 'px0'")

    rst = 0x0
    
    if big_endian:
        rst = int("{}{}".format(big_endian[2:4], big_endian[:2]), 16) # flip endianness of last two bytes
        logging.debug("rst vector address found at: 0x{:04x}".format(rst))
    else:
        logging.debug("ERR - reset vector search failed")

    return rst

# Helper function for recursive_parse_func
# grabs all child function calls from a function analysis in R2
def get_children(child_str):
    p = ur"JSR.*[^$](0x[0-9a-fA-F]{4})" # grab unrecognized funcs
    children = re.findall(p, child_str)
    p1 = ur"JSR.*fcn.0000([0-9a-fA-F]{4})"
    ch2 = re.findall(p1, child_str)
    children.extend(ch2) # grab recognized funcs

    int_children = list()
    for child in children:
        try:    
            int_children.append(int(child, 16))
        except TypeError:
            print (child)
    del children
    return int_children

# helper function for recursive parse func
# popluates 
def populate_cfg(addr, func_json):
    
    #json_obj = json.loads('{}'.format(func_json.decode('utf-8', 'ignore').encode('utf-8')), strict=True, object_pairs_hook=collections.OrderedDict)
    json_obj=json.loads(unicode(func_json, errors='ignore'), strict=False, object_pairs_hook=collections.OrderedDict)
    cfg = CFG(json_obj)
    return cfg

# recursively parses a binary, given address 
def recursive_parse_func(addr, r2):

    r2.cmd("0x{:04x}".format(addr))     # seek to address
    logging.debug("R2 Command used: '0x{:04x}'".format(addr))

    r2.cmd("aa")
    logging.debug("R2 Command used: aa")

    r2.cmd("sf.")
    addr = int(r2.cmd("s"), 16)

    child_str = r2.cmd("pdf")          # grab list of func params
    logging.debug("R2 Command used: 'pdf'")

    children = get_children(child_str) # pull children from func list

    if addr in visited.keys():
        func = visited[addr]
        return func
    else:
        cfg = populate_cfg(addr, r2.cmd("agj"))
        logging.debug("R2 Command used: 'agj'")
        func = function(addr, cfg)
        visited[addr] = func

    # need to make this recursion stop properly
    for child_addr in children:

        if child_addr in visited.keys(): # we don't need to recursively parse a function's children if it's already parsed
            visited[child_addr].parents[addr] = func          # store reference to parent in child object
            func.push_child(visited[child_addr])              # store the child in the base func object        

        else:
            visited[child_addr] = recursive_parse_func(child_addr, r2)
            visited[child_addr].parents[addr] = func          # store reference to parent in child object
            func.push_child(visited[child_addr])              # store the child in the base func object        

    return func

def func_parse_str(func_str):
    ret = []
    fs = func_str.splitlines()
    for line in fs:
        try:
            addr = int(line[:10], 16)
        except TypeError:
            continue
        if addr and addr >= 36864:
            ret.append(addr)
    return ret

def linear_parse_func(func, r2):
    func_list = []
    r2.cmd("af-")
    r2.cmd("aaa")
    func_str = r2.cmd('afl') # pull a complete list of functions
    logging.debug("R2 Command used: 'afl'")
    #r2.cmd("af-")

    l = func_parse_str(func_str)
    for addr in l:
        if addr not in visited.keys():
            func_list.append(recursive_parse_func(addr, r2)) # attempt to manually parse each address

    return func_list

# Creates an array of hashed features representing the instruction grams of each block within a function
def grab_features(func, visited):

    func_dict = {}

    if func in visited:
        return func_dict

    func_dict[ur"{}".format(func.base_addr)] = ur"{}".format(get_signature(func.cfg.first, []))
    visited.append(func)

    for child in func.children.values():
        func_dict.update(grab_features(child, visited))

    return func_dict

# return a list of hash values for an entire function
def get_signature(block, visited):

    result = []
    if block is None or block in visited: # Ignore blocks we've already resited
        return result
    
    #result.extend(block.get_seq_inst())
    result.extend(block.ret_instruct_list())

    visited.append(block)

    if block.jump:
        result.extend(get_signature(block.jump, visited))

    if block.fail:
        result.extend(get_signature(block.fail, visited))

    return result

def get_json(feature_dict):
    
    ret = ""
        
    ret = OrderedDict(json.dumps(feature_dict))
    pr = json.loads(ret)

    return ret

def get_start(infile):
    addr = 0x0000

    try:
        r2 = r2pipe.open(infile, ["-2"])           # load infile into R2 - error if not found
        r2.cmd("e asm.arch=m7700")
        addr = 0
        val = r2.cmd("/c CMP al #0xf0") # attempt to find the initial address
        if val is "":
            val = r2.cmd("/c CMP ax #0xf0f0") # attempt to find the initial address
        vals = val.split()

        try:
            r2.cmd("s {}".format(vals[0]))
        except IndexError:
            None
        addr = int(r2.cmd("s"),16)
        r2.quit()

    except IOError:
        print "Could not locate start of binary"
    return addr

# this method is responsible for
# - automatically parsing the rom file for functions
# - generating a graph from said functions
# - loading that graph into memory
def parse_rom(infile):
    
    print("Loading '{}' into R2...".format(infile))
    start = get_start(infile)

    try:
        r2 = r2pipe.open(infile, ["-2"])           # load infile into R2 - error if not found
    except IOError:
        print "R2 Couldn't open file {}\n".format(infile)
    if r2:                             # assert the R2 file opened correctly
        r2.cmd('e asm.arch=m7700')     # set the architecture env variable
        logging.debug("R2 Command used: 'e asm.arch=m7700'")
        logging.info("R2 loaded arch: " + r2.cmd('e asm.arch')) # check that arch loaded properly

        # first, attempt to generate a full graph from the reset vector
        rst = get_rst(r2) 
        logging.info ("Binary reset vector located at 0x{:04x}".format(rst))
        #logging.info ("Attempting to seek to reset vector...")

        if (rst < start): # some RST vectors are located below the test fcn
            start = rst

        r2.cmd("e anal.hasnext=true")
        r2.cmd("e anal.limits=true")
        r2.cmd("e anal.from=0x{:04x}".format(start))
        r2.cmd("e anal.to=0xffb5") # ffd0 onward are just vectors and should be reserved, not functions
        r2.cmd("e anal.split=false")
        r2.cmd("e anal.bb.split=false")

        logging.debug("e anal.hasnext: {}".format(r2.cmd("e anal.hasnext")))
        logging.debug("e anal.limits: {}".format(r2.cmd("e anal.limits")))
        logging.debug("e anal.from: {}".format(r2.cmd("e anal.from")))
        logging.debug("e anal.to: {}".format(r2.cmd("e anal.to")))
        logging.debug("e anal.split: {}".format(r2.cmd("e anal.split")))
        logging.debug("e anal.bb.split: {}".format(r2.cmd("e anal.bb.split")))

        #r2.cmd("e anal.bb.maxsize=0xffff")
        #r2.cmd("e anal.recont")

        #r2.cmd("s 0x{:04x}".format(rst))
        #r2.cmd("aaa")     # run a full analysis on the whole binary 
        #logging.debug("R2 Command used: 'aaa'")

    #    r2.cmd("s 0x{:04x}".format(rst))
    #    logging.debug("R2 Command used: 's 0x{:04x}'".format(rst))
        #logging.info ("R2 seeked to address {}".format(r2.cmd("s")))

        #r2.cmd("e anal.jmpabove=false")
        #r2.cmd("e anal.eobjmp=true")
        #r2.cmd("")

        # build func from a recursive function parse
        func_list = []
        func = None
        try:
            func = recursive_parse_func(rst, r2)
            func_list.append(func)

        except ValueError as valerr:
            print valerr
            print ("Recursive disassembly parse for ROM failed:")
       
        # then attempt to find additional functoins that were missed in the initial sweep with a recursive search
        try:
            func_list.extend(linear_parse_func(func, r2))
        except ValueError as valerr:
            print valerr
            print("Linear disassembly parse for ROM failed.")

        feature_dictionary = {}
        for funcs in func_list:
            feature_dictionary.update(grab_features(funcs, []))

        print "test"
     #   functions.append(func_list)
        global visited 
        visited = {} # clear the global visited struct
    else: 
        print("Error parsing R2")
    r2.quit()
    print("Quitting R2...")
    return feature_dictionary

# helper function to check if a string is a hex string or not
def isHex(num): 
    try:
        int (num, 16)
        return True
    except ValueError:
        return False

def main ():
    # set up the parser first
    # default parser args - filename, opens file for JSON parsing 
    # can also output JSON file as a .DOT file, or pull in a ROM and call R2 
    parser = argparse.ArgumentParser(description='Import and process M7700 JSON Graph files.')

    parser.add_argument('filename', metavar='filename', nargs='+', type=str, default=sys.stdin, 
                   help='M7700 ROM file for parsing')

    parser.add_argument('-o', '--output', action='store_true',
                   help='Output M7700 rom to file')

    logging.basicConfig(filename='log_filename.txt', level=logging.DEBUG)

    args = parser.parse_args()
    jsons = {}

    for infile in args.filename:
        if infile is not None:
            print("Opening file: {}".format(infile))

        feature_dict = parse_rom(infile)
        jsons[infile] = feature_dict # do ROM-level analysis with R2pipe


    with open('file.json', 'w') as out:
        json.dump(jsons, out, indent=4, sort_keys=True)

    out.close()

#        if (os.path.isfile(infile)):
#            if args.output: # only output if specified
#                with out as
#                out.write(json.dump(jsons))
#                out.close
#        else: 
#            print ("File '{}' not found".format(infile))

# start
main()