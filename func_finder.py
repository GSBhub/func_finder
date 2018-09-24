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
from collections import OrderedDict
from networkx.drawing import nx_agraph
from subprocess import check_call
from datetime import datetime

# template for all function data types

class instruction:

    def __init__(self, base_addr, opcode):
        self.base_addr = base_addr
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
        self.base_addr = base_addr
        self.seq_inst = {}
        for op in seq_json:
            self.seq_inst[op[u'offset']] = instruction(op[u'offset'], op[u'opcode'])
 
    def get_seq_opcode(self): 
        return "WIP"    
    
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
        self.json = json[0]
        if u'offset' in json[0]:
            self.base_addr = json[0][u'offset']
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
                            try:
                                block_obj.fail = dict_block[block_json[u'fail'] + 1][0]
                            except KeyError:
                                try: 
                                    block_obj.fail = dict_block[block_json[u'fail'] - 1][0]
                                except KeyError:
                                    #dear god why
                                    try:
                                        block_obj.fail = dict_block[block_json[u'fail'] + 2][0]
                                    except KeyError:
                                        try:
                                            block_obj.fail = dict_block[block_json[u'fail'] - 2][0]
                                        except KeyError:
                                            print "idk nigga 1"

                    if u'jump' in block_json:
                        try:
                            block_obj.jump = dict_block[block_json[u'jump']][0]
                        except KeyError:
                            try:
                                block_obj.jump = dict_block[block_json[u'jump'] + 1][0]
                            except KeyError:
                                try:
                                    block_obj.jump = dict_block[block_json[u'jump'] - 1][0]
                                except KeyError:
                                    try:
                                        block_obj.jump = dict_block[block_json[u'jump'] - 2][0]
                                    except KeyError:
                                        try:
                                            block_obj.jump = dict_block[block_json[u'jump'] + 2][0]
                                        except KeyError:
                                            print "idk nigga 2"
                self.first = dict_block[blocks[000][u'offset']][0]
            else:
                raise KeyError()
        else: 
            raise KeyError()

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
        self.base_addr = base_addr
        self.children = {}
        self.parents = {}
        self.cfg = cfg

    def __str__(self):
        ret = "Root: {} ".format(self.base_addr)
        for addr, child in self.children.items():
            ret = ret + " {}".format(child)
        return ret

    def push_child(self, func):
        self.children[func.base_addr] = func


# locates the reset vector address from a valid M7700 binary
# using a currently open radare2 session
def get_rst(r2):
    r2.cmd("s 0xfffe")     # seek to the address for the reset vector (const for all of our binaries)
    big_endian = str(r2.cmd("px0")) # print last two bytes of rst vector
    
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
    splitln_str = child_str.splitlines()
    #children = {}
#    for line in splitln_str:
    p = ur"JSR.*(0x[0-9a-fA-F]{4})"
    children = re.findall(p, child_str)
    int_children = list()
    for child in children:
       print("child: {}".format(child))
       int_children.append(int(child, 16))
    return int_children

# helper function for recursive parse func
# popluates 
def populate_cfg(addr, func_json):
    #func_json = r'{}'.format(func_json)
    json_obj = json.loads('{}'.format(func_json.decode('utf-8', 'ignore').encode('utf-8')), strict=False)

    #first = block(json_obj['offset'], json_obj['blocks']['ops'])
    cfg = CFG(json_obj)
    print (
        '{}'.format(cfg))
#    for entry in json_obj:
#        for block in entry['blocks']:
#            print "Entry: {} \n".format(block)

    # parse the func json, populate the sequence instruction data types and blocks

    return cfg

# recursively parses a binary, given address 
def recursive_parse_func(addr, r2):

    r2.cmd("s {}".format(addr))     # seek to address
    r2.cmd("aa")                    # analyze at address
    cfg = populate_cfg(addr, r2.cmd("agj"))
    func = function(addr, cfg)
    #func.func_str = r2.cmd("pdf")        # print func disassembly
    child_str = r2.cmd("pdf")          # grab list of func params
    #func.dot = r2.cmd("agd")              # grab dot of func from r2

    children = get_children(child_str) # pull children from func list

    # ideally this eventually stops, though it likely won't
    for child_addr in children:
        child = recursive_parse_func(child_addr, r2)
        child.parents[addr] = func         # store reference to parent in child object
        func.push_child(child) # store the child in the base func object

    return func

# this method is responsible for
# - automatically parsing the rom file for functions
# - generating a graph from said functions
# - loading that graph into memory
def parse_rom(infile):
    
    print("Loading '{}' into R2...".format(infile))
    r2 = r2pipe.open(infile)           # load infile into R2 - error if not found
    if r2:                             # assert the R2 file opened correctly
        r2.cmd('e asm.arch=m7700')     # set the architecture env variable
        logging.info("R2 loaded arch: " + r2.cmd('e asm.arch')) # check that arch loaded properly

        # TODO: finish this
        rst = get_rst(r2) 
        logging.info ("Binary reset vector located at 0x{:04x}".format(rst))
        logging.info ("Attempting to seek to reset vector...")
        r2.cmd("s 0x{:04x}".format(rst))
        logging.info ("R2 seeked to address {}".format(r2.cmd("s")))
        func = recursive_parse_func(rst, r2)
        print func
    else: 
        print("Error parsing R2")
    r2.quit()
    print("Quitting R2...")
    return func

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

    for infile in args.filename:
        if infile is not None:
            print("Opening file: {}".format(infile))

        func = parse_rom(infile)

        # do ROM-level analysis with R2pipe
        if (os.path.isfile(infile)):
            if args.output: # only output if specified
                print ("WIP")
        else: 
            print ("File '{}' not found".format(infile))

# start
main()