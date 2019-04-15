#!/usr/bin/python
"""
Creates a JSON file containing a set of hashed features for each identified function in a valid M7700 BIN
"""

__all__ = ['function']
__version__ = '0.1.0'
__author__ = 'Greg'

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
import xlsxwriter
import xml.etree.ElementTree as ET
from collections import OrderedDict
from networkx.drawing import nx_agraph
from subprocess import check_call
from datetime import datetime
from itertools import cycle

# all function data types

class instruction:
    # smallest data type for function class, the individual instructions
    # field contains: base addr (where in memory this is)
    #               : opcode
    #               : all parameters used by instruction

    def __init__(self, _base_addr, opcode):
        self._base_addr = hex(_base_addr)
        _ = opcode.split()
        self._opcode = _[0]
        self._params = _[1:]

    def __str__(self):
        if self._params:
            ret = "OP: {}\nParams: {}\n".format(
                self._opcode, self._params)
        else:
            ret = "OP: {}\n".format(self._opcode)
        return ret

class block ():
    # a set of instructions that are isolated from other sub-instructions behind a _jump condition or a branch
    # field contains: base addr (where in memory these instructions begin)
    #               : _instruction_block - list of all instruction objects stored within a block
    #               : _fail - pointer to next block specified by "failed" _jump conditions
    #               : _jump - pointer to next block specified by
    #                       successful _jump conditions, or unconditional jumps
    #               : _parents - list containing all member blocks that call this block
    ######## Note: Jump and Fail pointers are set by the CFG class constructor

    _parents = None
    _fail    = None
    _jump    = None

    def __init__(self, _base_addr, seq_json):
        self._base_addr = hex(_base_addr)
        self._instruction_block = OrderedDict()
        self._parents = list()
        for entry in seq_json:
            self._instruction_block[entry[u'offset']] = instruction(
                entry[u'offset'], entry[u'opcode'])

    # implementation "sort of" equals method, threshold is minimum jaccard for equal
    def _compare(self, compare, threshold=.75):
        a = self._instruction_block.items()  
        b = compare._instruction_block.items()
        jaccard = len(list(set(a) & set(b))) / len(list(set(a) | set(b)))
        return True if jaccard > threshold else False        

    # simple helper function to return the nth item in the instruction dict
    # normally this dict is sorted by the address of the instruction, this
    # helper allows you to circumvent that
    def _get_instruction(self, index):
        iter = cycle(self._instruction_block.items())
        ret = None
        if index >= len(self._instruction_block):
            raise IndexError(index, "Index {} out of bounds.".format(index))
        for _ in range (-1, index):
           ret = next(iter) 
        if ret is None:
            raise IndexError(index, "Index {} out of bounds.".format(index))
        
        return ret[1]

    # Returns a hash of the instructions
    # takes entire instruction list for a block,
    # hashes it with the md5 hash algorithm,
    # and returns. Does nothing else.
    def _get_hashed_list(self):
        ret = ur""
        for _ in self._instruction_block.values():
            ret = ret + ur"{}".format(_._opcode)

        return [(md5.new(ret).hexdigest())]

    # Creates a list of all instructions for this block
    # tokenized into n-gram blocks. Returns that list.
    # Filter ignores the BRA instructions, leaving them out of gram creation.
    # Default program gram length: 2
    # If the grams provided exceed the length for a list, only items matching that length will
    # be added to the index. 
    def _n_gram(self, args):
        filter_list = args.ignore
        #get_consts = True
        n_grams = args.ngrams
        min_len = args.min_grams
        grams = list()
        ret = list()
        opcodes = []

        # generate a filtered list of opcodes given the provided filter
        for key in self._instruction_block.keys():
            if (filter_list is not None and self._instruction_block[key]._opcode in filter_list):
                continue # skip opcodes in the filter
            else:
                opcodes.append(self._instruction_block[key]._opcode)
                # if get_consts:
                #     for param in self._instruction_block[key]._params:
                #         if "#" in param:
                #             opcodes.append(param)

        # split list into N-gram opcodes if number of grams in list is sufficient         
        if n_grams > 0 and n_grams < len(opcodes):
            grams = zip(*[opcodes[i:] for i in range(n_grams)])
        # otherwise, check to see if list passes the minimum length requirement
        elif n_grams == 0 or min_len <= len(opcodes):
            grams = ["".join(opcodes)] # just sub the whole list

        if grams is not None:
            for pair in grams:
                ret.append("".join(pair))

        return ret

    # Returns a list of the edges of this block, tokenized into two-gram sections
    # first items are the edges for the parent caller blocks and the first instruction
    # last items are the final instructions of this block and its callees
    # Filter ignores the BRA instructions if specified, returning the previous instruction instead
    def _edge_list(self, args):

        filter_list = args.ignore
    
        ret = list()
        current_ops = self._instruction_block
        last_op = None
        for instr in reversed(current_ops.values()):
            
            if instr._opcode not in filter_list:
                last_op = instr # find last non-filtered instruction, seeking back
                break

        #parent_next_op = None

        # redundant with child search
        # for parent in self._parents:
        #     # pull opcode of parent
        #     parent_last_op = parent._get_instruction(len(parent._instruction_block) - 1)._opcode
        #     if (filter_list is not None and parent_last_op in filter_list):
        #         i = 1
        #         parent_next_op = None
        #         while parent_next_op is None and i < len(parent._instruction_block):
        #             # attempt to find a valid instruction that is not in the filter list
        #             if  parent._get_instruction(len(parent._instruction_block) - i)._opcode not in filter_list:
        #                 parent_next_op = parent._get_instruction(len(parent._instruction_block) - i)._opcode
        #             i += 1


            # if parent_next_op is not None and current is not None: # don't add new item if none found
            #     ret.append(ur"{}{}".format(parent_last_op, 
            #         current._opcode
            #     ))

        # add in child edges
        if self._jump is not None:
            # point to next block
            next_block = self._jump
            instructions = next_block._instruction_block
            child_last_op = None
            for instr in reversed(instructions.values()):
                if instr._opcode not in filter_list:
                    child_last_op = instr # find last non-filtered instruction, seeking back
                    break

            if last_op is not None and child_last_op is not None:
                ret.append(ur"{}{}".format(last_op._opcode, child_last_op._opcode))
            
        if self._fail is not None:

            next_block = self._fail
            instructions = next_block._instruction_block
            child_last_op = None
            for instr in reversed(instructions.values()):
                if instr._opcode not in filter_list:
                    child_last_op = instr # find last non-filtered instruction, seeking back
                    break

            if last_op is not None and child_last_op is not None:
                ret.append(ur"{}{}".format(last_op._opcode, child_last_op._opcode))
            
        return ret

    # Main feature generation algorithm, parses args passed at run-time 
    # and generates a complete feature vector using those params
    # Full list of args can be located down by the main method
    def _get_features(self, args):
        ret = []
        if args.hashed_list:
            return self._get_hashed_list()

        ret.extend(self._n_gram(args)) # placeholder values for now

        if args.edges:
            ret.extend(self._edge_list(args))

        return ret

    def _print_inst(self):
        for instruction in self._instruction_block.itervalues():
            print(instruction)

    def __str__(self):
        ret = "Base_addr: 0x{:04x}\n".format(self._base_addr)
        if self._fail:
            ret += "\tFail: 0x{:04x}\n".format(self._fail._base_addr)
        if self._jump:
            ret += "\tJump: 0x{:04x}\n".format(self._jump._base_addr)
        return ret

class CFG:
    # a tree of blocks that compose a complete function
    # field contains: base addr (where in memory these blocks begin)
    #               : first - pointer to the first block in memory
    #               : json - json representation of the CFG
    # constructor is responsible for populating the block data-types given a JSON representation from R2
    _netx_cfg = None
    _first = None

    def __init__(self, json):
        self._netx_cfg = nx.DiGraph()
        if json:
            self._json = json[0]
        else:
            self._json = ""
        if u'offset' in self._json: 

            # JSON objects from R2 use offset as their base address, seek here and begin parsing
            self._base_addr = hex(self._json[u'offset'])
            if u'blocks' in self._json:
                # Populate block objects using the 'blocks' field in R2's JSON
                blocks = self._json[u'blocks']
                dict_block = {}
                
                # pass addr of first block, ops of first block, and pointers of first block
                #self._first = block(blocks[000][u'offset'], blocks[000][u'ops'])

                # create a dictionary of all blocks using this information
                for blk in blocks:
                    if len(blk['ops']) == 0:
                        continue
                    else:
                        dict_block[blk[u'offset']] = [block(
                            blk[u'offset'],
                            blk[u'ops']), blk]
                i = 0
                for _, pair in dict_block.items():
                    # init nodes
                    self._netx_cfg.add_node(pair[0], 
                        base_addr=pair[0]._base_addr, 
                        instruction_block = pair[0]._instruction_block,
                        parents = pair[0]._parents,
                        jump = pair[0]._jump,
                        fail = pair[0]._fail,
                        node_num = i
                    )
                    pair[0].node_num = i
                    i+=1

                # match up all the block objects to their corresponding _jump, _fail addresses
                for _, pair in dict_block.items():
                    block_obj = pair[0]
                    block_json = pair[1]
                    #_netx_cfg[_][block] = block_obj

                    if u'fail' in block_json:
                        try:
                            block_obj._fail = dict_block[block_json[u'fail']][0]
                            block_obj._fail._parents.append(block_obj)
                            #_netx_cfg.add_node(block_obj._fail)
                            self._netx_cfg.add_edge(block_obj, block_obj._fail)
                            self._netx_cfg[block_obj][block_obj._fail]["color"] = "red"
                           
                        except KeyError:
                            # KeyErrors result if no valid jumps exist, can be safely ignored
                            continue

                    if u'jump' in block_json:
                        try:
                            block_obj._jump = dict_block[block_json[u'jump']][0]
                            block_obj._jump._parents.append(block_obj)
                            #_netx_cfg.add_node(block_obj._jump)
                            self._netx_cfg.add_edge(block_obj, block_obj._jump)
                            if block_obj._fail is not None:
                                self._netx_cfg[block_obj][block_obj._jump]["color"] = "green"
                            else: 
                                self._netx_cfg[block_obj][block_obj._jump]["color"] = "blue"

                        except KeyError:
                            # KeyErrors result if no valid jumps exist, can be safely ignored
                            continue
                # save first block, keeping entire tree in mem
                self._first = dict_block[int(self._base_addr, 16)][0] 

    def __str__(self):
        ret = ""
        node = self._first
        while node is not None:
            ret += "{}\n".format(node)
            if node._fail:
                node = node._fail
            else:
                node = node._jump
        return ret

    # Bottleneck feature searching
    # attempts to find "bottlenecks" - single conditional jumps with multiple parents
    # default depth - 2
    def _bottlenecks(self, args, visited, depth=2):
        # Very WIP

        ret = dict() # feature list, containing grams back

        # first - identify all bottlenecks within a function, store in list
        bottlenecks = self._get_bottlenecks(self._first, visited)
        # then  - get features from bottlenecks of depth N back
        for bottleneck in bottlenecks:
            #bn = self._netx_cfg.subgraph(self._netx_cfg.neighbors(bottleneck))

            ret[bottleneck._base_addr] = (
                self._bottleneck_seek_back(
                    bottleneck, depth, args, visited)
                )

        return ret

    # recursively traverses function CFG and gathers a list of all bottlenecks
    def _get_bottlenecks(self, current, visited):

        ret = list()
        if current is None or current in visited:  
            # Ignore blocks we've already resited, base condition
            return ret  # if block has 4 or more _parents, define as a bottleneck

        if (len(current._parents) >= 4):
            ret.append(current)

        visited.append(current)

        if current._fail is not None:
            ret.extend(self._get_bottlenecks(current._fail, visited))

        if current._jump is not None:
            ret.extend(self._get_bottlenecks(current._jump, visited))

        return ret

    # recursively seeks back N blocks from bottleneck
    # returns a list of all N-gram features including this block and any prior
    def _bottleneck_seek_back(self, bottleneck, depth, args, visited):

        ret = list()
        current = bottleneck

        ret.extend(current._get_features(args))

        if depth == 0 or bottleneck is None:  # base condition - JUST return bottleneck
            return ret

        # visited.append(bottleneck)
        # current = bottleneck

        # add block's current features to ret

        # add in edge instruction for each parent
        for parent in current._parents:

            # parent_op = parent._get_instruction(len(parent._instruction_block) - 1)._opcode

            subgraph = self._bottleneck_seek_back(parent, depth - 1, args, visited)
            if subgraph:
                ret.extend(subgraph)

        return ret

class function:
    # overall function datatype, containing the CFG
    # field contains: base addr (where in memory these instructions begin)
    #               : json - json rep of data structure from R2
    #               : dot - dot rep of data structure from R2
    #               : children - functions called by this function
    #               : _parents  - functions that call this function

    _unique_id = -1 # dummied out for now, trying to figure out a unique way to label matching functions
    _base_addr = 0x0  # address of the function
    _json = ""      # json representation of function pointed to
    _dot = ""       # dot representation of function pointed to
    
    def __init__(self, _base_addr, cfg):
        self._base_addr = hex(_base_addr)
        self._children = {}
        self._parents = {}
        self._cfg = cfg

    def __str__(self):
        ret = "0x{:04x}\n".format(self._base_addr)
        for child in self._children.values():
            ret += "\t{}".format(child)
        return ret

    # adds a child to list of functions that this function calls
    def _push_child(self, func):
        self._children[func._base_addr] = func

    # Master-function to grab features from block sub-classes
    # Returns a complete list of features for this entire function
    def _get_features(self, args):
        ret = []
        if self._cfg._first is None:
            return

        ret = (self._get_features_helper(self._cfg._first, [], args))

        if args.bottlenecks:
            bn = self._cfg._bottlenecks(args, [], args.depth)
            if bn is not {} and len(bn) is not 0:
                ret.append(bn)
        return ret

    # recursive helper for _get_features
    def _get_features_helper(self, block, __visited, args):
        ret = []
        if block is None or block in __visited:  
            # Ignore blocks we've already resited, base condition
            return ret
        # get feature list from block
        ret.extend(block._get_features(args))
        __visited.append(block)

        # grab features from block's children
        if block._jump is not None:
            ret.extend(self._get_features_helper(block._jump, __visited, args))
        if block._fail is not None:
            ret.extend(self._get_features_helper(block._fail, __visited, args))
        return ret

# Container class, contains information on the ROM including
#   - RST Vector Address
#   - Instruction Loop Length
#   - Other vectors
#  These features will be used to identify which engine each binary belongs to
class ROM():

    def __init__(self, filename, functions, RST, START):
        self.filename = filename
        # self.jsons = jsons
        # self.r2 = r2 - jsons, r2,  removed args
        self.functions = functions
        self.RST = RST # RST vector address
        self.START = START # length of main internal loop
        self.max_jsons = OrderedDict() # max JSON values from JSONParser 
        self.engine = "???"

    # returns similarity percentage of two ROMs based on internal features of this data structure
    # 
    # Metrics: RST Vector address - Code Start address - Max JSON Jaccard Values
    # 
    # Returns a value from 0 - 1 
    def _compare(self, rom_cmp):

        comparison_index = 0.0
        return "WIP"

    # specific comparison function similar to above 
    # designed to match how alike a functin is with the specific control
    def _control_comparison(self, control):

        comparison_index = 0.0
        jaccard_comparison = 0.0
        jacc_vals = 0

        for label, maxes in self.max_jsons.iteritems():
            if control.filename in label: # locate the control-self jaccard values
                for _, comp_val in maxes.iteritems():
                    #for _, json in comp_val.iteritems():
                    jaccard_comparison += comp_val[1] # add jaccard value from each json structure
                    jacc_vals += 1
        try:
            jaccard_comparison = jaccard_comparison / jacc_vals
        except ZeroDivisionError:
            jaccard_comparison = 0

        # if control.RST == self.RST:
        #     comparison_index += 1
        # if control.START == self.START:
        #     comparison_index += 1          

        comparison_index += jaccard_comparison

        return comparison_index 

# locates the reset vector address from a valid M7700 binary
# using a currently open radare2 session
# used to find initial location for mem searches
def _get_rst(r2):
    # seek to the address for the reset vector (const for all of our binaries)

    r2.cmd("s 0xfffe")
    logging.debug("R2 Command used: 's 0xfffe'")

    rst_addr = str(r2.cmd("px0"))  # print last two bytes of rst vector
    logging.debug("R2 Command used: 'px0'")

    rst = 0x0

    if rst_addr:
        # flip endianness of last two bytes (start off little, need to be big)
        rst = int("{}{}".format(rst_addr[2:4], rst_addr[:2]), 16)
        logging.debug("rst vector address found at: 0x{:04x}".format(rst))
    else:
        logging.debug("ERR - reset vector search failed")

    return rst

# Helper function for recursive_parse_func
# grabs all child function calls from a function analysis in R2
# our arch only uses JSR for function calls, so this works for now
def _get_children(child_str):
    # this regex searches for any functions starting with JSR
    p = ur"JSR.*[^$](0x[0-9a-fA-F]{4})"  
    children = re.findall(p, child_str)
    p1 = ur"JSR.*fcn.0000([0-9a-fA-F]{4})"
    ch2 = re.findall(p1, child_str)
    children.extend(ch2)  

    int_children = list()
    for child in children:
        try:
            int_children.append(int(child, 16))
        except TypeError:
            print (child)
    del children
    return int_children

# helper function for recursive parse func
# popluates CFG data structure for each function, given a valid func_json
def _populate_cfg(addr, func_json):
    # nice solution found at https://grimhacker.com/2016/04/24/loading-dirty-json-with-python/
    # helps handle "dirty" JSON input
    regex_replace = [(r"([ \{,:\[])(u)?'([^']+)'", r'\1"\3"'), (r" False([, \}\]])", r' false\1'), (r" True([, \}\]])", r' true\1')]
    for r, s in regex_replace:
        func_json = re.sub(r, s, func_json)

    json_obj = json.loads(unicode(func_json, errors='ignore'),
                          strict=False, object_pairs_hook=collections.OrderedDict)
    cfg = CFG(json_obj)
    return cfg

# recursively parses a binary, given address
# function parsing is as follows in terms of radare2 instructions
#   - 0x{addr} -  seek to address
#   - aa       -  analyze function to end of basic block (analyze all) - more consistent than running aaa at start of binary
#   - sf.      -  seek to beginning of any already-identified functions (limits repeats)
#   - pdf      - print disassembly of function (For parsing to get children)
#   - agj      - print analyzed json data structure
#  for each child found in pdf (a child defined as a JSR to another unique function address), this method recurses
#  found children addresses are added to a "_visited" global data structure, and are not recursed if _visited multiple times
#       instead, _visited children just have their list of _parents updated whenever something else finds them
def _recursive_parse_func(addr, visited, r2):
    #r2.cmd("a2f")

    r2.cmd("0x{:04x}".format(addr))     # seek to address
    logging.debug("R2 Command used: '0x{:04x}'".format(addr))

    r2.cmd("sf.")

    #r2.cmd("af-")
    #r2.cmd("aa")

    addr = int(r2.cmd("s"), 16)

    child_str = r2.cmd("pdf")          # grab list of func params
    logging.debug("R2 Command used: 'pdf'")
    
    children = _get_children(child_str)  # pull list of children from func list

    if addr in visited.keys():
        # attempt to see if we've traversed down that function branch before (ie, defined it and its children)
        func = visited[addr]
        return func
    else:
        # iterate over all of this function's children, and recursively travel down each branch
        cfg = _populate_cfg(addr, r2.cmd("agj")) # create a CFG for each function from R2's JSON
        logging.debug("R2 Command used: 'agj'")
        func = function(addr, cfg)
        visited[addr] = func


    for child_addr in children:
        if child_addr in visited.keys():  # we don't need to recursively parse a function's children if it's already parsed
            visited[child_addr]._parents[addr] = func  # store reference to parent in child object
            func._push_child(visited[child_addr]) # store the child in the base func object
        else:
            visited[child_addr] = _recursive_parse_func(child_addr, visited, r2) # store reference to parent in child object
            visited[child_addr]._parents[addr] = func # store the child in the base func object
            func._push_child(visited[child_addr])
    return func

def _parse_call_str(func_str):
    ret = []
    fs = func_str.splitlines()
    children = set()
    
    for ln in fs:
        p = ur".*JSR.*[^$](0x[0-9a-fA-F]{4})"  
        children.update(re.findall(p, ln))
        p1 = ur".*JSR.*fcn.0000([0-9a-fA-F]{4})"
        ch2 = re.findall(p1, ln)
        children.update(ch2)  

    for child in children:
        
        try:
            if (int(child, 16) > 0x8000):
                ret.append(int(child, 16))
        except TypeError:
            print (child)

    del children

    # for line in fs:
    #     try:
    #         addr = int(line[:10], 16) # first 10 spots in line are the hex address
    #     except TypeError:
    #         continue
    #     if addr and addr >= 36864: # sanity check to make sure we're not including addresses from MMIO/RAM
    #         ret.append(addr)
    return ret


# simple helper function to split a function string into a list and return any found addresses in that list
def _func_parse_str(func_str):
    ret = []
    fs = func_str.splitlines()
    for line in fs:
        try:
            addr = int(line[:10], 16) # first 10 spots in line are the hex address
        except TypeError:
            continue
        if addr and addr >= 36864: # sanity check to make sure we're not including addresses from MMIO/RAM
            ret.append(addr)
    return ret

# secondary function search method - attempts to identify all functions within radare, 
# then passes each to the recursive parse
# not strictly "linear" because it uses our recursive method, 
# but it does attempt to brute-force non found functions instead of just recursing from the reset vector
# catches a few extra functions that a normal recurse from the RST vector does not
def _linear_parse_func(func, visited, r2):
    func_list = []
    r2.cmd("aac")
    
    # use /A call instead of afl
    # func_str = r2.cmd('afl')  # pull a complete list of functions
    # logging.debug("R2 Command used: 'afl'")
    func_str = r2.cmd("/A call")

    assert(func_str is not None)

    l = _parse_call_str(func_str)

    for addr in l:
        #if addr not in visited.keys():
            # attempt to manually parse each address with recursion
        func_list.append(_recursive_parse_func(addr, visited, r2))

    return func_list


# Creates an array of hashed features representing the instruction grams of each block within a function
def _grab_features(func, visited, args):

    func_dict = {}
    if func in visited:
        return func_dict

    sig = func._get_features(args)
    func_dict[ur"{}".format(func._base_addr)] = ur"{}".format(sig)
    visited.append(func)

    for child in func._children.values():
        func_dict.update(_grab_features(child, visited, args))

    return func_dict

# helper to attempt to locate the start of our M7700 binaries
# very sloppy, but our start methods across each binary 
# all start with the same instruction
def _get_start(infile):
    addr = 0x0000

  #  try:
    # load infile into R2 - error if not found
    r2 = r2pipe.open(infile, ["-2"])
    r2.cmd("e asm.arch=m7700")
    addr = 0
    val = r2.cmd("/c CMP al #0xf0")  # attempt to find the initial address
    if val is "":
        # attempt to find the initial address (if the flags aren't set properly yet)
        val = r2.cmd("/c CMP ax #0xf0f0")
    vals = val.split()

    try:
        r2.cmd("s {}".format(vals[0]))
    except IndexError:
        None
    addr = int(r2.cmd("s"), 16)
    r2.quit()
    
#    except IOError:
   # print ("Could not locate start of binary")

    return addr

# this method is responsible for
# - automatically parsing the rom file for functions
# - generating a graph from said functions
# - loading that graph into memory
def _parse_rom(infile, args):

    visited = {}
    
    print("Loading '{}' into R2...".format(infile))
    start = _get_start(infile)
    
    try:
        # load infile into R2 - error if not found
        r2 = r2pipe.open(infile, ["-2"]) # note - -2 flag surpresses R2 warning/logging information
    except IOError:
        print ("R2 Couldn't open file {}\n").format(infile)
    if r2:                             # assert the R2 file opened correctly
        r2.cmd('e asm.arch=m7700')     # set the architecture env variable
        logging.debug("R2 Command used: 'e asm.arch=m7700'")

        # check that arch loaded properly
        logging.info("R2 loaded arch: " + r2.cmd('e asm.arch'))

        # first, attempt to generate a full graph from the reset vector
        rst = _get_rst(r2)
        logging.info("Binary reset vector located at 0x{:04x}".format(rst))

        if (rst < start):  # some RST vectors are located below the test fcn
            start = rst

        r2.cmd("S 0x0000 0x0000 {:04x} data rw".format(start - 0x1))
        r2.cmd("S {:04x} {:04x} {:04x} ROM rwx".format(start, start, 0xffd0-start)) # define code sector

        r2.cmd("e anal.limits=true")
        r2.cmd("e anal.from=0x{:04x}".format(start)) 
        # start algorithm doesn't work too well, there are a few funcs that have some extra routines before the 0x9000 ROM code
 
        # ffd0 onward are just vectors and should be reserved, not functions
        r2.cmd("e anal.to=0xffd0")
        #logging.debug("e anal.hasnext: {}".format(r2.cmd("e anal.hasnext")))
        logging.debug("e anal.from: {}".format(r2.cmd("e anal.from")))
        logging.debug("e anal.to: {}".format(r2.cmd("e anal.to")))

        r2.cmd("0x{:04x}".format(rst))
        r2.cmd("aaa")

        # build func from a recursive function parse
        func_list = []
        func = None
        try:
            # visited struct is passed by reference, and should be populated in both cases
            func = _recursive_parse_func(rst, visited, r2)
            func_list.append(func)

        except ValueError as valerr:
            print (valerr)
            print ("Recursive disassembly parse for ROM failed:")

        # then attempt to find additional functoins that were missed in the initial sweep with a recursive search
        try:
            func_list.extend(_linear_parse_func(func, visited, r2))
        except ValueError as valerr:
            print (valerr)
            print("Linear disassembly parse for ROM failed.")

        feature_dictionary = {}

        for funcs in func_list:
            # pass the functions, an empty list (visited), and our option flags to the feature parser
            feature_dictionary.update(_grab_features(funcs, [], args))
        # functions.append(func_list)
        split = _json_parser_format(infile)
        
        # store features in ROM
        rom = ROM(split, func_list, rst, start)

    else:
        print("Error parsing R2")
    r2.quit()
    print("Quitting R2...")

    return func_list, feature_dictionary, rom

# helper function to check if a string is a hex string or not
def _isHex(num):
    try:
        int(num, 16)
        return True
    except ValueError:
        return False

# implementation "sort of" equals method, threshold is minimum jaccard for equal
# params 2 nodes
def _compare(node1, node2, threshold=.75):

    a = node1['instruction_block'].items()  
    b = node2['instruction_block'].items()

    jaccard = len(list(set(a) & set(b))) / len(list(set(a) | set(b)))

    return True if jaccard > threshold else False        

def _pull_ctrl_funcs(ctrl_func):
    sensors = {
        'batt_voltage': ['0x9a56', '0x9f5b', '0xa166', '0xa307', '0xae2c', '0xd982', '0xe1cd'],
        'vehicle_speed': ['0x9be8', '0x9dce', '0xa59d', '0xa9a7', '0xafc6', '0xb960'],
        'engine_speed': ['0xa59d', '0xa5ec', '0xa9a7', '0xafc6', '0xb5bf', '0xb960'],
        'water_temp': ['0x9b46', '0xab56'],
        'ignition_timing': ['0xdb1a', '0xda0f'],
        'airflow': ['0xddcd'],
        'throttle_position': ['0xe1cd'],
        'knock_correction': ['0xafc6']
    }
    ret = {}
    for func in ctrl_func:
        for sensor, funcs in sensors.iteritems():
            if func._base_addr in funcs:
                ret[sensor] = func
    return ret

# helper method to quickly convert our file names into a more consise format
# this format is used in JSONParser as the names for the excel spreadsheets
def _json_parser_format(infile):
    split = infile.split('/')
    split = split[len(split) - 1]
    split = split.split('-')
    split = split[0][4:] + '-' + split[1][2:] + '-' + split[4].split('.')[0]
    return split

# Quick method to translate the sensor type from each string into the proper index labels
def _instruction_translation(sensor_label):
    ret = ""
    if "Battery Voltage" in sensor_label:ret = "batt_voltage"
    elif "Vehicle Speed" in sensor_label: ret= "vehicle_speed"
    elif "Engine Speed" in sensor_label: ret = "engine_speed"
    elif "Water Temp." in sensor_label: ret = "water_temp" 
    elif "Igition Timing" in sensor_label: ret = "ignition_timing"
        # Note: this is misspelled in the actual datasheet, 
        # so this is  the "correct" way to access it
    elif "Airflow Sensor" in sensor_label: ret = "airflow"
    elif "Throttle Position Sensor" in sensor_label: ret = "throttle_position"
    elif "Knock Correction" in sensor_label: ret = "knock_correction" 
    return ret

def _json_outfile_formatter(json, listing):
    temp = {
            "batt_voltage":[],
            "vehicle_speed":[],
            "engine_speed":[],
            "water_temp":[],
            "ignition_timing":[],
            "airflow":[],
            "throttle_position":[],
            "knock_correction":[]
    }
    for func_type, pair in json[listing].iteritems():
        a = func_type[func_type.find("(")+1:func_type.find(")")]
        sensor = _instruction_translation(a)
        temp[sensor].append(pair[0])# pull all sensor type from row (value in parenthesis)

    for sensor, li in temp.iteritems():
        li = li.sort()

    return temp

def _prep_json_outfile(bins, ctrl_roms):
    max_candidate_bins = OrderedDict()
    #print "AAAA"
    for engine, engine_bin in bins.iteritems():
        max_candidate_bins[engine] = OrderedDict()

        # first - define entry for the control for each engine
        control_bin = ctrl_roms[engine]

        max_candidate_bins[engine]['Control'] = _json_outfile_formatter(control_bin.max_jsons, "{} {}".format(control_bin.filename, control_bin.filename))
   
        for rom in bins[engine]:
            
            if rom.filename not in ctrl_roms:

                # next - populate every entry that is not the control
                max_candidate_bins[engine][rom.filename] = _json_outfile_formatter(rom.max_jsons, "{} {}".format(control_bin.filename, rom.filename))
 
    return max_candidate_bins

def _json_parser_processing(json_in, outfile, rom_list, ctrl_roms):

    ctrl_list = []

    for ctrl_name, _ in json_in.iteritems():
        ctrl_list.append(_json_parser_format(ctrl_name))

    #subp_args = ['-c', ctrl_list, '-j' , outfile, os.path.splitext(outfile)[0] + '.xlsx']
    #execfile('JsonParser.py {}'.format(sys.argv))
    ctrl_str = ""
    for cs in ctrl_list:
        ctrl_str = "{} {}".format(ctrl_str, cs)

    print "Starting JSONParser..."
    #-c {} ctrl_str, 

    p = subprocess.Popen(['python ./JsonParser.py {} {} -j'.format(
            outfile, os.path.splitext(outfile)[0] + '.xlsx')
            ], stdout=subprocess.PIPE, shell=True)
    output,err = p.communicate()
    
    print (output)  

    # Load in max JSON values, average Jaccards, use to sort into bins
    with open('parser_maxes.json', 'r') as json_tmp_val:
        max_jsons = json.load(json_tmp_val)
    
    # first - find all max values from JSONparser
    for fn, rom in rom_list.iteritems():
        for file_comp, maxes in max_jsons.iteritems():
            rom.max_jsons[file_comp] = OrderedDict()
            if fn in file_comp: # and fn not in ctrl_list:
                # if this ROM is not a control AND this set of maxes belongs to this ROM
                rom.max_jsons[file_comp] = maxes

    bins = OrderedDict()
    for engine, _ in ctrl_roms.iteritems():
        bins[engine] = []

    # then  - use all features in the max to determine which bin to put each ROM
    max_index = 0.0
    for fn,rom in rom_list.iteritems():
        engine_candidate = None

        for engine, ctrl in ctrl_roms.iteritems():
            if engine_candidate is None:
                engine_candidate = engine

            index = rom._control_comparison(ctrl)

            if index > max_index: 
                # find most likely engine match given our control values
                max_index = index
                engine_candidate = engine

        rom.engine = engine_candidate
        
        bins[rom.engine].append(rom) # partition off that engine candidate to their engine bin for comparison
        max_index = 0.0

    max_candidate_bins = _prep_json_outfile(bins, ctrl_roms)

    return max_candidate_bins


# Program Flag options
# Default options - func_finder.py filename ...
# Filename can be multiple options, each subsequent filename loads in an additional ROM
# additional options:
#   -o: outfile  - specify the name for the output JSON file
#   -n: grams    - specify the number of grams to break the software for an ECU into
#   -i: ignore   - ignore certain instructions
#   -e: edges    - add in edge processing to graph
#   -b: bot.necks- attempt bottleneck subgraph processing instead of full graph processing
#   -d: depth    - set the depth variable of the bottleneck to specify how far back to go
def main():
    # set up the parser first
    # default parser args - filename, opens file for JSON parsing
    # can also output JSON file as a .DOT file, or pull in a ROM and call R2
    parser = argparse.ArgumentParser(
        description='Import and process M7700 JSON Graph files.')
    # rough option to run full list by default on all files in our bin directory - just for testing
    parser.add_argument('filename', metavar='filename', nargs='?', type=str, default=("/home/greg/Documents/git/func_finder/bins/*.bin"),
                        help='M7700 ROM file for parsing')

    parser.add_argument('-o', '--outfile', metavar='outfile', default="file.json", type=str,
                        help='Specify Filename')
 
    parser.add_argument('-x', '--xml', metavar='xml', default="parser_settings.json", type=str,
                        help='Specify XML/JSON Settings Filename')

    parser.add_argument('-n', '--ngrams', metavar='ngrams', default=2, type=int,
                   help='Specify number of grams to break feature vectors into')

    parser.add_argument('-i', '--ignore', metavar='ignore', nargs='+', type=str, default=[],
                   help='Define filter instructions (needs at least one)')
    
    parser.add_argument('-m', '--min-grams', metavar='min_grams', type=int, default=1,
                        help='Specify minimum length of grams to include in output')

    parser.add_argument('-j', '--parse-json', dest='parse_json', action='store_true',
                        help='Call Parse_Json script after feature generation.')

    parser.add_argument('-e', '--edges',      dest='edges', action='store_true',
                   help='Process edges')

    parser.add_argument('-z', '--hashed_list',dest='hashed_list', action='store_true',
                   help='Legacy Hashed List Generator')

    parser.add_argument('-b', '--bottlenecks', dest='bottlenecks', action='store_true',
                   help='Search for and process bottleneck subgraphs')

    parser.add_argument('-d', '--depth', metavar='depth', default=1, type=int,
                   help='Change bottleneck subgraph depth')

    logging.basicConfig(filename='log_filename.txt', level=logging.DEBUG)

    args = parser.parse_args()
    if args.filename == "/home/greg/Documents/git/func_finder/bins/*.bin":
        import glob
        args.filename = glob.glob("/home/greg/Documents/git/func_finder/bins/*.bin")
    outfile = args.outfile
    jsons = OrderedDict()
    function_collections = OrderedDict()
    #tree = ET.parse(args.xml)
    #root = tree.getroot()
    with open(args.xml, 'r') as fin:
        json_settings = json.load(fin)#root.findall('control') TODO: change var names to json
    ctrl_roms = OrderedDict() # bins to point to for the control funcs
    rom_list = OrderedDict()

    for infile in args.filename:
        #if infile is not None:
        
        print("Opening file: {}".format(infile))

        function_collections[infile], jsons[infile], rom = _parse_rom(infile, args)
        rom_list[rom.filename] = rom

        for ctrl_name, ctrl_vals in json_settings.iteritems():
            if (ctrl_name in infile): # pull list of control functions
                rom_nm = _json_parser_format(infile)
                ctrl_roms[ctrl_vals['engine']] = rom_list[rom_nm]

    #TODO:
    # use feature vector generation from the ctrl roms to
    # 1. ID which bins belong to that family based off those features
    # 2. Separate those bins off
    # 3. Separate the JSON files based off of those bins
    # 4. Output and label accordingly

    # IDEAS:
    # Features contained in the XML are basically all I need to ID
    #
    # Pull based on reset vector

    with open(outfile, 'w') as out:
        json.dump(jsons, out, indent=4, sort_keys=True)

        out.close()
    
    if args.parse_json: # TODO: add some way to name the json output, I guess
        max_candidate_bins = _json_parser_processing(json_settings, outfile, rom_list, ctrl_roms)

        with open("fcg_maxes.json", 'w') as outfile:
            json.dump(max_candidate_bins, outfile, indent=4, sort_keys=True)
            outfile.close()
        print "Wrote addresses of max sensor candidates for each engine to file fcg_maxes.json."
 
    # # Create JSON outfile for Pysensor, titled with ROM comparison
    # # structure is
    # # ENGINE1 - {
    # # 
    # #   CONTROL {
    # #       CONTROL SENSOR VALUES/ADDRESSES/MAXES
    # #   } 
    # # 
    # #   CANDIDATE_1...N {
    # #       CANDIDATE SENSOR ADDRESSES/MAXES
    # #   }
    # # }

print("Starting...")
# start
if __name__ == '__main__':
    main()