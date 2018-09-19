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
class function:
    parents ={}
    base_addr = 0x0 # address of the function
    json = ""      # json representation of function pointed to
    dot = ""       # dot representation of function pointed to
    children = {}
    graph = None # graphviz graph file

    def __init__(self, base_addr):
        self.base_addr = base_addr
        self.graph = nx.Graph()

    def __str__(self):
        ret = "Root: 0x{} ".format(self.base_addr)
        for addr, child in self.children.items():
            ret = ret + " {}".format(child)
        return ret

    def push_child(self, func):
        self.children[func.base_addr] = func

# -------- Output analyzed caller graphs to files
# - Files are in a hierarchy - top level is the "caller" function
# - next level down is the address of each "callee" jump
# - final level is the dot and json of the callee jump 
def output_graphs(callers, r2):

        # first, generate a supergraph of all nodes for each caller
        for func, func_caller in callers.items():
            logging.info ("Func: 0x{:04x} Caller: {}".format(func, func_caller))
            for addr, callee in func_caller.callees.items():
                logging.info ("Addr: 0x{:04x} Callee: {}".format(addr, callee))

        for func, func_caller in callers.items():
           
            func_str = '0x{:04x}'.format(func)
        
            logging.info("Seeking to address {} in radare.".format(func_str))
            r2.cmd("s {}".format(func_str))
            logging.debug("Current addr: {}".format(r2.cmd("s")))  # seek to the address of this func
            logging.info("Creating main caller JSON, Disassembly")
            r2.cmd('af-')# clean analysis data
            r2.cmd('aa')
            #r2.cmd('af')
            #r2.cmd('sp')
            func_caller.json = r2.cmd('agdj') # pull JSON disassembly from R2
            func_caller.dot = r2.cmd('agd')  # pull dot for function from R2
        
            func_caller.graph = nx_agraph.from_agraph(pygraphviz.AGraph(func_caller.dot)) # pull graph into networkx

            new_path = '{}-{}'.format(func_str, func_caller.count)

            if not os.path.exists(new_path):
                os.makedirs(new_path)
            if not os.curdir == new_path:
                os.chdir(new_path)

            proc_string = "gvpack -o {}/{}_master.dot {}/{}.dot".format(new_path, func_str, new_path, func_str)

            #logging.debug("Path object for CALLER: {}".format(new_path))
            f1 = open ("{}.json".format(func_str), "w")
            f2 = open("{}.dot".format(func_str), "w")
            f1.write(func_caller.json)
            f2.write(func_caller.dot)
            f1.close()
            f2.close()

            for addr, callee in func_caller.callees.items():

                try: 
                    addr_str = str('0x{:04x}'.format(callee.dest_addr))
                except ValueError:
                    addr_str = str('0x{}'.format(callee.dest_addr))

                r2.cmd("s {}".format(addr_str))
                logging.debug("Current addr: {}".format(r2.cmd("s")))  # seek to the address of this func

                r2.cmd('af-')# clean analysis data
                r2.cmd('aa')           
                #r2.cmd('af')
                #r2.cmd('sp') # seek to func identified here

                callee.json = r2.cmd('agdj')
                callee.dot = r2.cmd('agd') 

                sub_path = '{}'.format(addr_str)

                callee.graph = nx_agraph.from_agraph(pygraphviz.AGraph(callee.dot)) # pull graph into networkx

                if not os.path.exists(sub_path):
                    os.makedirs(sub_path)  

                os.chdir(sub_path)

                proc_string = proc_string + (" {}/{}/{}.dot".format(new_path, '0x{:04x}'.format(addr), sub_path))

                f3 = open ("{}.json".format(sub_path), "w")
                f4 = open("{}.dot".format(sub_path), "w")
                check_call(['dot','-Tpng', '-o', "{}.png".format(sub_path),"{}.dot".format(sub_path)])

                f3.write(callee.json)
                f4.write(callee.dot)
                #callee.graph = nx_agraph.read_dot(f4)
                #caller.master = nx.compose(func_caller.graph, callee.graph)

                f3.close()
                f4.close()
                os.chdir("..")

            #print proc_string
            #process = subprocess.Popen(proc_string.split(), stdout=subprocess.PIPE)
            #output, error = process.communicate()
            #logging.info(output)
            #logging.debug(error)
            os.chdir("..")

           # print func_caller.dot
            # print func_caller.graph.edges()
            # print func_caller.master.edges()

        cwd = os.getcwd()
        os.chdir(cwd)
        return callers    

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

# grab all child function calls from a function analysis in R2
def get_children(child_str):
    splitln_str = child_str.splitlines()
    #children = {}
#    for line in splitln_str:
    p = ur"JSR.*(0x[0-9a-fA-F]{4})"
    children = re.findall(p, child_str)

    for child in children:
        print("child: {}".format(child))
    return children

# recursively parses a binary, given address 
def recursive_parse_func(addr, r2):

    func = function(addr)
    r2.cmd("s {}".format(addr))     # seek to address
    r2.cmd("aa")                    # analyze at address
    #func.func_str = r2.cmd("pdf")        # print func disassembly
    child_str = r2.cmd("pdf")          # grab list of func params
    func.dot = r2.cmd("agd")              # grab dot of func from r2

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