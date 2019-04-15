#!/usr/bin/python

import sys
import json
import xlsxwriter
import r2pipe
import ast
import xlrd
import argparse
import xml.etree.ElementTree as ET
from func_finder import _get_start, _get_rst
from collections import OrderedDict

__all__ = ['EcuFile', 'Cell', 'IndexTable']
__version__ = '0.1.0'

# Predefined functions containing sensor addresses for comparision's
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
# How far left & right to show address range
hex_margin = 250

class EcuFile:
    def __init__(self, file_name, functions, gt=None):
        """
        EcuFile constructor
        :param file_name: File name of ECU binary
        :param functions: JSON of function address & block hashes
        """
        self.functions = OrderedDict()

        self.name = _json_parser_format(file_name)
        split = file_name.split('/')
        self.file_name = split[len(split) - 1]
        
        local_gt = dict(gt) # clone GT, we're fixing some of the errors in the man address

        r2 = r2pipe.open('./bins/' + self.file_name, ["-2"])
      
        start = _get_start(file_name) # using private functions here, but oh well

        rst = _get_rst(r2)

        r2.cmd('e asm.arch=m7700')
        r2.cmd('e anal.limits=true')
        r2.cmd('e anal.from={}'.format(start if rst > start else rst))
        r2.cmd('e anal.to=0xffd0') # rough estimate of last code
        r2.cmd('s {}'.format(rst))
        r2.cmd('aaa') # analyze all

        functions.items()

        for address, hashes in functions.items():

            if hashes != [''] and int(address, 16) >= 36864:
                # convert hash to dict
                tmp_dict = ast.literal_eval((hashes))
                if  tmp_dict is not None and len(tmp_dict) is not 0 : 
                    # purge empty entries from list
                    self.functions[address] = tmp_dict
          
        if self.name in local_gt.keys():
            for sensor_type, l in dict(local_gt[self.name]).iteritems():
                for addr in list(l):
                    r2.cmd("s {}".format(addr)) # seek to addr from XLSX
                    r2.cmd("sf.")               # seek to beginning of function
                    gt[self.name][sensor_type][ # change addrs from file to point to start of function
                        gt[self.name][sensor_type].index(addr)] = ur"{}".format(r2.cmd("s")).strip()
                    # print ("{}".format(sensor_type))
                    # print ("{}".format(addr))
                    # print r2.cmd("s")
        r2.quit()
        print('Created ECU file ' + self.file_name)

class Cell:
    
    def __init__(self, func_addr, jaccard, flags=None):
        self.func_addr = func_addr
        self.jaccard = jaccard
        if flags is not None:
            self.flags = flags
        else:
            self.flags = { # more can be added in the future
        'Guess_Candidate' : False, # is a guess candidate (mark yellow)
        'Max_Row': False,          # is highest jaccard value
        'Control_Value': False     # matches control address  
        }
        self.row = None
        self.col = None

class IndexTable:

    def __init__(self, ecu_file_1, ecu_file_2):
        """
        IndexTable constructor
        :param ecu_file_1, ecu_file_2: ECU files used for this table
        """
        self.indexes = OrderedDict()
        self.tables = OrderedDict()
        
        self.name = ecu_file_1.name + ' ' + ecu_file_2.name
        self.test_name = ecu_file_2.file_name

        # Custom cell formats
        self.header_format = book.add_format({'font_color': 'white', 'bg_color': 'black'})
        self.purple_format = book.add_format({'font_color': 'white', 'bg_color': 'purple'})
        self.blue_format = book.add_format({'font_color': 'white', 'bg_color': 'blue'})
        self.yellow_format = book.add_format({'font_color': 'black', 'bg_color': 'yellow'})
        self.red_format = book.add_format({'font_color': 'white', 'bg_color': 'red'})

        print('Created index table ' + self.name) 

    def push_index(self, function_1, function_2, jaccard_index):
        """
        Adds new 'cell' for table
        :param function_1, function_2: Header addresses
        :param jaccard_index: Jaccard Index calculation
        """
        if function_1 not in self.indexes.keys():
            self.indexes[function_1] = OrderedDict()
        self.indexes[function_1][function_2] = Cell(function_2, jaccard_index)

    def _write_format(self, sheet, highest_index, sensor_addr):
        """
        Format cells with result data
        :param sheet: Excel sheet to write write results
        :param highest_index: Highest jaccad index in row
        """

        if sensor_addr: 
            sheet.conditional_format(
                highest_index[0], highest_index[1], highest_index[0], highest_index[1],
                {'type': 'no_errors', 'format': self.purple_format}
            )  # match condition - color a match with man analysis purple
        else:
            sheet.conditional_format(
                highest_index[0], highest_index[1], highest_index[0], highest_index[1],
                {'type': 'no_errors', 'format': self.blue_format}
            ) # non-match - color it blue instead

    def write_results(self, book, gt):
        """
        Writes all results to Excel sheet
        :param book: Excel sheet containing result data
        :param test_blocks: Code blocks to test results with
        """
        print('Loading sheet ' + table.name)

        sheet = book.add_worksheet(table.name)
        sheet.freeze_panes(0, 1)
        sheet.set_column(0, 0, 23)

        row, col = 0, 0
        highest_index = [0, 0, 0]
        left_margin, right_margin = 0, 0
        tmp_key = ''
        addr_list = None
        sensor_addr = None        
        man_addrs = list()
        max_rows = {}

        bin_name = table.name.split(" ")[1]
        if bin_name in gt.keys(): # pull ID'd addr row of manual analysis data from table
            addr_list = gt[bin_name] 
        control = self.name.split(" ")[0] # pull control address from name
        # Write results to cells

        for _1, row_dict in table.indexes.items():
            for _2, cell in row_dict.items(): # bad temp names for variables following a recent update

                keys = [_1, _2]


                # Switch to new row
                jaccard_index = cell.jaccard
                if keys[0] != tmp_key: # process first pos of new row
                    tmp_key = keys[0]
                    row = row + 1
                    col = 1
                    cell.row = row
                    cell.col = col
                    # Side header for each row
                    sheet.write(row, 0, keys[0], self.header_format)
                    print('\t Added row {}'.format(keys[0]))

                    # Pull list of man analysis using keys
                    if addr_list is not None:
                        if "batt_voltage" in tmp_key or  "Battery Voltage" in tmp_key:
                            man_addrs = addr_list["Battery Voltage"]
                        elif "vehicle_speed" in tmp_key or "Vehicle Speed" in tmp_key:
                            man_addrs = addr_list["Vehicle Speed"]
                        elif "engine_speed" in tmp_key or "Engine Speed" in tmp_key:
                            man_addrs = addr_list["Engine Speed"]
                        elif "water_temp" in tmp_key or "Water Temp." in tmp_key :
                            man_addrs = addr_list["Water Temp."]
                        elif "ignition_timing" in tmp_key or "Igition Timing" in tmp_key:
                            # Note: this is misspelled in the actual datasheet, 
                            # so this is  the "correct" way to access it
                            man_addrs = addr_list["Igition Timing"]
                        elif "airflow" in tmp_key or "Airflow Sensor" in tmp_key:
                            man_addrs = addr_list["Airflow Sensor"]
                        elif "throttle_position" in tmp_key or "Throttle Position Sensors" in tmp_key:
                            man_addrs = addr_list["Throttle Position Sensors"]
                        elif "knock_correction" in tmp_key or "Knock Correction" in tmp_key:
                            man_addrs = addr_list["Knock Correction"]

                        sensor_nm = keys[0][keys[0].find("(")+1:keys[0].find(")")]
                        test = gt[control][sensor_nm].index(keys[0][0:6])
                        try:
                            sensor_addr = man_addrs[test]
                        except IndexError:
                            sensor_addr = None

                    if highest_index != [0, 0, 0]:
                        max_rows[keys[0]] = cell
                    highest_index = [0, 0, 0]

                    # Set address range margins
                    hex_addr = int(keys[0].split(' ')[0], 16)
                    left_margin = hex_addr - hex_margin
                    right_margin = hex_addr + hex_margin

                else:# process rest of row

                    col = col + 1
                    cell.row = row
                    cell.col = col

                    if len(man_addrs) is not 0:
                        ctrl_addr = keys[0][keys[0].find("(")+1:keys[0].find(")")]
                        test = gt[control][ctrl_addr].index(keys[0][0:6])
                        try:
                            sensor_addr = man_addrs[test]
                        except IndexError:
                            sensor_addr = None

                # Check if encountered higher Jaccard index
                if jaccard_index > highest_index[2]:
                    highest_index = [row, col, jaccard_index]
                    max_rows[keys[0]] = cell

                # read the sample graph and write everything to spreadsheet
                if (sensor_addr is not None) and (sensor_addr.rstrip() in keys[1]):
                    cell.flags["Control_Value"] = True
                    
                # Highlight "estimate" address margins
                if int(keys[1], 16) >= left_margin and int(keys[1], 16) <= right_margin:
                    cell.flags["Guess_Candidate"] = True

                sensor_addr = None

                # write col headers (addresses)
                sheet.write(0, col, keys[1], self.header_format)

        # # write all results to spreadsheet
        # for _, cell in table.indexes.items():
        for _1, row_dict in table.indexes.items():
            for _2, cell in row_dict.items(): # bad temp names for variables following a recent update
                keys = [_1, _2]        
                if cell in max_rows.values(): # mark maxes in-kind
                    cell.flags["Max_Row"] = True
                self._write_cells(sheet, cell, cell.row, cell.col, keys, round(cell.jaccard , 2))

    # Read the cell object, process the cells, write results to the sheet
    # Object flags determine what color to add
    # Add a new flag to the "flags" dict in the "cell" object if we need new
    # colors
    def _write_cells(self, sheet, cell, row, col, keys, jaccard_index):
        # write header for row

        # specify format for writing cell
        write_format = None
        if cell.flags["Max_Row"]:
            write_format = self.blue_format
            if cell.flags["Control_Value"]: 
                write_format = self.purple_format        
        elif cell.flags["Control_Value"]:
            write_format = self.red_format
        elif cell.flags["Guess_Candidate"]:
            write_format = self.yellow_format

        sheet.write(row, col, jaccard_index, write_format)

def _jaccard_index(list_1, list_2):
    """
    Calculate Jaccard index from two lists (Use shortest list as check)
    :param list_1, list_2: Lists to compare
    :returns: Jaccard index of list_1 & list_2
    """
    if len(list_1) < len(list_2):
        intersection = len([x for x in list_1 if x in list_2])
    else:
        intersection = len([x for x in list_2 if x in list_1])

    union = len(list_1) + len(list_2) - intersection

    if len(list_1) == len(list_2) == 0:
        ret = None
    else:
        ret = float(intersection) / union

    return ret 

def _create_gt_sorted_list(control):
    ret = OrderedDict()
    for sensor, addresses in control.iteritems():
        for address in addresses: 
            if (address not in ret.keys()):
                ret[address] = [sensor]
            else:
                ret[address].append(sensor)
    return ret

def _create_tables(control_files, ecu_files, gt):
    """
    Creates comparison tables
    :param ecu_files: List of EcuFile objects
    :param control_files: List of Control Files
    :returns: List of created tables
    """
    tables = []


    for control_file in control_files:

        control = control_file.name
        gt_sorted_list = _create_gt_sorted_list(gt[control])
        for ecu_file in ecu_files:
            table_indexes = set()
            table = IndexTable(control_file, ecu_file)

            addresses = {}
            for sensor, raw_addresses in gt[control].items():
                addresses[sensor] = []
                for raw_address in raw_addresses:
                    addresses[sensor].append(ur"{}".format(raw_address.rstrip())) 

            # Loop through functions in ECU files
            #for function_1, function_1_hashes in control_file.functions.items():
            #for sensor, addresses in gt[control].iteritems():
            for function_1, sensors in gt_sorted_list.iteritems():
                for sensor in sensors:
                    function_1_hashes = control_file.functions[function_1]

                    for function_2, function_2_hashes in ecu_file.functions.items():
                    # for all sensors and their functions in the list of ground truth items - The Row value
                        
                        func1_bottleneck_list = []
                        func2_bottleneck_list = []    
                        func1_instr_list = []
                        func2_instr_list = []

                        for val in function_1_hashes:
                            if type (val) is dict:
                                for addr, items in val.iteritems():
                                    func1_bottleneck_list.extend(items)
                            else:
                                func1_instr_list.append(val)

                        for val in function_2_hashes:
                            if type (val) is dict:
                                for addr, items in val.iteritems():
                                    func2_bottleneck_list.extend(items)
                            else:
                                func2_instr_list.append(val)

                            # test index method - 
                            # try comparing jaccard dist. for blocks, then average JD
                            # merit - compares bottlenecks to each other vs. whole func
                            
                        average_jaccard = None

                        #if len(func1_bottleneck_list) > 0:
                        average_jaccard = _jaccard_index(func1_bottleneck_list, func2_bottleneck_list)
                        
                        #     # test index method - 
                        #     # try comparing jaccard dist. for blocks, then average JD
                        #     # merit - compares bottlenecks to each other vs. whole func

                        row_name = function_1 + ' (' + sensor + ')'
                        total_ji = _jaccard_index(function_1_hashes, function_2_hashes)

                        if average_jaccard is not None:
                            total_ji = (total_ji + average_jaccard) / 2

                        table.push_index(row_name,
                            function_2,
                            total_ji
                        )
                        table_indexes.add(row_name)
                       #     break

        
            tables.append(table)

    return tables

# helper method to quickly convert our file names into a more consise format
# this format is used in JSONParser as the names for the excel spreadsheets
def _json_parser_format(infile):
    split = infile.split('/')
    split = split[len(split) - 1]
    split = split.split('-')
    split = split[0][4:] + '-' + split[1][2:] + '-' + split[4].split('.')[0]
    return split

# Process the ground truth/manual analysis data by loading it in
# This data is used to verify all of our nodes that are found using our
# automatic method
# Returns: Nested dictionary laid out as follows
# Binary name: Sensor name: [All sensor functions manually found]
# for each binary, sensor, and values in the provided file
def _process_gt(sheet):
    ret = dict()
    code_blocks = xlrd.open_workbook(sheet)
    gt = code_blocks.sheet_by_index(0) # pull man analysis ground truth
    i = 3 # skip first column - control test data
    bin_nms = dict()

    while i <= 29: # we have n valid/working samples currently
        bin_nms[i] = gt.cell(0, i).value
        i += 2

    sensor_nms = gt.col_values(0, 2)
    for col, bin_nm in bin_nms.iteritems(): 
        sensor_addr = gt.col_values(col, 2) 
        for addr in sensor_addr:
            addr = "{}".format(addr)
        code_block_addr = gt.col_values(col + 1, 2)
        
        tmp = {}
        for _ in range(0, 8):
            addrs = code_block_addr[_].splitlines()
            tmp[sensor_nms[_]] = list()
            for addr in addrs:
                if "???" not in addr: # only process defined addresses
                    tmp[sensor_nms[_]].append((ur"{}".format(addr.strip().lower())))
                else:
                    tmp[sensor_nms[_]].append(ur"0x0000") # Address 0000 will be our throwaway for ???
        ret[bin_nm] = tmp
        print "Loaded control info for bin {}".format(bin_nm)
    return ret

if __name__ == '__main__':
    ecu_files = []
    control_files = []
    gt = None 

    parser = argparse.ArgumentParser(
        description='Import and process M7700 JSON Files.')
#nargs='1', 
    parser.add_argument('json', metavar='json', type=str, default="test.json",
                        help='JSON Input')

    parser.add_argument('xlsx', metavar='xlsx', type=str, default="test.xlsx",
                        help='XLSX Output Filename')    
            
    parser.add_argument('-j', '--json', dest='json_test', action='store_true',
                        help='Output table results as a JSON data structure instead of an excel spreadsheet')
          
    parser.add_argument('-n', '--no-output', dest='no_output', action='store_true',
                        help='Supress all XLSX writing output.')
       
    parser.add_argument('-c', '--ctrl', dest='ctrl', nargs='+', type=str, 
                        help='List of control files.')

    parser.add_argument('-x', '--xml', metavar='xml', default="file.xml", type=str,
                        help='Specify XML Filename')

    args = parser.parse_args()
    tree = ET.parse(args.xml)
    root = tree.getroot()
    xml = root.findall('control')

    if args.json is None or args.xlsx is None:
            print('Run \'python JsonParser.py file.json output.xlsx')
            exit()

    gt = _process_gt("code_blocks.xlsx")
    controls = []

    # Pick out control files from XML
    for ctrl in xml:
        controls.append(_json_parser_format(ctrl.get('name')))

    # Open & parse JSON dump
    with open(args.json) as file:
        json_data = json.load(file, object_pairs_hook=OrderedDict)

        for file_name in json_data:
            ecu_file = EcuFile(file_name, json_data[file_name], gt)

            if ecu_file.name in controls:# or (ecu_file.name is not None and ecu_file.name in args.ctrl):
                control_files.append(ecu_file)
            #else: - uncomment to REMOVE control files from ecu_files list
            ecu_files.append(ecu_file)    

    # Write all table data to sheets
        # Setup Excel sheet
    book = xlsxwriter.Workbook(args.xlsx)

    tables = _create_tables(control_files, ecu_files, gt)

    for table in tables:
            table.write_results(book, gt)
            # write GT data to sheets

    jsons = {}
    if args.json_test: # JSON rep of max value in each row
        for table in tables:
            jsons[table.name] = OrderedDict()
            for sensor, row in table.indexes.iteritems():
                jsons[table.name][sensor] = None
                for index, cell in row.iteritems():
                    if cell.flags['Max_Row'] is True:
                        jsons[table.name][sensor] = cell.func_addr, cell.jaccard

        with open("parser_maxes.json", 'w') as fout: # write JSON to file
            json.dump(jsons, fout, indent=4, sort_keys=True)
            fout.close()
            
    if args.no_output is False:
        book.close()
        print('\nWrote values to {}\n'.format(args.xlsx))
        print('\nWrote Max array values to parser_maxes.json')
