import sys
import json

def get_jsil_coverage(file):
    filename = file + '_coverage.txt'
    with open(filename) as coverage_file:
        lines = coverage_file.readlines()
    lines = [line.rstrip() for line in lines]
    lines = [line.split() for line in lines]
    lines = [(line[0][1:-1], int(line[1])) for line in lines]
    coverage = {}
    for (fname, fline) in lines:
        if fname not in coverage:
            coverage[fname] = []
        coverage[fname].append(fline)
    for fname in coverage:
        coverage[fname] = sorted(coverage[fname])
    return coverage

def get_js_file(file):
    filename = file + '.js'
    with open(filename) as js_file:
        lines = js_file.readlines()
    lines = [line.rstrip() for line in lines]
    return lines

#js_line[fname][jsil line number] = js line number
def get_js_jsil_mapping(file):
    filename = file + '_line_numbers.json'
    with open(filename) as js_lines_file:
        js_json = js_lines_file.read()
    js_line = json.loads(js_json)
    for fname in js_line:
        js_line[fname] = [line[1] for line in js_line[fname]]
    return js_line

def make_coverage(filename):
    base_file = filename.split('.')[0]
    
    coverage = get_jsil_coverage(base_file)
    js_lines = get_js_file(base_file)
    mapping = get_js_jsil_mapping(base_file)
    
    js_fnames = list(mapping.keys()) # functions without the internals
    
    # executable js lines
    exec_lines = {}
    for fname in js_fnames:
        if fname not in exec_lines:
            exec_lines[fname] = []
            
        for js_line in mapping[fname]:
            if (js_line not in exec_lines[fname]) and (js_line != -1):
                exec_lines[fname].append(js_line)
    
        exec_lines[fname] = sorted(exec_lines[fname])
#    print('exec_lines:\t{}'.format(exec_lines))
        
    # js lines we actually ran
    found_lines = {} 
    
    # initialize all functions to empty
    for fname in js_fnames:
        found_lines[fname] = []
        
    for fname in coverage:
        if fname in js_fnames:
            for jsil_line in coverage[fname]:
                js_line = mapping[fname][jsil_line]
                if (js_line not in found_lines[fname]) and (js_line != -1):
                    found_lines[fname].append(js_line)
#    print('found_lines:\t{}'.format(found_lines))

    return exec_lines, found_lines

def print_coverage(exec_lines, found_lines):
    js_fnames = list(exec_lines.keys())
    
    for fname in js_fnames:

        missing_lines = []
        for exec_line in exec_lines[fname]:
            if exec_line not in found_lines[fname]:
                missing_lines.append(exec_line)

        if missing_lines == []:
            print('{}: executed all lines'.format(fname))
        else:
            print('{}: missing lines {}'.format(fname, missing_lines))

        nb_exec_lines = len(exec_lines[fname])
        nb_missing_lines = len(missing_lines)
        coverage_prop = (nb_exec_lines - nb_missing_lines)/nb_exec_lines
        print('{}: coverage {:.2%}'.format(fname, coverage_prop))

if __name__ == "__main__":
    if (len(sys.argv) < 2):
        print("No input file provided. Aborting.")
    else:
        exec_lines, found_lines = make_coverage(sys.argv[1])
        print_coverage(exec_lines, found_lines)