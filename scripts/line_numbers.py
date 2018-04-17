import json
import os
import sys

test_names = ['arrays', 'bag', 'bstree', 'dictionary', 'heap', 'linkedlist',
              'multidictionary', 'priorityqueue', 'queue', 'set', 'stack']

def get_stats(test):
    filename = test + '1_line_numbers.json'
    with open(filename) as file:
        json_data = json.load(file)
    return json_data

def jsil_line_count(test, data):
    nb_lines = {}
    for fname in data['ids']:
        if fname.startswith(test):
            nb_lines[fname] = len(data['stats'][fname])
    return nb_lines

def js_line_count(test, data):
    nb_lines = {}
    for fname in data['ids']:
        if fname.startswith(test):
            js_lines = [js_line for (jsil_line, js_line) in data['stats'][fname]]
            js_lines = set(js_lines)
            if -1 in js_lines:
                nb_lines[fname] = len(js_lines) - 1
            else:
                nb_lines[fname] = len(js_lines)
    return nb_lines

def get_line_counts(tests):

    line_counts = {}
    for test in tests:
        data = get_stats(test)
        line_counts[test] = {'js': js_line_count(test, data),
                             'jsil': jsil_line_count(test, data)}
    return line_counts

def sum_line_counts(line_counts):
    for test in line_counts:
        sum_js = sum(line_counts[test]['js'].values())
        sum_jsil = sum(line_counts[test]['jsil'].values())
        print('{}:'.format(test))
        print('\t{} js lines'.format(sum_js))
        print('\t{} jsil lines'.format(sum_jsil))
        #print('\\texttt{{{}.js}} & 0 & {} & {} \\\\'.format(test, sum_js, sum_jsil))
