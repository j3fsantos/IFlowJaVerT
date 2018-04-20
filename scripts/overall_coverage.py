import sys
import json
import colored

# overall_coverage.py: merge the coverage info for different tests of the
# same library.
#
# invoke with: python3 overall_coverage.py [test1].js [test2].js ...
#
# there must be corresponding files [test1]_coverage_result.json, etc.


def load_coverage(names):
    cov = {}
    for name in names:
        base_name = name.split('.')[0]
        filename = base_name + '_coverage_result.json'
        with open(filename) as file:
            json_cov = file.read()
        cov[name] = json.loads(json_cov)
    return cov

def lines_consistent(cov):
    test_cases = list(cov.keys())
    init_case = test_cases[0]

    fnames = list(cov[init_case]['executable'].keys())
    fnames.remove('main') # it's named by default but we don't care

    consistent = True
    for fname in fnames:
        # get all executable lines and check sanity
        lines = cov[init_case]['executable'][fname]
        for test_case in test_cases:
            case_lines = cov[test_case]['executable'][fname]
            if case_lines != lines:
                consistent = False
    return consistent

def make_overall_coverage(cov):
    test_cases = list(cov.keys())
    init_case = test_cases[0]

    fnames = list(cov[init_case]['executable'].keys())
    fnames.remove('main') # it's named by default but we don't care
    
    if not lines_consistent(cov):
        raise ValueError('Line numbering not consistent, aborting.')

    overall = {}

    for fname in fnames:
        executable_lines = cov[init_case]['executable'][fname]
        executed_lines = set()

        for case in test_cases:
            executed_lines = executed_lines.union(cov[case]['executed'][fname])
        executed_lines = sorted(list(executed_lines))
                
        overall[fname] = {'executable': executable_lines, 'executed': executed_lines}

    return overall
    
def print_overall_coverage(overall_cov, test_name):
    
    # coloring stuff
    green = colored.attr('bold') + colored.fg('green')
    red = colored.attr('bold') + colored.fg('red')
    blue = colored.attr('bold') + colored.fg('blue')
    reset = colored.attr('reset')

    # get all functions associated with the test
    total_executable_lines = 0
    total_executed_lines = 0
    
    for fname in overall_cov:
        executable_lines = set(overall_cov[fname]['executable'])
        executed_lines = set(overall_cov[fname]['executed'])
        missing_lines = list(executable_lines.difference(executed_lines))
        missing_lines = sorted(missing_lines)
        
        # aggregated info
        if fname.startswith(test_name):
            print(fname)
            total_executable_lines += len(executable_lines)
            total_executed_lines += len(executed_lines)

        if missing_lines == []:
            print(green + '{}: executed all lines'.format(fname))
        else:
            print(red + '{}: missing lines {}'.format(fname, missing_lines))
        
        nb_exec_lines = len(executable_lines)
        nb_missing_lines = len(missing_lines)
        coverage_prop = (nb_exec_lines - nb_missing_lines)/nb_exec_lines
        print('{}: coverage {:.2%}\n'.format(fname, coverage_prop) + reset)

    # final print
    total_prop = total_executed_lines / total_executable_lines
    print(blue + '{}: {}/{} ({:.2%}) lines executed'.format(test_name,
                                                            total_executed_lines,
                                                            total_executable_lines,
                                                            total_prop) + reset)


def get_test_name(filenames):
    base_name = filenames[0].split('.')[0]
    test_name = base_name.split('-')[0]
    return test_name

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print('No input files provided. Aborting')
    else:
        filenames = sys.argv[1:]
        test_name = get_test_name(filenames)
        coverage = load_coverage(filenames)
        overall_coverage = make_overall_coverage(coverage)
        print_overall_coverage(overall_coverage, test_name)
