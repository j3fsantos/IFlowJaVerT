import re
import sys

endings = ["expect\(",
           "\).toBeTruthy\(\)",
           "\).toBeFalsy\(\)",
           "\).toBeUndefined\(\)",
           "\).toEqual\(.*\)"]

def remove_tests(file):
    with open(file) as js_file:
        lines = js_file.readlines()

    newlines = []
    for line in lines:
        for ending in endings:
            line = re.sub(ending, '', line)
        if line.lstrip().startswith('it('):
            newlines.append('//' + line.lstrip())
            newlines.append('beforeEach();\n')
        else:
            newlines.append(line)

    with open(file, "w") as js_file:
        for line in newlines:
            js_file.write(line)


def split_tests(file):
    with open(file) as js_file:
        lines = js_file.readlines()

    common_part = []

    cur_test = {}

    count = 0
    for line in lines:

        # we haven't reached the first test yet
        if count == 0:
            # there it is
            if line.count('it(') > 0:
                count += 1
                cur_test[count] = [line]
            else:
                common_part.append(line)

        # we're inside a test
        else:
            if line.count('it(') > 0:
                count += 1
                cur_test[count] = []
            cur_test[count].append(line)

    for test in cur_test:
        basefile = file.split('.')[0]
        filename = "{}{}.js".format(basefile, test)

        with open(filename, "w") as js_file:
            for line in common_part:
                js_file.write(line)
            js_file.write('// test {}\n'.format(test))
            for line in cur_test[test]:
                js_file.write(line)


if __name__ == "__main__":
    filename = sys.argv[1]
    split_tests(filename)
