import sys
import re
import json

# regular expression for detecting symbolic values
regex_str = "symb_(number|string)\s*\((.*)\)"
regex = re.compile(regex_str)

# we need to make up values if they're missing in the valuation
counter = 0

def make_string_gen():
    counter = 0
    while counter < 1000000:
        counter += 1
        yield "_str__{}".format(counter)

make_string_generator = make_string_gen()
def make_string():
    return next(make_string_generator)

def make_number_gen():
    counter = 0
    while counter < 1000000:
        counter += 1
        yield counter

make_number_generator = make_number_gen()
def make_number():
    return next(make_number_generator)

# - if the line contains the declaration of a symbolic value, replace it with
#   the concrete value in the valuation if there is one
# - if the line contains an Assume, remove the line
# - if the line contains an Assert, replace it with a JS assert

def replace_line(line, line_number, valuation):
    
    # don't care about comments
    if line.lstrip().startswith('//'):
        return line

    # get rid of Assume/Assert
    elif ("Assume" in line) or ("Assert" in line):
        return ""

    # look for "symb_number" and "symb_string"
    found_symb = regex.search(line)
    if found_symb:
        symb_type = found_symb.group(1)
        symb_var = found_symb.group(2)
        found_symb = symb_var in valuation

        # look up the concrete value
        if found_symb:
            concrete_value = valuation[symb_var]
        else:
            if symb_type == "string":
                concrete_value = make_string()
            elif symb_type == "number":
                concrete_value = make_number()
            else:
                raise ValueError('unknown symbolic value type')

        # turn it into a string
        if symb_type == "string":
            concrete_string = '"{}"'.format(concrete_value)
        elif symb_type == "number":
            concrete_string = str(concrete_value)
        else:
            raise ValueError('unknown symbolic value type')
        
        # actually replace the call
        line = regex.sub(concrete_string, line)
        
        # remember if we had to make up the value
        if not found_symb:
            line += " // NOTE: made up missing symbolic {} in the valuation".format(symb_type)

    return line

def replace_file(filename, lines, model_name, valuation):
    new_filename = "{}_{}.js".format(filename, model_name)
    new_lines = [replace_line(line, i+1, valuation) for (line, i) in zip(lines, range(len(lines)))]
    with open(new_filename, "w") as new_file:
        for line in new_lines:
            new_file.write(line + "\n")


def make_concrete(js_filename):
    # read the JS file to modify
    if not (js_filename.endswith('.js')):
        print("JS input not a JS file. Aborting.")
        return

    file_short = js_filename.split('.')[0]

    js_lines = []
    with open(js_filename, "r") as js_file:
        js_lines = js_file.readlines()
        js_lines = [line.rstrip() for line in js_lines] # remove final \n

    # read the JSON file containing the concrete model for each outcome
    models_filename = "models_{}.json".format(file_short)
    with open(models_filename, "r") as models_file:
        models = json.load(models_file)

    for model in models:
        print("Model name: {}".format(model))
        valuation = models[model]
        if valuation == "unsat":
            print("\tModel unsatisfiable.")
        elif len(valuation) == 0:
            print("\tEmpty model (error?).")
        else:
            print("\tValuation:")
            for val in valuation:
                print("\t\t{} -> {}".format(val, valuation[val]))
            replace_file(file_short, js_lines, model, valuation)
        

def main():
    make_concrete(sys.argv[1])

main()
