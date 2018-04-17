import sys

def sum_lines(js_filename):
    basename = js_filename.split('.')[0]
    filename = basename + "_solver_time.txt"
    with open(filename) as time_file:
        lines = time_file.readlines()
    times = [int(line) for line in lines]

    # times are in milliseconds
    return sum(times)/1000

if __name__ == "__main__":
    if (len(sys.argv) < 2):
        print("No input file provided. Aborting.")
    else:
        print(sum_lines(sys.argv[1]))
