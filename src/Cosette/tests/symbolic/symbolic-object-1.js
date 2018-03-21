
function top(base) {
    this.base = base;
    this.fib = function fib(x) {
	if (x < 3) {
	    return 1;
	} else {
	    return this.fib(x-1) + this.fib(x-2);
	};
    }
    this.silly = function silly(x) {
	return this.fib(x) + (this.base <= 3? this.base: 0);
    }
    return this;
}

var x = new top(base_number);
x.silly(n_number);

