var total = 0;

var o = {
    fib: function f_fib(x) {
	if (x < 3) {
	    return 1;
	} else {
	    return this.fib(x-1) + this.fib(x-2);
	}
    },

    fact: function f_fact(x) {
	if (x < 1) {
	    return 1;
	} else {
	    return this.fact(x-1) * x;
	}
    },

    sum: function f_sum(x) {
	if (x < 1) {
	    return 0;
	} else {
	    return this.sum(x-1) + x;
	}
    },

    doit: function f_doit(x, y) {
	if (x == 1) {
	    return this.fib(y);
	} else if (x == 2) {
	    return this.fact(y);
	} else if (x == 3) {
	    return this.sum(y);
	} else {
	    return 0;
	}
    }
};


total += o.doit( ev1_number , n1_number );
total += o.doit( ev2_number , n2_number );
total += o.doit( ev3_number , n3_number );

total;
