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
};

o.fib(1);
o.sum(1);
o.fact(1);

total += o[ ev1_string ]( n1_number );
total += o[ ev2_string ]( n2_number );
total += o[ ev3_string ]( n3_number );

total;
