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

total += o[ ___ev1_string ]( ___n1_number );
total += o[ ___ev2_string ]( ___n2_number );
total += o[ ___ev3_string ]( ___n3_number );

total;
