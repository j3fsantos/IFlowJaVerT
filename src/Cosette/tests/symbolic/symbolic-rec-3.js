
var o = {
    double: function f_double(x) {
	return 2*x;
    },

    top: function f_top(f, x) {
	return this[f](x);
    }
    
};

o.double(7);
o.top(p_string, n_number);

