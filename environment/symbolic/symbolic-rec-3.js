
var o = {
    double: function f_double(x) {
	return 2*x;
    },

    top: function f_top(f, x) {
	return this[f](x);
    }
    
};

o.double(7);
o.top(___p_string, ___n_number);

