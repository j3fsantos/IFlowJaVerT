
var o = {
    top: function f_top(x) {
	if (x < 3) {
	    return 1;
	} else {
	    return this.top(x-1) + this.top(x-2);
	}
    }
};

o.top(6);

