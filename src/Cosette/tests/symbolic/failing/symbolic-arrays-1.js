var n_number = symb_number (n1); 
var s_string_1 = symb_string (s1); 
var s_string_2 = symb_string (s2); 

Assume ((n_number >= 0) and (n_number < 3)); 

function f_three() { return "ten"; }

function f_two() { return 5; }

function f_one() { return "one"; }

function top(f1, f2) {
    var a = [ f_one, f_two, f_three ];
    var v1 = (a[f1]);
    var v2 = (a[f2]);
    if (v1 === v2) {
	return v1;
    } else {
	return 0;
    }
}

f_one();
f_two();
f_three();

var n = n_number;
var x = top(s_string_1, s_string_2);

Assert (not (x = 0)); 