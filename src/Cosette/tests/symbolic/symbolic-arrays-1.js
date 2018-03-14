var ___n_number = jsil_make_symbolic_number (n1); 
var ___s_string_1 = jsil_make_symbolic_string (s1); 
var ___s_string_2 = jsil_make_symbolic_string (s2); 

jsil_assume ((___n_number >= 0) && (___n_number < 3)); 

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

var n = ___n_number;
var x = top(___s_string_1, ___s_string_2);

jsil_Assert (x !== 0); 