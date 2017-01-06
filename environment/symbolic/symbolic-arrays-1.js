var ___n_number = jsil_make_symbolic_number (); 
var ___s_string = jsil_make_symbolic_string (); 

jsil_assume ((___n_number > 1) && (___n_number < 3)); 

function f_three() { return "ten"; }

function f_two() { return 5; }

function f_one() { return "one"; }

function top(f1, f2) {
    var a = [ f_one, f_two, f_three ];
    var v1 = (a[f1])();
    var v2 = (a[f2])();
    if (v1 == v2) {
	return v1;
    } else {
	return 0;
    }
}

f_one();
f_two();
f_three();

var n = ___n_number;
top(n-1, ___s_string);
