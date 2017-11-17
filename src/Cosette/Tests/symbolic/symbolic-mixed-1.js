
function f_three() { return "ten"; }

function f_two() { return 5; }

function f_one() { return "one"; }

function top(f1, f2) {
    var o = { one: f_one, two: f_two, three: f_three };
    if (o.hasOwnProperty(f1) && o.hasOwnProperty(f2)) {
	var v1 = (o[f1])();
	var v2 = (o[f2])();
	if (v1 == v2) {
	    return v1;
	} else {
	    return 0;
	}
    } else {
	return 0;
    }
}

var p1 = jsil_make_symbolic_string();
//var p2 = jsil_make_symbolic_string();
var p2 = "three";
top(p1, p2);

