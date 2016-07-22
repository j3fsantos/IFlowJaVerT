
function f_three() { return this.z; }

function f_two() { return this.y; }

function f_one() { return this.x; }

function top(f, n) {
    var o = { one: f_one, two: f_two, three: f_three, x: "0", y: "5", z: "10" };
    if (o.hasOwnProperty(f) && o[f]() === n) {
	return "1";
    } else {
	return "0";
    }
}

//var s = jsil_make_symbolic_string();
var s = "three";
var v = jsil_make_symbolic_string();
top(s, v);
