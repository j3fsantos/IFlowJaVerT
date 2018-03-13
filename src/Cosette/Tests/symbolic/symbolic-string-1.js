
function f_three() { return this.z; }

function f_two() { return this.y; }

function f_one() { return this.x; }

var v = 0;
var o = { one: f_one, two: f_two, three: f_three, x: "0", y: "5", z: "10" };

var f = symb_string();
var n = symb_string();

if (o.hasOwnProperty(f) && o[f]() === n) {
    v = 1;
}

v;

