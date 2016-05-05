
function f_three() { return "ten"; }

function f_two() { return 5; }

function f_one() { return "one"; }

function top(f1, f2) {
    var o = { one: f_one, two: f_two, three: f_three };
    var v1 = (o[f1])();
    var v2 = (o[f2])();
    if (v1 == v2) {
	return v1;
    } else {
	return 0;
    }
}

f_one();
f_two();
f_three();

top(___p1_string, ___p2_string);

