var v = 0;
var s1 = jsil_make_symbolic_string();
var s2 = jsil_make_symbolic_string();
var s3 = jsil_make_symbolic_string();

if (s1.length > 0 && "a" === s1.charAt(0)) {
    v++;
}

if (s2.length > 0) {
    v++;
}

var s = s1.replace(s2, "xyz");

if (s.length > 0 && "x" === s.charAt(0)) {
    v++;
}

if (s === s3) {
    v++;
}

jsil_assert(v === 4)




