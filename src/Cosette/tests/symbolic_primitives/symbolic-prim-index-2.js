var v = 0;
var s1 = jsil_make_symbolic_string();
var s2 = jsil_make_symbolic_string();
var s3 = jsil_make_symbolic_string();

if (s1.indexOf(s2) === 5) {
    v++;
}

if (s1.indexOf(s3) === 2) {
    v++;
}

if (s3.charAt(0) != s2.charAt(0)) {
    v++;
}

if (s3.length > 0) {
    v++;
}

if (s2.length > 0) {
    v++;
}

jsil_assert(v === 5)




