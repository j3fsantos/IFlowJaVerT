var v = 0;
var s1 = symb_string();
var s2 = symb_string();
var s3 = symb_string();
var s4 = symb_string();
var s5 = symb_string();

if (s1.length === 1) {
    v++;
}

if (s2.length === 2) {
    v++;
}

if (s3.length === 3) {
    v++;
}

if (s4.length === 4) {
    v++;
}

if (s5.length === 5) {
    v++;
}

jsil_assert(v === 5)




