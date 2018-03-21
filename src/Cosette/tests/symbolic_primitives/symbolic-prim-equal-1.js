var v = 0;
var s1 = symb_string();
var s2 = symb_string();
var s3 = symb_string();
var s4 = symb_string();
var s5 = symb_string();

if ("a" == s1) {
    v++;
}

if ("ab" == s2) {
    v++;
}

if ("abc" == s3) {
    v++;
}

if ("abcd" == s4) {
    v++;
}

if ("abcde" == s5) {
    v++;
}

jsil_assert(v === 5)




