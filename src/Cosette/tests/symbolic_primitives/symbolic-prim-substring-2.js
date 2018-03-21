var v = 0;
var s1 = symb_string();
var s2 = symb_string();
var s3 = symb_string();

if (s1 == s2.substring(0, 2)) {
    v++;
}

if (s2 == s3.substring(0, 3)) {
    v++;
}

if (s1.length == 2) {
    v++;
}

if (s2.length == 3) {
    v++;
}

if (s3.length > 5) {
    v++;
}

if (s3.charAt(0) == "x") {
    v++;
}

if (s3.charAt(1) == "y") {
    v++;
}

if (s3.charAt(2) == "z") {
    v++;
}

jsil_assert(v === 8)


    




