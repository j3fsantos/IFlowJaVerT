var v = 0;
var s1 = symb_string();

if ("a" == s1.charAt(0)) {
    v++;
}

if ("b" != s1.charAt(1)) {
    v++;
}

if ("c" == s1.charAt(2)) {
    v++;
}

if ("d" != s1.charAt(3)) {
    v++;
}

if ("e" == s1.charAt(4)) {
    v++;
}

jsil_assert(v === 5)




