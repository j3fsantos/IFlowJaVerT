var v = 0;
var s1 = symb_string();
var s2 = symb_string();

if (s1.startsWith(s2)) {
    v++;
}

if (s2.startsWith("abc")) {
    v++;
}

if (s1.length > s2.length) {
    v++;
}

jsil_assert(v === 3)




