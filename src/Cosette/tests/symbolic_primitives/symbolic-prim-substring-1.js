var v = 0;
var s1 = symb_string();
var s2 = symb_string();

if (s1 == s2.substring(0,2)) {
    v++;
}

if (s1.length == 2) {
    v++;
}

if (s2.length > 3) {
    v++;
}

if (s2.charAt(1) == "x") {
    v++;
}

jsil_assert(v === 4)


    




