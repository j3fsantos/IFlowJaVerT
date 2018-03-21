var v = 0;
var s1 = symb_string();
var s2 = symb_string();

if ("ab" == s1.concat(s2)) {
    v++;
}

jsil_assert(v === 1)




