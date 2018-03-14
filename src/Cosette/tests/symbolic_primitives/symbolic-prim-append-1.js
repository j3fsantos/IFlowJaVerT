var v = 0;
var s1 = jsil_make_symbolic_string();
var s2 = jsil_make_symbolic_string();

if ("ab" == s1.concat(s2)) {
    v++;
}

jsil_assert(v === 1)




