var v = 0;
var s1 = jsil_make_symbolic_string();

if (s1.lastIndexOf("ab") === 0) {
    v++;
}

jsil_assert(v === 1)




