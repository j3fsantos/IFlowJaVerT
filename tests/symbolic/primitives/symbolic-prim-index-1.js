var v = 0;
var s1 = jsil_make_symbolic_string();

if ("abcdef".indexOf(s1) === 0) {
    v++;

    if (s1.indexOf("def") === 3) {
	v++;
    
    }
}

jsil_assert(v === 2)




