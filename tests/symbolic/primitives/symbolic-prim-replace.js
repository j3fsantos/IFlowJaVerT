var v = 0;
var s1 = "abcdefghijk";
var s2 = jsil_make_symbolic_string();

var s = s1.replace(s2, "xyz");

if ("a" === s.charAt(0)) {
    v++;
}

jsil_assert(v === 1)




