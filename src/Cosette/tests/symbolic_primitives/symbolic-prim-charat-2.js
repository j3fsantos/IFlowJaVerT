var v = 0;
var s1 = symb_string();
var s2 = "abcdef";

for(var i = 0; i < s2.length; i++) {
    if (s2.charAt(i) == s1.charAt(i)) {
	v++;
    }
}

jsil_assert(v === 6)




