var v = 0;
var s = symb_string(s);
var s1 = symb_string(s1);
var s2 = symb_string(s2);

if (s != s1) {
  if (s != s2) {
    if (s1 != s2) {
      v = 5;
    }
  }
}

Assert(v = 5)