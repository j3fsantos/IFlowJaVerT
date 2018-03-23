
function top(o) {
    for(var p in o) {
      var s = o[p].replace("script", "s");
      var test = s.contains("script");
      Assert(not test);
      o[p] = s;
    }
    return 0;
}

var o = { };

var s1_p = symb_string(s1_p);
var s1_v = symb_string(s1_v);

o[ s1_p ] = s1_v;
o[ "ok" ] = "safe";

top(o);
