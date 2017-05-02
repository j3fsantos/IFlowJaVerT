var f1 = jsil_make_symbolic_string (s1); 

var a = [ 1 ];
var v1 = a[f1];

jsil_assert ((v1 !== undefined));

v1