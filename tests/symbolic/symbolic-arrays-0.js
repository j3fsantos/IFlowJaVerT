var f1 = jsil_make_symbolic_string (s1); 

var a = [ 17 ];
var v1 = a[f1];

jsil_assert ((v1 === 17));

v1