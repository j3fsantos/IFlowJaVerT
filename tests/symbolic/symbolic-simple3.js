var f1 = jsil_make_symbolic_number (n1); 
var f2 = jsil_make_symbolic_number (n2); 

var a = [ 1, 2, 3 ];
var v1 = a[f1];
var v2 = a[f2];

jsil_assert ((v1 == v2));

v2
