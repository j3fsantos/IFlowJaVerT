var f1 = jsil_make_symbolic_string (s1); 

var a = [ 17 ];

var v1 = a[f1];

jsil_Assert (!(v1 === 17));

v1