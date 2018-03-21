var f1 = symb_string (s1); 
var f2 = symb_string (s2); 

var a = [ 1, 2, 3 ];
var v1 = a[f1];
var v2 = a[f2];

Assert ((v1 === v2) && (0 < v1) && (v1 < 4));

v2
