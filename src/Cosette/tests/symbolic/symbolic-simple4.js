var f1 = symb_number (n1); 
var f2 = symb_string (n2); 

var a = [ 1, 2, 3 ];
var v1 = a[ (f1 == 0)? 0: (f1 == 1)?1: 2];
var v2 = a[ (f2 === "zero")? "0": (f2 === "one")?"1": "2"];

Assert ((v1 == v2));

v2
