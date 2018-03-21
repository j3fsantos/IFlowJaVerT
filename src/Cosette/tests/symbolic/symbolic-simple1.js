var n_number_1 = symb_number (n1); 
var n_number_2 = symb_number (n2); 

Assume ((n_number_1 > 0));
Assume ((n_number_2 > 0));

var x = n_number_1 + n_number_2; 

Assert ((x > 0));
x
