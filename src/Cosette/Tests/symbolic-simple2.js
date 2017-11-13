var ___n_number_1 = jsil_make_symbolic_number (n1); 
var ___n_number_2 = jsil_make_symbolic_string (n2); 

jsil_assume ((___n_number_1 > 0));
jsil_assume ((___n_number_2 > 0));

var x = ___n_number_1 + ___n_number_2; 

jsil_assert ((x.length > 0));
x
