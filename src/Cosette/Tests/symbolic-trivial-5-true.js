var n = jsil_make_symbolic_number (); 
jsil_assume ((n > 0) && (n < 2000));
var f = function (n) {
 return n*10; 
}
var y = 3 + 7 + f(n);
var z = y + 7;
jsil_assert(z > 0); 
