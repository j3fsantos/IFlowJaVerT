var n = symb_number (n1);
Assume ((n > 0) and (n < 2000));
var f = function (n) {
  return n*10;
}
var y = 3 + 7 + f(n);
var z = y + 7;
Assert(z < 0);