var s1 = symb_string(s1); 
var n1 = symb_number(n1); 

Assume (n1 < 9);

function extend(o) {
  for(var p in o) {
    this[p] = o[p];
  }
}

var Q = {
  extend: extend
};

var input = {
  s: s1,
  n: n1
};

Q.extend(input);

var res = Q.n;
Assert(res > 10);