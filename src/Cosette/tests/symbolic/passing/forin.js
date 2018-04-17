
// make one fail (outcome = 60) and 


function nbProp(o) {
  var count = 0;
  for (var p in o) {
    count += 1;
  }
  return count;
}

var o = { a: 1, b: 2, c: 3};

var s1 = symb_string(s1);
var s2 = symb_string(s2);
o[s1] = 4;
o[s2] = 5;

var res = nbProp(o);

Assert(res = 4);