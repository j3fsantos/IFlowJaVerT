
// make one fail (outcome = 60) and 

var p1_string = symb_string(p1_string);

function top(o) {
  var count = 0;
  for (var p in o) {
    count += 1;
  }
  return count;
}

var o = { a: 1, b: 2, c: 3, d: 4, e: 5, f: 6, g: 7 };

o[ p1_string ] = 4;
var res = top(o);

Assert(res = 8);