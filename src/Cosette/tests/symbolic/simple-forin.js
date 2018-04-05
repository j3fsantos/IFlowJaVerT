
// this one is interesting (use hasOwnProperty)
// make one fail (outcome = 60) and 

var p1_string = symb_string(p1_string);
Assume(not (s-nth(p1_string, 0) = "@"));

function top(o) {
  var count = 0;
  for (var p in o) {
    count += 1;
  }
  return count;
}

var o = { a: 1, b: 2, c: 3 };

o[ p1_string ] = 4;
var res = top(o);