
// this one is interesting (use hasOwnProperty)
// make one fail (outcome = 60) and 


function top(o) {
  var count = 0;
  for (var p in o) {
    count += 1;
  }
  return count;
}

var o = { a: 1, b: 2, c: 3 };

var p1_string = symb_string(p1_string);

o[ p1_string ] = 4;

var res = top(o);

// var truc = symb_number(truc);
// Assume(truc = res);
// Assert(truc = 60);