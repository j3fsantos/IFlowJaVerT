/**
  @return: "ten"
*/

var s1 = symb_string(s1);
var s2 = symb_string(s2);
var n1 = symb_string(n1);

function f_three() { return s1; }

function f_two() { return n1; }

function f_one() { return s2; }

function top(f1, f2) {
  var a = [ f_one, f_two, f_three ];
  var v1 = (a[f1])();
  var v2 = (a[f2])();
  if (v1 == v2) {
    return v1;
  } else {
    return 0;
  }
}

f_one();
f_two();
f_three();

var n2 = symb_number(n2);
var s3 = symb_string(s3);
// Assume(n2 = 2);
// Assume(s3 = "2");

var ret1 = top(n2, s3);

Assert(((n2 = 0) and (s3 = "0") and (ret1 = s2)) or ((n2 = 1) and (s3 = "1") and (ret1 = n1)) or ((n2 = 2) and (s3 = "2") and (ret1 = s1)) or (ret1 = 0));