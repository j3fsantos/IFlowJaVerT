var o = {
  // fib: function f_fib(x) {
  //   if (x < 3) {
  //     return 1;
  //   } else {
  //     return this.fib(x-1) + this.fib(x-2);
  //   }
  // },
  
  // fact: function f_fact(x) {
  //   if (x < 1) {
  //     return 1;
  //   } else {
  //     return this.fact(x-1) * x;
  //   }
  // },
  
  // sum: function f_sum(x) {
  //   if (x < 1) {
  //     return 0;
  //   } else {
  //     return this.sum(x-1) + x;
  //   }
  // },
  
  plusOne: function(x) {
    return x + 1;
  },
  
  minusOne: function(x) {
     return x - 1;
   },
  // 
  // timesTwo: function(x) {
  //   return x * 2;
  // },
};

var s1 = symb_string(s1);
// Assume((s1 = "fib") or (s1 = "fact") or (s1 = "sum"));
//Assume((s1 = "plusOne"));
var n1 = symb_number(n1);

// figure out which function to call
var total = o[s1](n1);

Assert(total = 10);