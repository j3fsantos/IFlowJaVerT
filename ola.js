/*
  @toprequires (scope(i: #i))
  @topensures (scope(i: 0))
*/
var i = 0;
/*
  @requires (scope(x: #x) * (#x > 0))
  @ensures (scope (w: #x*2)) 
*/
var f = function (x) {
   var w; 
   w = x*2;
   return w
}
