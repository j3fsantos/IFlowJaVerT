/*
  @toprequires (emp)
  @topensures (scope(i: 0))
*/
var i = 0;

var x = 1;

/*
  @pre (emp * (x == #x) )
  @post (scope(w: #x+2))
*/
function f (x) {
   var w;
   w = x+2;

   return w
}

/*
  @pre (emp * (x == #x) )
  @post (emp)
*/
var foo = function (xixi) {
   return xixi + "coco";
}
