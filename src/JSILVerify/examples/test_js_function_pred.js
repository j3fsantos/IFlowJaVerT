/**
 @toprequires (emp)
 @topensures (scope(x: 3))
*/
var x = 3;

/**
 @pre (scope(x: #x))
 @post (((ret, "g") -> #g) * ((ret, "ret") -> (y + #x)) * fun_obj(g, #g, #g_proto))
 @id f
*/
var f = function (y) {
   /**
    @pre (scope(y: #y) * (z == #z))
    @post (ret == (#z + #y))
    @id g
   */
   var g = function (z) {
      return z + y
   };
   var o = {
      g: g,
      ret: y + x
   }
   return o
}

var z = f(4)
