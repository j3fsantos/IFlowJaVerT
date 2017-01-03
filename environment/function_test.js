/**
 @toprequires (emp)
 @topensures (
 	scope(g : #g) * fun_obj(g, #g, #g_proto) * 
 	scope(f : #f) * fun_obj(f, #f, #f_proto) * 
 	scope(y :  3) * scope(w : 7))
*/
var y = 3;


/**
	@id  g
	@rec false

	@pre  (scope(g : #g) * scope(f : #f) * scope(y : #y) * (z == #z) * types(#y : $$number_type, #z : $$number_type))
	@post (scope(g : #g) * scope(f : #f) * scope(y : #y) * (ret == (#z + #y)))
*/
var g = function (z) { return z + y };


/**
	@id  f
	@rec false

	@pre  (scope(g : #g) * scope(f : #f) * scope(y : #y) * (u == #u) * types(#u : $$number_type))
	@post (scope(g : #g) * scope(f : #f) * scope(y : #y) * (ret == (#u + 1)))
*/
function f (u) { return u + 1 }

var w = f(g(3))
