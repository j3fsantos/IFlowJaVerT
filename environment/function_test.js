/**
 @toprequires (emp)
 @topensures (scope(y : 3) * scope(g: #g) * scope(f: #f) *
 	fun_obj(g, #g, #g_proto) * fun_obj(f, #f, #f_proto) * scope(w: 6))
*/
var y = 3;


/**
	@id  g
	@rec false

	@pre (scope(y : #y) * scope(g: #g) * scope(f: #f) * (z == #z) * types(#y : $$number_type, #z : $$number_type))
	@post ((ret == (#z + #y)) * scope(y: #y) * scope(g: #g) * scope(f: #f))
*/
var g = function (z) {
	return z + y
};


/**
	@id  f
	@rec false

	@pre ((u == #u) * types(#u : $$number_type))
	@post ((ret == (#u + 1)))
*/
function f (u) { return u + 1}

var w = g(3)
