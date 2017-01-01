/**
 @toprequires (emp)
 @topensures (scope(y : 3) * scope(g: #g) * fun_obj(g, #g, #g_proto) * scope(w: 6))
*/
var y = 3;

/**
	@id  g
	@rec false

	@pre (scope(y : #y) * scope(g: #g) * (z == #z) * types(#y : $$number_type, #z : $$number_type))
	@post ((ret == (#z + #y)) * scope(y: #y) * scope(g: #g))
*/
var g = function (z) {
	return z + y
};

var w = g(3)
