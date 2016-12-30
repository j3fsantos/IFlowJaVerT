/**
 @toprequires (emp)
 @topensures (scope(y : 3) * fun_obj(g, #g, #g_proto))
*/
var y = 3;

/**
	@id  g
	@rec false
	
	@pre (scope(y : #y) * (z == #z) * types(#y : $$number_type, #z : $$number_type))
	@post (ret == (#z + #y))
*/
var g = function (z) {
	return z + y
};