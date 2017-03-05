
/**
	@id  g
	@rec false

	@pre  (scope(g : #g) * scope(f : #f) * types(#y : $$number_type))
	@post (scope(g : #g) * scope(f : #f) * (ret == $$empty))
*/
var g = function () { };


/**
	@id  f
	@rec false

	@pre  (scope(g : #g) * scope(f : #f) * fun_obj(g, #g, #gproto))
	@post (scope(g : #g) * scope(f : #f))
*/
function f () { new g() }
