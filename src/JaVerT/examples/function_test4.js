/**
	@id  g
	@rec false

	@pre  ( emp )
	@post ( ret == $$empty )
*/
var g = function () { };


/**
	@id  f
	@rec false

	@pre  (scope(g : #g) * scope(f : #f) * fun_obj(g, #g, #gproto))
	@post (scope(g : #g) * scope(f : #f) * fun_obj(g, #g, #gproto))
*/
function f () { new g() }
