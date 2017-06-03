/**
	@pred implementation(f, impl_name) :
		fun_obj(retfun, f, #f_proto, #f_sc) *
		sc_scope(retfun, name: impl_name, #f_sc);
*/

/** 
	@toprequires emp
	@topensures (
		scope (v1 : 41) * scope (v2 : 42) * scope (v3 : 43) *
		scope (i1 : #i1) * implementation(#i1, "enqueue") *
		scope (i2 : #i2) * implementation(#i2, "dequeue") *
		scope (i3 : #i3) * implementation(#i3, "whatever")
	)
*/

/**
	@id impl
	
	@pre  ((name == #name) * types (name : $$string_type))
	@post ((ret == #ret) * implementation(#ret, #name))
*/
function impl (name) {

	/**
		@id  retfun

		@pre  (scope(name : #name) * (#name == "enqueue") * types(#name : $$string_type))
		@post (scope(name : #name) * (ret == 41))
		
		@pre  (scope(name : #name) * (#name == "dequeue") * types(#name : $$string_type))
		@post (scope(name : #name) * (ret == 42))
		
		@pre  (scope(name : #name) * (! (#name == "enqueue")) * (! (#name == "dequeue")) * types(#name : $$string_type))
		@post (scope(name : #name) * (ret == 43))
	*/
	return (function () {
		if (name === "enqueue") {
			return 41; }
		else if (name === "dequeue")
			return 42;
		else 
			return 43;
	});
};

var i1 = impl("enqueue");
var i2 = impl("dequeue");
var i3 = impl("whatever");

var v1 = i1();
var v2 = i2();
var v3 = i3();

/** 
	We can verify that v1 holds 41, v2 holds 42, v3 holds 43.
	We can also verify that i1 is a function object corresponding to retfun whose name is enqueue.
*/