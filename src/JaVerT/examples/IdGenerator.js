/**
	@pred idGenerator(ig, c, prefix, sc_ig) :
		JSObject(ig) * 
		DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #sc, _) *
		DataProp(ig, "reset", #ri)  * FunctionObject(#ri,  "reset", #sc, _) *
		sc_scope(getId, count: c, #sc) * sc_scope(getId, prefix: prefix, #sc) *
		o_chains(getId : #sc, makeIdGen : sc_ig) *
		types (c: $$number_type, prefix: $$string_type);
*/

/**
	@toprequires ( initialHeapPre() ) 
	@topensures 
		scope(makeIdGen: #mig) *
		scope(ig1: #ig1) *
		scope(ig2: #ig2) *
		FunctionObject(#mig, "makeIdGen", _, _) *
		idGenerator(#ig1, 1, "foo", _) *
		idGenerator(#ig2, 0, "bar", _) * 
		scope(id1: #id1) *
		(#id1 == "foo_id_0")
*/

/**
	@id   makeIdGen
	@pre  ((prefix == #prefix) * types(#prefix: $$string_type))
	@post (idGenerator(ret, 0, #prefix, $$scope))
*/
var makeIdGen = function (prefix) { 

	var count = 0; 

	/**
		@id   getId
		@pre  (this == #ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #c, #p, #sc_ig)
		@post idGenerator(#ig, #c + 1, #p, #sc_ig) * (ret == (#p ++ "_id_" ++ num_to_string(#c)))
	*/
	var getId = function () { return prefix + "_id_" + (count++) };

	/**
		@id   reset
		@pre  (this == #ig) * o_chains(reset: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #c, #p, #sc_ig) 
		@post idGenerator(#ig, 0, #p, #sc_ig)
	*/
	var reset = function () { count = 0 }; 

	return { getId: getId, reset: reset }
};

var ig1 = makeIdGen ("foo");
var ig2 = makeIdGen ("bar");

var id1 = ig1.getId();