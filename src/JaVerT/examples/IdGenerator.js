/**
@pred idGenerator(ig, sc_ig, c_val, prefix) :
   JSObject(ig) * 
   DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #gni_sc, _) *
   DataProp(ig, "reset", #ri)  * FunctionObject(#ri, "reset", #ri_sc, _) *
   closure(count: c_val, prefix: prefix; getId: #gni_sc, reset: #ri_sc, makeIdGen: sc_ig) * 
   types (c_val: $$number_type, prefix: $$string_type);
*/

/**
	@toprequires (initialHeapPre())
	@topensures (
	   scope(makeIdGen: #mig) *
	   scope(ig1: #ig1) *
	   scope(ig2: #ig2) *
	   FunctionObject(#mig, "makeIdGen", _, _) *
	   idGenerator(#ig1, _, 1, "foo") *
	   idGenerator(#ig2, _, 0, "bar") * 
	   scope(id1: #id1) *
	   (#id1 == "foo_id_0"))
*/

/**
	@id   makeIdGen
	@pre  ((prefix == #prefix) * types(#prefix: $$string_type))
	@post (idGenerator(ret, $$scope, 0, #prefix))
*/
var makeIdGen = function (prefix) { 

	var count = 0; 

	/**
		@id   getId
		@pre  (this == #ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #sc_ig, #c, #prefix)
		@post idGenerator(#ig, #sc_ig, #c + 1, #prefix) * (ret == (#prefix ++ "_id_" ++ num_to_string(#c)))
		
	*/
	var getId = function () { 
		return prefix + "_id_" + (count++) 
	}; 

	/**
		@id   reset
		@pre  (this == #ig) * o_chains(reset: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #sc_ig, #c, #prefix)
		@post idGenerator(#ig, #sc_ig, 0, #prefix)
	*/
	var reset = function () { 
		count = 0 
	}; 

	return { 
		getId: getId, 
		reset: reset 
	}
};

var ig1 = makeIdGen ("foo");
var ig2 = makeIdGen ("bar");

var id1 = ig1.getId();