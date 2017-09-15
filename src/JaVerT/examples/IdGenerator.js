/**
	@pred idGenerator(ig, sc_ig, c_val, prefix) :
	   JSObject(ig) * 
	   DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #gni_sc, _) *
	   DataProp(ig, "reset", #ri)  * FunctionObject(#ri, "reset", #ri_sc, _) *
	   closure(count: c_val, prefix: prefix; getId: #gni_sc, reset: #ri_sc) *
	   o_chains(getId : #gni_sc, makeIdGen : sc_ig) *
	   types (c_val: $$number_type, prefix: $$string_type);
	   
	What is the methodology?
	
		1) Build a predicate that describes the closure. It has to have:
			PARAMETERS: 
				- CL: the scope chain of the enclosing function
			INSIDE:
				- IM: the function objects representing the functions in the closure (here, getId and reset)
				- IM: a closure assertion connecting the ERs
				- CL: an o_chains assertion stating the overlap with the scope chain of the enclosing function
		
		2) The specs of the functions have to have:
			- PRE: an o_chains assertion of the form o_chains(<id_of_function_being_verified>: $$scope, <id_of_enclosing_function>: #sc) 
			       to connect the current scope with the scope of the enclosing function. Then, that #sc is passed to the predicate.
*/

/**
	@toprequires ( initialHeapPre() ) 
	@topensures 
	   scope(makeIdGen: #mig) *
	   scope(ig1: #ig1) *
	   scope(ig2: #ig2) *
	   FunctionObject(#mig, "makeIdGen", _, _) *
	   idGenerator(#ig1, _, 1, "foo") *
	   idGenerator(#ig2, _, 0, "bar") * 
	   scope(id1: #id1) *
	   (#id1 == "foo_id_0")
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
		@pre  (this == #ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #sc_ig, #c, #p)
		@post idGenerator(#ig, #sc_ig, #c + 1, #p) * (ret == (#p ++ "_id_" ++ num_to_string(#c)))
	*/
	var getId = function () { return prefix + "_id_" + (count++) };

	/**
		@id   reset
		@pre  (this == #ig) * o_chains(reset: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #sc_ig, #c, #p) 
		@post idGenerator(#ig, #sc_ig, 0, #p)
	*/
	var reset = function () { count = 0 }; 

	return { getId: getId, reset: reset }
};

var ig1 = makeIdGen ("foo");
var ig2 = makeIdGen ("bar");

var id1 = ig1.getId();