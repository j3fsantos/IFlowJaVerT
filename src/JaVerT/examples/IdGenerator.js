/**
@pred idGenerator(ig, c_val, prefix) :
   JSObject(ig) * 
   DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #gni_sc, _) *
   DataProp(ig, "reset", #ri)  * FunctionObject(#ri, "reset", #ri_sc, _) *
   closure(count: c_val, prefix: prefix; getId: #gni_sc, reset: #ri_sc) * 
   types (c_val: $$number_type, prefix: $$string_type);
*/

/**
@pred IDGeneratorAlternate(ig, c_val, prefix, sc_id) :
   JSObject(ig) * 
   DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #gni_sc, _) *
   DataProp(ig, "reset", #ri)  * FunctionObject(#ri, "reset", #ri_sc, _) *
   closure(count: c_val, prefix: prefix; getId: #gni_sc, reset: #ri_sc) * 
   o_chains(getId: #gni_sc, makeIdGen: sc_id) *
   types (c_val: $$number_type, prefix: $$string_type);
*/

/**
	@toprequires (initialHeapPre())
	@topensures (
	   scope(makeIdGen: #mig) *
	   scope(ig1: #ig1) *
	   scope(ig2: #ig2) *
	   FunctionObject(#mig, "makeIdGen", #mig_sc, _) *
	   idGenerator(#ig1, 1, "foo") *
	   idGenerator(#ig2, 0, "bar") * 
	   scope(id1: #id1) *
	   (#id1 == "foo_id_0"))
*/


/**
	@id   makeIdGen
	@pre  ((prefix == #prefix) * types(#prefix: $$string_type))
	@post (idGenerator(ret, 0, #prefix))
*/
var makeIdGen = function (prefix) { 

	var count = 0; 

	/**
		@id   getId
		
		@pre  (scope(count: #c)     * scope(prefix: #prefix) * types(#c: $$number_type, #prefix: $$string_type)) 
		@post (scope(count: (#c+1)) * scope(prefix: #prefix) * (ret == (#prefix ++ "_id_" ++ num_to_string(#c))))
		
		@pre  IDGeneratorAlternate(#ig, #c, #p, #sc_ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig)
		@post IDGeneratorAlternate(#ig, #c + 1, #p, #sc_ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig)
	*/
	var getId = function () { return prefix + "_id_" + (count++) }; 

	/**
		@id   reset
		@pre  scope(count: #c)
		@post scope(count: 0)
	*/
	var reset = function () { count = 0 }; 

	return { getId: getId, reset: reset }
};


var ig1 = makeIdGen ("foo");
var ig2 = makeIdGen ("bar");

var id1 = ig1.getId();