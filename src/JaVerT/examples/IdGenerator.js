/**
@pred idGenerator(ig, c_val, prefix, sc_id) :
   JSObject(ig) * 
   DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #gni_sc, _) *
   DataProp(ig, "reset", #ri)  * FunctionObject(#ri, "reset", #ri_sc, _) *
   closure(count: c_val, prefix: prefix; getId: #gni_sc, reset: #ri_sc) * 
   o_chains(getId: #gni_sc, makeIdGen: sc_id) *
   o_chains(reset: #ri_sc,  makeIdGen: sc_id) *
   types (c_val: $$number_type, prefix: $$string_type);
*/

/**
	@toprequires ( initialHeapPre() ) 
	@topensures 
	   scope(makeIdGen: #mig) *
	   scope(ig1: #ig1) *
	   scope(ig2: #ig2) *
	   FunctionObject(#mig, "makeIdGen", #mig_sc, _) *
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
		@pre  idGenerator(#ig, #c,     #p, #sc_ig) * (this == #ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig)
		@post idGenerator(#ig, #c + 1, #p, #sc_ig) * (this == #ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig)
	*/
	var getId = function () { return prefix + "_id_" + (count++) }; 

	/**
		@id   reset
		@pre  idGenerator(#ig, #c, #p, #sc_ig) * (this == #ig) * o_chains(reset: $$scope, makeIdGen: #sc_ig)
		@post idGenerator(#ig,  0, #p, #sc_ig) * (this == #ig) * o_chains(reset: $$scope, makeIdGen: #sc_ig)
	*/
	var reset = function () { count = 0 }; 

	return { getId: getId, reset: reset }
};

var ig1 = makeIdGen ("foo");
var ig2 = makeIdGen ("bar");

var id1 = ig1.getId();