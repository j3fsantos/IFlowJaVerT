/**
	@pred uniqueKeys(c, ids) :
		types(c: $$number_type, ids : $$set_type) *
		(forall #x : $$number_type. ((! (#x --e-- ids)) \/ ((0 <=# #x) /\ (#x <# c))));

	@pred idGenerator(ig, sc_ig, c, ids) :
		JSObject(ig) * 
		DataProp(ig, "getId", #gni) * FunctionObject(#gni, "getId", #gni_sc, _) *
		sc_scope(getId, count: c, #gni_sc) * o_chains(getId : #gni_sc, makeIdGen : sc_ig) *
		(0 <=# c) * uniqueKeys(c, ids) * 
		types (c: $$number_type, ids : $$set_type);
*/

/**
	@toprequires initialHeapPre() 
	@topensures 
	   scope(makeIdGen: #mig) *
	   scope(ig1: #ig1) *
	   scope(ig2: #ig2) *
	   FunctionObject(#mig, "makeIdGen", _, _) *
	   idGenerator(#ig1, _, 1, -{ 0 }-) *
	   idGenerator(#ig2, _, 0, -{   }-) * 
	   scope(id1: #id1) *
	   (#id1 == 0)
*/


/**
	@id   makeIdGen
	@pre  emp
	@post idGenerator(ret, $$scope, 0, -{ }-)
*/
var makeIdGen = function () { 

	var count = 0; 

	/**
		@id   getId
		@pre  (this == #ig) * o_chains(getId: $$scope, makeIdGen: #sc_ig) * idGenerator(#ig, #sc_ig, #c, #ids)
		@post (! (#c --e-- #ids)) * idGenerator(#ig, #sc_ig, #c + 1, -u- (#ids, -{ #c }-)) * (ret == #c)
	*/
	var getId = function () { return (count++) };

	return { getId: getId }
};

var ig1 = makeIdGen ("foo");
var ig2 = makeIdGen ("bar");

var id1 = ig1.getId();