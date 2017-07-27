/**
@pred idGenerator(ig, c_val, prefix) :
   standardObject(ig) *
   dataField(ig, "getNewId", #gni) * fun_obj(getNewId, #gni, #gni_proto, #gni_sc) *
   dataField(ig, "getCurId", #gci) * fun_obj(getCurId, #gci, #gci_proto, #gci_sc) *
   dataField(ig, "resetId",  #ri)  * fun_obj(resetId,  #ri,  #ri_proto,  #ri_sc)  *
   
   closure(counter: c_val, prefix: prefix; getNewId: #gni_sc, getCurId: #gci_sc, resetId: #ri_sc) *

   types (c_val: $$number_type, prefix: $$string_type);
*/


/**
	@toprequires (emp)
	@topensures (
	   scope(makeIdGenerator: #mig) *
	   scope(idGen1: #ig1) *
	   scope(idGen2: #ig2) *
	   fun_obj(makeIdGenerator, #mig, #mig_proto, #mig_sc) *
	   idGenerator(#ig1, 1, "banana") *
	   idGenerator(#ig2, 0, "avocado") * 
	   scope(x: #x) *
	   (#x == "idbanana1"))
*/


/**
	@id  makeIdGenerator
	@pre  ((prefix == #prefix) * types(#prefix: $$string_type))
	@post (idGenerator(ret, 0, #prefix))
*/
var makeIdGenerator = function (prefix) { 

	var counter = 0; 

	/**
		@id  getNewId
		@pre  (scope(counter: #c)     * scope(prefix: #prefix) * types(#c: $$number_type, #prefix: $$string_type)) 
		@post (scope(counter: (#c+1)) * scope(prefix: #prefix) * (ret == ("id" ++ #prefix ++ num_to_string(#c+1))))
	*/
	var getNewId = function () { 
		return "id" + prefix + ++counter;
	}; 

	/**
		@id  getCurId
		@pre  (scope(counter: #c) * scope(prefix: #prefix) * types(#c: $$number_type, #prefix: $$string_type)) 
		@post (scope(counter: #c) * scope(prefix: #prefix) * (ret == ("id" ++ #prefix ++ num_to_string(#c))))
	*/
	var getCurId = function () { 
		return "id" + prefix + counter; 
	}; 


	/**
		@id  resetId
		@pre  scope(counter: #c)
		@post scope(counter: 0)
	*/
	var resetId = function () { 
		counter = 0; 
	}; 

	var IdGenerator = {
		getNewId: getNewId, 
		getCurId: getCurId, 
		resetId:  resetId 
	}; 

	return IdGenerator
};


var idGen1 = makeIdGenerator ("banana");
var idGen2 = makeIdGenerator ("avocado");

idGen1.getNewId();


var x = idGen1.getCurId(); 


