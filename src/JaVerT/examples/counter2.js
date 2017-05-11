/**
@pred counter(c, c_val) :
   standardObject(c) *
   dataField(c, "getCounter", #gc) *
   dataField(c, "incCounter", #ic) *
   fun_obj(inc_counter, #ic, #ic_proto, #ic_sc) *
   sc_scope(inc_counter, c: c_val, #ic_sc) *
   fun_obj(get_counter, #gc, #gc_proto, #gc_sc) * 
   o_chains(inc_counter: #ic_sc, get_counter: #gc_sc) * 
   types (c_val: $$number_type);
*/


/**
@toprequires (emp)
@topensures (
   scope(make_counter: #mc) *
   scope(counter_1: #c1) *
   scope(counter_2: #c2) *
   fun_obj(make_counter, #mc, #mc_proto, #mc_sc) *
   counter(#c1, 1) *
   counter(#c2, 0) * 
   scope(x: #x) *
   (#x == 1))
*/


/**
	@id  make_counter
	@rec false

	@pre  ( emp )
	@post ( counter(ret, 0)  )
*/
var make_counter = function () { 

	var c = 0; 

	/**
		@id  inc_counter
		@rec false

		@pre  ( scope(c: #c) * types(#c: $$number_type))
		@post ( scope(c: (#c+1)) * (ret == (#c+1)) )
	*/
	var incCounter = function () { 
		c++; 
		return c;
	}; 

	/**
		@id  get_counter
		@rec false

		@pre  ( scope(c: #c) * types(#c: $$number_type))
		@post ( scope(c: #c) * (ret == #c) )
	*/
	var getCounter = function () { 
		return c; 
	}; 

	var o = {
		getCounter: getCounter, 
		incCounter: incCounter
	}; 

	return o
};


var counter_1 = make_counter ();
var counter_2 = make_counter ();

counter_1.incCounter();


var x = counter_1.getCounter(); 


