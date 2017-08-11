/**
@pred counter(c, c_val) :
	JSObject(c) *
  	DataProp(c, "getCounter", #gc) *
  	DataProp(c, "incCounter", #ic) *
  	FunctionObject(#gc, "get_counter", #gc_sc, #ignore2) *
   	FunctionObject(#ic, "inc_counter", #ic_sc, #ignore1) *
  	sc_scope(inc_counter, c: c_val, #ic_sc) *
   	o_chains(inc_counter: #ic_sc, get_counter: #gc_sc) * 
   	types (c_val: $$number_type);
*/


/**
@toprequires (initialHeapPre())
@topensures (
   scope(make_counter: #mc) *
   scope(counter_1: #c1) *
   scope(counter_2: #c2) *
   FunctionObject(#mc, "make_counter", #mc_sc, #ignore) *
   counter(#c1, 1) *
   counter(#c2, 0) * 
   scope(x: 1))
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


