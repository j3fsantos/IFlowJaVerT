/**
@pred counter(c, c_val) :
   standardObject(c) *
   dataField(c, "getCounter", #gc) *
   dataField(c, "incCounter", #ic) *
   dataField(c, "decCounter", #dc) *
   fun_obj(incCounter, #ic, #ic_proto, #ic_sc) *
   fun_obj(getCounter, #gc, #gc_proto, #gc_sc) *
   fun_obj(decCounter, #dc, #dc_proto, #dc_sc) *
   closure(count: c_val; incCounter: #ic_sc, getCounter: #gc_sc, decCounter: #dc_sc) *
   types (c_val: $$number_type);
*/


/**
@toprequires (emp)
@topensures (
   scope(make_counter: #mc) *
   scope(counter_1: #c1) *
   scope(counter_2: #c2) *
   fun_obj(make_counter, #mc, #mc_proto, #mc_sc) *
   counter(#c1, 2) *
   counter(#c2, 1) *
   scope(count : 3))
*/

/**
   @id  make_counter
   @pre  (emp)
   @post (counter(ret, 0))
*/
var make_counter = function () {
   var count = 0;

   /**
   	@id  getCounter
   	@pre  (scope(count : #c) * types(#c : $$number_type))
   	@post (scope(count : #c) * (ret == #c))
   */
   var getCounter = function () {
      return count;
   };

   /**
      @id  incCounter
      @pre  (scope(count : #c) * types(#c : $$number_type))
      @post (scope(count : #c+1))
   */
   var incCounter = function () {
      count++;
   };
   
   /**
      @id  decCounter
      @pre  (scope(count : #c) * types(#c : $$number_type))
      @post (scope(count : (#c - 1)))
   */
   var decCounter = function () {
      count--
   };

   return {
      getCounter: getCounter,
      incCounter: incCounter,
      decCounter: decCounter
   }
}

var counter_1 = make_counter ();
var counter_2 = make_counter ();

counter_1.incCounter();
counter_1.incCounter();

counter_2.incCounter();

var count = counter_1.getCounter() + counter_2.getCounter()