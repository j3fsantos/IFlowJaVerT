/**
@pred counter(c, c_val) :
   JSObject(c) *
   DataProp(c, "getCounter", #gc) *
   DataProp(c, "incCounter", #ic) *
   DataProp(c, "decCounter", #dc) *
   FunctionObject(#ic, "incCounter", #ic_sc, #ignore1) *
   FunctionObject(#gc, "getCounter", #gc_sc, #ignore2) *
   FunctionObject(#dc, "decCounter", #dc_sc, #ignore3) *
   closure(count: c_val; incCounter: #ic_sc, getCounter: #gc_sc, decCounter: #dc_sc) *
   types (c_val: $$number_type);
*/


/**
@toprequires (initialHeapPre())
@topensures (
   scope(make_counter: #mc) *
   scope(counter_1: #c1) *
   scope(counter_2: #c2) *
   FunctionObject(make_counter, #mc, #mc_sc, #ignore) *
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

var count = counter_1.getCounter() + counter_2.getCounter(); 
count 