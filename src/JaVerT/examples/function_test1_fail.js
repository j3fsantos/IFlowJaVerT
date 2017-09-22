/**
@pred Counter(c, c_val) :
   JSObject(c) *
   DataProp(c, "getCounter", #gc) *
   DataProp(c, "incCounter", #ic) *
   FunctionObject(#gc, "getCounter", #gc_sc, _) *
   FunctionObject(#ic, "incCounter", #ic_sc, _) *
   closure(count: c_val; incCounter: #ic_sc, getCounter: #gc_sc) *
   types (c_val: $$number_type);
*/


/**
@toprequires (initialHeapPre())
@topensures (
   scope(make_counter: #mc) *
   scope(counter_1: #c1) *
   scope(counter_2: #c2) *
   FunctionObject(#mc, "make_counter", #mc_sc, _) *
   Counter(#c1, 1) *
   Counter(#c2, 0))
*/

/**
   @id  make_counter
   @pre  (initialHeapPost())
   @post (Counter(ret, 0))
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
      @post (scope(count : #c+1) * (ret == (#c+1)))
   */
   var incCounter = function () {
      count++;
      count++; 
      return count;
   };

   return {
      getCounter: getCounter,
      incCounter: incCounter
   }
}

var counter_1 = make_counter ();
var counter_2 = make_counter ();

counter_1.incCounter();
