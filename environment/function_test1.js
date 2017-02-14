
/**
   @id  getCounter
   @pre  (emp)
   @post ((ret == #obj) * ())
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
      @id  getCounter
      @pre  (scope(count : #c) * types(#c : $$number_type))
      @post (scope(count : #c+1) * (ret == (#c+1)))
   */
   var incCounter = function () {
      cout++;
      return count;
   };

   return {
      getCounter: getCounter,
      incCounter: incCounter
   }
}
