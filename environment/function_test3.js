/**
@pred counter(c, c_val) :
	fun_obj(fcounter, c, #c_proto, #c_sc) *
   closure(x: c_val; fcounter: #c_sc) *
   types (c_val: $$number_type);
*/

/**
   @id  f1
   @pre  (emp * (x == #x) * types(#x: $$number_type))
   @post (counter(ret, #x))
*/
var f1 = function (x) {

   /**
      @id  fcounter
      @pre  (scope(x: #x) * types(#x: $$number_type))
      @post (scope(x: #x+1) * (ret == #))
   */
   return function () {
      return x++
   }

}
