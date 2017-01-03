/**
 @toprequires (emp)
 @topensures (
 	scope(make_counter : #m) * fun_obj(make_counter, #m, #m_proto) *
 	scope(fc_1 : #f1) * fun_obj(fun_counter, #f1, #f1_proto) *
 	scope(fc_2 : #f2) * fun_obj(fun_counter, #f1, #f1_proto))
*/


/**
   @id  make_counter
   @rec false

   @pre  (emp)
   @post (scope(counter: 0) * fun_obj(fun_counter, #f, #f_proto) * (ret == #f))
*/
var make_counter = function (z) {
   var counter = 0;

   /**
   	@id  fun_counter
   	@rec false

   	@pre  (scope(counter: #c) * types(#c: $$int_type))
   	@post (scope(counter: #c + 1) * (ret == (#c + 1)))
   */
   var fun_counter = function () {
      counter += 1;
      return counter;
   }

   return fun_counter;
};

var fc_1 = make_counter ();
var fc_2 = make_counter ();

var c = fc_1 () + fc_2 () + fc_1 ()
