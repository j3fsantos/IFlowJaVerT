/**
@pred List(l, values) :
   standardObject(l) *
   dataField(l, "value", #v) *
   dataField(l, "next", #l) *
   (values == (#val :: #rest_values)) *
   (#val == {{ #text, #v }}) * 
   List(#l, #rest_values) * 
   types(#v : $$number_type, #val : $$list_type), 

   (l == $$null) * (values == {{ }});
*/


 /**
   @id  f

    @pre (
       (x == #x) * 
       (y == #y) *  
       List(#x, ({{"hole", #a1}} :: ({{"text", #a2}} :: #values_a))) * 
       List(#y, (#b1 :: (#b2 :: #values_b))) *
       types (#values_a : $$list_type, #values_b : $$list_type)
    )
    @post (
      (ret == (#a1 + #a2)) * 
      List(#x, ({{"hole", #a1}} :: ({{"text", #a2}} :: #values_a))) * 
      List(#y, (#b1 :: (#b2 :: #values_b))) *
      types (#values_a : $$list_type, #values_b : $$list_type)
    )
  */
function f (x, y) { 
   /** @unfold List(x, #dontcare1)                         */
   var a1 = x.value; 
   x = x.next;
   /** @invariant dataField(x, "next", #x2)               */
   /** @unfold List(#x2, #dontcare2)                      */
   var a2 = x.value; 
   /** @fold List(x, (#v1 :: (#v2 :: #values_a)))         */
   return a1 + a2
}