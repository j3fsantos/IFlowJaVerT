/**
@toprequires (initialHeapPre())
@topensures (
   scope(w: 666) *
   scope(f1: #f1) *
   scope(f3_out: #f3) *
   scope(x: 2010) *
   FunctionObject(#f1, "f1", _, _) *
   FunctionObject(#f3, "f3", _, _)
   )
*/

var w = 666;

/**
   @id  f1
   @pre  (initialHeapPostWeak() * scope(w: #w) * (x1 == #x1) * types(#w: $$number_type, #x1: $$number_type))
   @post (initialHeapPostWeak() * scope(w: #w) * 
            FunctionObject(ret, "f3", #f3_sc, _) * 
            closure(z1: (#x1 + #w), z2: (#x1 + #w + 2); f3: #f3_sc))
*/
var f1 = function (x1) {
   var z1 = x1 + w;

   /**
      @id  f2
      @pre  (scope(w: #w) * scope(z1: #z1) * (x2 == #x2) *
               types(#w: $$number_type, #z1: $$number_type, #x2: $$number_type))
      @post (scope(w: #w) * scope(z1: #z1) *
               FunctionObject(ret, "f3", #f3_sc, _) *
               closure(z2: (#z1 + #x2); f3: #f3_sc) * 
               o_chains(f2: $$scope, f3: #f3_sc))
   */
   var f2 = function (x2) {
      var z2 = z1 + x2;

      /**
         @id  f3
         @pre  (initialHeapPostWeak() * scope(w: #w) * scope(z1: #z1) * scope(z2: #z2) * (x3 == #x3) *
                  types(#w: $$number_type, #z1: $$number_type, #z2: $$number_type, #x3: $$number_type))
         @post (initialHeapPostWeak() * scope(w: #w) * scope(z1: #z1) * scope(z2: #z2) *
                  (ret == (#w + #z1 + #z2 + #x3)))
      */
      var f3 = function (x3) {
         var z3 = w + z1 + z2 + x3;
         return z3;
      }

      return f3;
   }

   return f2(2);
}

var f3_out = f1(3);
var x = f3_out(4);
