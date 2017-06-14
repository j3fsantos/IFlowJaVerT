/**
@pred AbstractPi(o, p, v) :
   Pi (o, p, #v1, #desc, #v2, #v3, #v4) * DataDescriptor(#desc) * desc_val(#desc, v); 

  @pred isGood(p) : (p == #p) * isGood(#p);
  @pred isBad(p)  : (s == #s) * isBad(#s);

  @onlyspec isGoodF(p)
      pre:  [[ (p == #p) * isGood(#p) ]]
      post: [[ isGood(#p) * (ret == #r) * types (#r : $$object_type) ]]
      outcome: normal
*/

/**
   @id  getGoodProp
   @pre  (AbstractPi(o, p, #v) * isGood(p) * types(o: $$object_type, p: $$string_type) * 
            scope(isGoodF: #isGood_fun) * isNamedProperty(p) * 
            fun_obj(isGoodF, #isGood_fun, #isGood_fun_proto) * 
            (p == #p) * (o == #o))  
   @post (AbstractPi(#o, #p, #v)  * (ret == #v))
*/
var getGoodProp = function (o, p) {
   if (isGoodF(p)) {
      return o[p]; 
   } else {
      return null; 
   }
}
