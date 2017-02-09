var counter;

/**
   @id  incCounter

   @pre  (scope(counter: #c) * types(#c : $$number_type))
   @post (scope(counter: #c+1) * types(#c : $$number_type))
*/
var incCounter = function () { counter++; return counter; };