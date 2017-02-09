var x;
var i = 0;
while (i < 10) {
   try {
      if ((i % 2) ==  0) {
         throw "banana";
      }
      i++;
   } catch (e1) {
      try {
         if ((i % 4) == 0) {
            throw "cucumber"
         }
         i++
      } catch (e2) {
         if (i == 8) {
            x = e1 + e2;
            break
         }
         i++;
      }
   }
}
x+i
