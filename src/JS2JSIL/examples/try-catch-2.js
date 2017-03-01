var x;
var i = 0;
while (i < 10) {
   try {
      if ((i % 2) ==  0) {
         throw "banana";
      }
      i++;
   } catch (e) {
      if (i == 8) {
         x = e;
         break
      }
      i++;
   }
}
x+i