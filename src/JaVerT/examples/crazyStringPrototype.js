var s = new String ("baz"); 
var f = function () {}; 
f.prototype = s;
var o = new f(); 
o[0] 

