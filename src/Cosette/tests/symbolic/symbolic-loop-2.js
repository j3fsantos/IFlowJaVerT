var s = jsil_make_symbolic_string(); 

var total = 0;
for(var i = 0; i < s.length; i++) {
    total += i;
}

jsil_Assert(total === 15);
