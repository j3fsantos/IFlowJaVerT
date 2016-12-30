var n = jsil_make_symbolic_number (); 

var total = 0;
for(var i = 0; i < n; i++) {
    total += i;
}

jsil_assert(total === 15);
