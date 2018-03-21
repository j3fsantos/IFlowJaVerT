var n = symb_number (); 

var total = 0;
for(var i = 0; i < n; i++) {
    total += i;
}

Assert(total === 15);
