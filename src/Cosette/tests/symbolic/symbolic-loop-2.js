var s = symb_string(); 

var total = 0;
for(var i = 0; i < s.length; i++) {
    total += i;
}

Assert(total === 15);
