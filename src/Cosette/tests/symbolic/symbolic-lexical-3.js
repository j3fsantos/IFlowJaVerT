var n = symb_number (n); 

function top() {

  var y = symb_string (y);

  return function inner(x) {
    var str = "";
    for(var z = 0; z != x; z++) {
        str = y + str;
    }
    return str;
  }
}

(top())( n );

