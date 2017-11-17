/*get(m.put(k, v)) = v */


function Map () {
   this._contents = {};
}

function isValidKey (key) {
    return (typeof (key) === 'string') && (key !== '') && (key[0] !== "@"); 
}


Map.prototype.get = function get (key) {
  var result;

  if (isValidKey(key)) { 
    if (this._contents.hasOwnProperty(key)) {
      result = this._contents[key] 
    } else {
      result = null 
    }  
    return result
  } else {
    throw new Error("Invalid Key")
  }
}


Map.prototype.put = function put (key, value) {
   if (isValidKey(key)) { 
       this._contents[key] = value; 
   } else {
       throw new Error("Invalid Key")
   } 
}

var ___p1_string = symb_string (s1);
var ___v1_number = symb_number (n1);
var m = new Map(); 

if (isValidKey (___p1_string)) { 
  m.put(___p1_string, ___v1_number); 
  var key_val = m.get(___p1_string); 
  jsil_assert(key_val = ___v1_number)
} else { }


