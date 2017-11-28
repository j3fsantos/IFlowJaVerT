/* get(m.put(k, v)) = v */


/** @id Map */
function Map () {
   this._contents = {};
}


/** @id mapGet */
Map.prototype.get = function (key) {

	if (this._contents.hasOwnProperty(key)) {
	  return this._contents[key] 
	} else 
	  return null 
}


var s1 = symb_string (s1);
var m = new Map(); 

m._contents[s1] = 42;
var key_val = m.get(s1); 
assert(key_val = 42)