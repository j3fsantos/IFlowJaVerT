var f;
f = function (x, y, z) { 
	var g;
	g = function (t, u, v) {
		var h;
		h = function (w, x, y, z) {
			return 15;
		}
		return (h());
	}
	
	return (g());
};

f();