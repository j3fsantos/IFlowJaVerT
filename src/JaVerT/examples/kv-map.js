/**
	***** VALID AND INVALID KEYS *****
	
	@pred validKey(key) : 
		isNamedProperty(key) *
		(! (key == "hasOwnProperty"));
		
	@pred invalidKey(key) :
		types (key : $$undefined_type),
		types (key : $$null_type),
		types (key : $$boolean_type),
		types (key : $$number_type),
		types (key : $$string_type) * (key == "hasOwnProperty");
*/

/**	
	@pred Map (m, mp, kvs, keys) :
		ObjectWithProto(m, mp) *
		dataField(m, "_contents", #c) * standardObject(#c) *
		((m, "get") -> None) * ((m, "put") -> None) * ((m, "validKey") -> None) *
		((#c, "hasOwnProperty") -> None) * KVPairs(#c, kvs, keys) * empty_fields(#c : -u- (keys, "hasOwnProperty"));
  	
	@pred KVPairs (o, kvs, keys) :
		(kvs == -{ }-) * (keys == -{ }-),
		(kvs == -u- (-{ {{ #key, #value }} }-, #rkvs)) * (keys == -u- (-{ #key }-, #rkeys)) *
		validKey(#key) * dataField(o, #key, #value) * KVPairs(o, #rkvs, #rkeys);
		
  	@pred MapProto(mp) :
		standardObject(mp) *
		dataField(mp, "get", #get_loc) * fun_obj(mapGet, #get_loc, #get_proto, #get_sc) *
		dataField(mp, "put", #put_loc) * fun_obj(mapPut, #put_loc, #put_proto, #put_sc) *
		dataField(mp, "validKey", #vK_loc) * fun_obj(isValidKey, #vK_loc, #vK_proto, #vK_sc) *
		((mp, "_contents") -> None);
*/

/**
    @id  map

    @pre (
    	ObjectWithProto(this, #mp) *
        ((this, "_contents") -> None) *
        ((this, "get") -> None) *
        ((this, "put") -> None) *
        ((this, "validKey") -> None) *
        MapProto(#mp)
    )
    
    @post (
    	Map(this, #mp, #kvs, #keys) * (#kvs == -{ }-) * (#keys == -{ }-) * 
    	MapProto(#mp)
    )
*/
function Map () {
   this._contents = {};
}

/**
	@id isValidKey
	
	@pre  ((key == #key) * validKey(#key))
	@post (ret == $$t)
		
	@pre ((key == #key) * invalidKey(#key))
	@post (ret == $$f)
*/
Map.prototype.validKey = function (key) {
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}

/**
	@id mapGet
*/
Map.prototype.get = function getValue (key) {
	if (isValidKey(key)) { 
		if (this._contents.hasOwnProperty(key)) 
			return this._contents[key];
		else 
			return null
	} else throw new Error("Invalid Key")
	}

/**
	@id mapPut
*/
Map.prototype.put = function (key, value) {
   if (isValidKey(key)) { 
       var contents = this._contents;
       contents[key] = value; 
   } else {
       throw new Error("Invalid Key")
   } 
}