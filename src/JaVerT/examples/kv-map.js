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
		((#c, "hasOwnProperty") -> None) * KVPairs(#c, kvs, keys) * empty_fields(#c : -u- (keys, -{ "hasOwnProperty" }-));
  	
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
    	MapProto(#mp) * (ret == this)
    )
*/
function Map () {
	this._contents = {};
	
	/* @invariant dataField(this, "_contents", #c)
	   @fold KVPairs(#c, -{ }-, -{ }-) */
	return this;
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
	
	@pre  (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) *
	      (#k --e-- #keys) * ({{ #k, #v }} --e-- #kvs)
	
	@post Map(this, #mp, #kvs, #keys) * MapProto(#mp) *
	      (ret == #v)
	      
	@PETAR Ok, so this is nasty. My reasoning would be
	
	0) We need to get the contents of the map in #c
	
	Scenario 1:
	1a) if (#k --e-- #keys) then we need to do a directed unfold of KVPairs for #k
	2a) directed fold for #k
	
	Scenario 2:
	1b) if ! (#k --e-- #keys) then we need to get that (#c, #k) -> None from emptyFields
	2b) put the key back in emptyFields (or maybe not needed)
	
	I don't think we have annotation mechanisms for all this (if-then-else)?
	We're gonna need serious callspecs
*/
Map.prototype.get = function (k) {
	/* @invariant dataField(this, "_contents", #c) */
    if (this._contents.hasOwnProperty(k)) { 
        return this._contents[k] 
    } else { return null }  
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