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
	***** Map abstraction *****
	
	@pred Map(l, kvs, keys) : 
		(kvs == -{ }- ) * (keys == -{ }-) * emp,  

		(kvs == -u- (-{ {{ #key, #value }} }-, #rest)) * (keys == -u- ({{ #key }}, #rest_keys)) * 
			dataField(l, #key, #value) * validKey(#key) * validValue (#value) * Map(l, #rest); 


	@pred MapObject(m, mp, kvs, keys) :
		ObjectWithProto(m, mp) *
		dataField(m, "_contents", #contents) *
		standardObject(#contents) *
		((#contents, "hasOwnProperty") -> None) *
		((m, "get") -> None) *
		((m, "put") -> None) *
		Map(#contents, kvs, keys) *
		emptyFields(#contents, -u- (-{"hasOwnProperty"}-, keys)) *  
		types(mp : $$object_type);
  	
  	@pred MapProto(mp) :
		standardObject(mp) *
		dataField(mp, "get", #get_loc) * fun_obj(mapGet, #get_loc, #get_proto, #get_sc) *
		dataField(mp, "put", #put_loc) * fun_obj(mapPut, #put_loc, #put_proto, #put_sc) *
		((mp, "_contents") -> None);
*/

/**
	@id isValidKey
	
	@pre (
		(key == #key) * validKey(#key)
	)
	@post ( 
		ret == $$t 
	)
		
	@pre (
		(key == #key) * invalidKey(#key)
	)
	@post ( 
		ret == $$f
	)
*/
function isValidKey(key) {
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}


/**
    @id  map

    @pre (
    	ObjectWithProto(this, #mp) *
        ((this, "_contents") -> None) *
        ((this, "get") -> None) *
        ((this, "put") -> None) *
        MapProto(#mp)
    )
    
    @post (
    	MapObject(this, #hp, -{}-) * 
    	MapProto(#mp) * 
    	(ret == $$empty)
    )
*/
function Map () {
   this._contents = {};
}

/**
	@id mapGet

	
	@pre (
		(key == #key) * 
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		MapObject(this, #mp, -u- (-{ {{ #key, #value }} }-, #rest)) * MapProto(#mp) 
	)
	
	@post (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		MapObject(this, #mp, -u- (-{ {{ #key, #value }} }-, #rest)) * MapProto(#mp) * 
		(ret == #value)
	)
	
	@pre (
		(key == #key) * validKey(key) * 
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		emptyField(#contents, #key)
	)
	
	@post (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		emptyField(#contents, #key) *
		(ret == $$null)
	)
	
	@pre (
		(key == #key) * invalidKey(key) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
	
	@posterr (
		(err == #err) * ErrorObjectWithMessage(#err, "Invalid Key") *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
*/
Map.prototype.get = function getValue (key) {
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

/**
	@id mapPut
	
	@pre (
		(key == #key) * invalidKey(key) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
	
	@posterr (
		(err == #err) * ErrorObjectWithMessage(#err, "Invalid Key") *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
*/
Map.prototype.put = function (key, value) {
   if (isValidKey(key)) { 
       this._contents[key] = value; 
   } else {
       throw new Error("Invalid Key")
   } 
} 