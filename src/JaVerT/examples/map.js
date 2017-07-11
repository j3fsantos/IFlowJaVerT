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
	@pred Map(m, contents, mp) :
		ObjectWithProto(m, mp) *
		dataField(m, "_contents", contents) *
		standardObject(contents) *
		((contents, "hasOwnProperty") -> None) *
		((m, "get") -> None) *
		((m, "put") -> None) *
		types(mp : $$object_type);
  	
  	@pred MapProto(mp) :
		standardObject(mp) *
		dataField(mp, "get", #get_loc) * fun_obj(mapGet, #get_loc, #get_proto, #get_sc) *
		dataField(mp, "put", #put_loc) * fun_obj(mapPut, #put_loc, #put_proto, #put_sc) *
		((mp, "_contents") -> None);
*/

/**
	@id isValidKey
	
	@pre  ((key == #key) * validKey(#key))
	@post (ret == $$t)
		
	@pre ((key == #key) * invalidKey(#key))
	@post (ret == $$f)
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
    	Map(this, #contents, #hp) * 
    	MapProto(#mp)
    )
*/
function Map () {
   this._contents = {};
}

/**
	@id mapGet
	
	@pre (
		(key == #key) * validKey(#key) * 
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		dataField(#contents, #key, #v)
	)
	
	@post (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		dataField(#contents, #key, #v) *
		(ret == #v)
	)
	
	@pre (
		(key == #key) * validKey(#key) * 
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
		(key == #key) * invalidKey(#key) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
	
	@posterr (
		ErrorObjectWithMessage(err, "Invalid Key") *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
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

	@pre (
		(key == #key) * validKey(#key) * 
		(value == #value) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		emptyField(#contents, #key)
	)
	
	@post (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		dataField(#contents, #key, #value)
	)
	
	@pre (
		(key == #key) * validKey(#key) * 
		(value == #value) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		dataFieldGeneral(#contents, #key, #oldValue, $$t, #enum, #conf) 
	)
	
	@post (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		dataFieldGeneral(#contents, #key, #value, $$t, #enum, #conf)
	)
	
	@pre (
		(key == #key) * validKey(#key) * 
		(value == #value) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		dataFieldGeneral(#contents, #key, #oldValue, $$f, #enum, #conf) 
	)
	
	@posterr (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		dataFieldGeneral(#contents, #key, #oldValue, $$f, #enum, #conf) *
		isTypeError(err)
	)
	
	@pre (
		(key == #key) * invalidKey(#key) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
	
	@posterr (
		ErrorObjectWithMessage(err, "Invalid Key") *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
*/
Map.prototype.put = function (key, value) {
   if (isValidKey(key)) { 
       var contents = this._contents;
       contents[key] = value; 
   } else {
       throw new Error("Invalid Key")
   } 
} 