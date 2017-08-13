/**
	***** VALID AND INVALID KEYS *****
	
	@pred ValidKey(key) : 
		isNamedProperty(key) *
		(! (key == "hasOwnProperty"));
		
	@pred InvalidKey(key) :
		types (key : $$undefined_type),
		types (key : $$null_type),
		types (key : $$boolean_type),
		types (key : $$number_type),
		types (key : $$string_type) * (key == "hasOwnProperty");
*/

/**	
	@pred Map(m, contents, mp) :
		JSObjWithProto(m, mp) *
		DataProp(m, "_contents", contents) *
		JSObject(contents) *
		((contents, "hasOwnProperty") -> None) *
		((m, "get") -> None) *
		((m, "put") -> None) *
		types(mp : $$object_type);
  	
  	@pred MapProto(mp) :
		JSObject(mp) *
		DataProp(mp, "get", #get_loc) * FunctionObject(#get_loc, "mapGet", #get_sc, _) *
		DataProp(mp, "put", #put_loc) * FunctionObject(#put_loc, "mapPut", #put_sc, _) *
		((mp, "_contents") -> None);
*/

/**
	@id isValidKey
	
	@pre  ((key == #key) * ValidKey(#key))
	@post (ret == $$t)
		
	@pre ((key == #key) * InvalidKey(#key))
	@post (ret == $$f)
*/
function isValidKey(key) {
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}


/**
    @id  map

    @pre (
    	initialHeapPost() * 
    	JSObjWithProto(this, #mp) *
        ((this, "_contents") -> None) *
        ((this, "get") -> None) *
        ((this, "put") -> None) *
        MapProto(#mp)
    )
    
    @post (
    	initialHeapPost() * 
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
		initialHeapPost() * 
		(key == #key) * ValidKey(#key) * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		DataProp(#contents, #key, #v)
	)
	
	@post (
		initialHeapPost() * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		DataProp(#contents, #key, #v) *
		(ret == #v)
	)
	
	@pre (
		initialHeapPost() * 
		(key == #key) * ValidKey(#key) * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		EmptyProp(#contents, #key)
	)
	
	@post (
		initialHeapPost() * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		EmptyProp(#contents, #key) *
		(ret == $$null)
	)
	
	@pre (
		initialHeapPost() * 
		(key == #key) * InvalidKey(#key) *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _)
	)
	
	@posterr (
		initialHeapPost() * 
		ErrorObjectWithMessage(err, "Invalid Key") *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _)
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
		initialHeapPost() * 
		(key == #key) * ValidKey(#key) * 
		(value == #value) *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		EmptyProp(#contents, #key)
	)
	
	@post (
		initialHeapPost() * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		DataProp(#contents, #key, #value)
	)
	
	@pre (
		initialHeapPost() * 
		(key == #key) * ValidKey(#key) * 
		(value == #value) *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		DataPropGen(#contents, #key, #oldValue, $$t, #enum, #conf) 
	)
	
	@post (
		initialHeapPost() * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		DataPropGen(#contents, #key, #value, $$t, #enum, #conf)
	)
	
	@pre (
		initialHeapPost() * 
		(key == #key) * ValidKey(#key) * 
		(value == #value) *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) *
		DataPropGen(#contents, #key, #oldValue, $$f, #enum, #conf) 
	)
	
	@posterr (
		initialHeapPost() * 
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _) * 
		Map(this, #contents, #mp) * MapProto(#mp) * 
		DataPropGen(#contents, #key, #oldValue, $$f, #enum, #conf) *
		isTypeError(err)
	)
	
	@pre (
		initialHeapPost() * 
		(key == #key) * InvalidKey(#key) *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _)
	)
	
	@posterr (
		initialHeapPost() * 
		ErrorObjectWithMessage(err, "Invalid Key") *
		scope(isValidKey : #iVK) * FunctionObject(#iVK, "isValidKey", _, _)
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