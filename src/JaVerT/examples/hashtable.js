/**
	***** VALID AND INVALID KEYS *****
	
	@pred validKey(key) : 
		types (key : $$string_type);
		
	@pred invalidKey(key) :
		types (key : $$undefined_type),
		types (key : $$null_type),
		types (key : $$boolean_type),
		types (key : $$number_type);
*/

/**
	***** Hashtbl abstraction *****
	
	@pred Hashtbl(ht, contents, htp) :
		ObjectWithProto(ht, htp) *
		dataField(ht, "_contents", contents) *
		standardObject(contents) *
		((contents, "hasOwnProperty") -> None) *
		((ht, "get") -> None) *
		((ht, "put") -> None) *
		types(htp : $$object_type);
  	
  	@pred HashtblProto(htp) :
		standardObject(htp) *
		dataField(htp, "get", #get_loc) * fun_obj(hashtblGet, #get_loc, #get_proto, #get_sc) *
		dataField(htp, "put", #put_loc) * fun_obj(hashtblPut, #put_loc, #put_proto, #put_sc) *
		((htp, "_contents") -> None);
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
	return (typeof(key) === "string") 
}


/**
    @id  hashtbl

    @pre (
    	ObjectWithProto(this, #htp) *
        ((this, "_contents") -> None) *
        ((this, "get") -> None) *
        ((this, "put") -> None) *
        HashtblProto(#htp)
    )
    
    @post (
    	Hashtbl(this, #contents, #hp) * 
    	HashtblProto(#htp) * 
    	(ret == $$empty)
    )
*/
function Hashtbl () {
   this._contents = {};
} 

/**
	@id hashtblGet
	
	@pre (
		(key == #key) * validKey(key) * 
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Hashtbl(this, #contents, #htp) * HashtblProto(#htp) *
		Pi(#contents, #key, #lcls, #d, #ls, #ltf, #lpv) * (1 <# l-len #ls)
	)
	
	@post (
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto) * 
		Hashtbl(this, #contents, #htp) * HashtblProto(#htp) * 
		Pi(#contents, #key, #lcls, #d, #ls, #ltf, #lpv) * (ret == $$null)
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
Hashtbl.prototype.get = function getValue (key) {
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
	@id hashtblPut
	
	@pre (
		(key == #key) * invalidKey(key) *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
	
	@posterr (
		(err == #err) * ErrorObjectWithMessage(#err, "Invalid Key") *
		scope(isValidKey : #iVK) * fun_obj(isValidKey, #iVK, #iVK_proto)
	)
*/
Hashtbl.prototype.put = function (key, value) {
   if (isValidKey(key)) { 
       this._contents[key] = value; 
   } else {
       throw new Error("Invalid Key")
   } 
} 