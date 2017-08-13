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
	@pred Map (m, mp, kvs, keys) :
		JSObjWithProto(m, mp) *
		DataProp(m, "_contents", #c) * JSObject(#c) *
		((m, "get") -> None) * ((m, "put") -> None) * ((m, "validKey") -> None) *
		((#c, "hasOwnProperty") -> None) * KVPairs(#c, kvs, keys) * EmptyProps(#c, -u- (keys, -{ "hasOwnProperty" }-));
  	
	@pred KVPairs (o, kvs, keys) :
		[def1] (kvs == -{ }-) * (keys == -{ }-),
		[def2] (kvs == -u- (-{ {{ #key, #value }} }-, #rkvs)) * (keys == -u- (-{ #key }-, #rkeys)) *
					ValidKey(#key) * DataProp(o, #key, #value) * KVPairs(o, #rkvs, #rkeys);
		
  	@pred MapProto(mp) :
		JSObject(mp) *
		DataProp(mp, "get", #get_loc) * FunctionObject(#get_loc, "mapGet", _, _) *
		DataProp(mp, "put", #put_loc) * FunctionObject(#put_loc, "mapPut", _, _) *
		DataProp(mp, "validKey", #vK_loc) * FunctionObject(#vK_loc, "isValidKey", _, _) *
		((mp, "_contents") -> None);
*/

/**
    @id  map

    @pre (
    	initialHeapPost() * 
    	JSObjWithProto(this, #mp) *
        ((this, "_contents") -> None) *
        ((this, "get") -> None) *
        ((this, "put") -> None) *
        ((this, "validKey") -> None) *
        MapProto(#mp)
    )
    
    @post (
    	initialHeapPost() * 
    	Map(this, #mp, #kvs, #keys) * (#kvs == -{ }-) * (#keys == -{ }-) * 
    	MapProto(#mp) * (ret == this)
    )
*/
function Map () {
	this._contents = {};
	
	/* @invariant DataProp(this, "_contents", #c)
	   @tactic fold KVPairs(#c, -{ }-, -{ }-) */
	return this;
}

/**
	@id isValidKey
	
	@pre  ((key == #key) * ValidKey(#key))
	@post (ret == $$t)
		
	@pre ((key == #key) * InvalidKey(#key))
	@post (ret == $$f)
*/
Map.prototype.validKey = function (key) {
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}

/**
	@id mapGet
	
	@pre     (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * InvalidKey(#k) * initialHeapPost() 
	@posterr Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ErrorObjectWithMessage(err, "Invalid Key") * initialHeapPost() 

	@pre  (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (! (#k --e-- #keys)) * initialHeapPost() 
	@post Map(this, #mp, #kvs, #keys) * MapProto(#mp) * (ret == $$null) * initialHeapPost() 
	
	@pre  (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (#k --e-- #keys) * ({{ #k, #v }} --e-- #kvs) * initialHeapPost() 
	@post Map(this, #mp, #kvs, #keys) * MapProto(#mp) * (ret == #v) * initialHeapPost() 
*/
Map.prototype.get = function (k) {
	/* @invariant DataProp(this, "_contents", #c) */
	if (this.validKey(k)) {
		/* @tactic if (#k -e- #keys) then { unfold KVPairs(#c, #kvs, #keys) [def2 with (#key := #k) and (#value := #v)] } */
	    if (this._contents.hasOwnProperty(k)) { 
	    	var result = this._contents[k];
	    	/* @tactic fold KVPairs(#c, #kvs, #keys) */
	        return result
	    } else { return null }
	} else
		throw new Error("Invalid Key")
}

/**
	@id mapPut
	
	@pre     (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * InvalidKey(#k) * initialHeapPost() 
	@posterr Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ErrorObjectWithMessage(err, "Invalid Key") * initialHeapPost() 

	@pre  (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (! (#k --e-- #keys)) * initialHeapPost() 
	@post Map(this, #mp, -u- (-{ {{ #k, #v }} }-, #kvs), -u- (-{ #k }-, #keys)) * MapProto(#mp) * initialHeapPost() 

	@pre  (k == #k) * (v == #v) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (#k --e-- #keys) * (#kvs == -u- ({{ #k, #w }}, #rkvs)) * initialHeapPost() 
	@post Map(this, #mp, -u- (-{ {{ #k, #v }} }-, #rkvs), #keys) * MapProto(#mp) * initialHeapPost() 
*/
Map.prototype.put = function (k, v) {
	/* @invariant DataProp(this, "_contents", #c) * scope (v : #v) */
	if (this.validKey(k)) { 
		/* @tactic if (#k -e- #keys) then { unfold KVPairs(#c, #kvs, #keys) [def2 with (#key := #k) and (#value := #w) and (#rkvs := #rkvs)] } */
		this._contents[k] = v; 
		/* @tactic if (#k -e- #keys) 
			then { fold KVPairs(#c, -u- (-{ {{ #k, #v }} }-, #rkvs), #keys) } 
			else { fold KVPairs(#c, -u- (-{ {{ #k, #v }} }-, #kvs), -u- ( -{ #k }-, #keys)) } */
		return v;
	} else
		throw new Error("Invalid Key")
}