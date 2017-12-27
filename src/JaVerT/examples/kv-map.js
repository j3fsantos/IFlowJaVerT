/**
	***** VALID AND INVALID KEYS *****
	
	@pred ValidKey(key) : 
		isNamedProperty(key) *  
		(! (key == "hasOwnProperty"));
		
	@pred InvalidKey(key) :
		types (key : Undefined),
		types (key : Null),
		types (key : Bool),
		types (key : Num),
		types (key : Str) * (key == "hasOwnProperty");
*/

/**	
	@pred Map (m, mp, kvs, keys) :
		JSObjWithProto(m, mp) *
		DataProp(m, "_contents", #c) * JSObject(#c) *
		((m, "get") -> none) * ((m, "put") -> none) * ((m, "validKey") -> none) *
		((#c, "hasOwnProperty") -> none) * KVPairs(#c, kvs, keys) * EmptyProps(#c, -u- (keys, -{ "hasOwnProperty" }-));
  	
	@pred KVPairs (o, kvs, keys) :
		[def1] (kvs == -{ }-) * (keys == -{ }-),
		[def2] (kvs == -u- (-{ {{ #key, #value }} }-, #rkvs)) * (keys == -u- (-{ #key }-, #rkeys)) *
					ValidKey(#key) * DataProp(o, #key, #value) * KVPairs(o, #rkvs, #rkeys);
		
  	@pred MapProto(mp) :
		JSObject(mp) *
		DataProp(mp, "get", #get_loc) * FunctionObject(#get_loc, "mapGet", _, _) *
		DataProp(mp, "put", #put_loc) * FunctionObject(#put_loc, "mapPut", _, _) *
		DataProp(mp, "validKey", #vK_loc) * FunctionObject(#vK_loc, "isValidKey", _, _) *
		((mp, "_contents") -> none);
*/

/**
    @id  map

    @pre (
    	initialHeapPostWeak() * 
    	JSObjWithProto(this, #mp) *
        ((this, "_contents") -> none) *
        ((this, "get") -> none) *
        ((this, "put") -> none) *
        ((this, "validKey") -> none) *
        MapProto(#mp)
    )
    
    @post (
    	initialHeapPostWeak() * 
    	Map(this, #mp, #kvs, #keys) * (#kvs == -{ }-) * (#keys == -{ }-) * 
    	MapProto(#mp) * (ret == this)
    )
*/
function Map () {
	this._contents = {};
	
	/* @tactic assert( DataProp(this, "_contents", #c) )
	   @tactic fold KVPairs(#c, -{ }-, -{ }-) */
	return this;
}

/**
	@id isValidKey
	
	@pre  ((key == #key) * ValidKey(#key))
	@post (ret == true)
		
	@pre ((key == #key) * InvalidKey(#key))
	@post (ret == false)
*/
Map.prototype.validKey = function (key) {
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}

/**
	@id mapGet
	
	@pre     (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * InvalidKey(#k) * initialHeapPostWeak() 
	@posterr Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ErrorObjectWithMessage(err, "Invalid Key") * initialHeapPostWeak() 

	@pre  (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (! (#k --e-- #keys)) * initialHeapPostWeak() 
	@post Map(this, #mp, #kvs, #keys) * MapProto(#mp) * (ret == null) * initialHeapPostWeak() 
	
	@pre  (k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (#k --e-- #keys) * ({{ #k, #v }} --e-- #kvs) * initialHeapPostWeak() 
	@post Map(this, #mp, #kvs, #keys) * MapProto(#mp) * (ret == #v) * initialHeapPostWeak() 
*/
Map.prototype.get = function (k) {
	/* @tactic assert ( DataProp(this, "_contents", #c) ) */
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
	
	@pre    ((k == #k) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * InvalidKey(#k) * initialHeapPostWeak())
	@posterr Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ErrorObjectWithMessage(err, "Invalid Key") * initialHeapPostWeak() 

	@pre  ((k == #k) * (v == #v) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (! (#k --e-- #keys)) * initialHeapPostWeak())
 	@post Map(this, #mp, -u- (-{ {{ #k, #v }} }-, #kvs), -u- (-{ #k }-, #keys)) * MapProto(#mp) * initialHeapPostWeak() 

	@pre  ((k == #k) * (v == #v) * Map(this, #mp, #kvs, #keys) * MapProto(#mp) * ValidKey(#k) * (#k --e-- #keys) * 
			(#kvs == -u- (-{ {{ #k, #w }} }-, #rkvs)) * initialHeapPostWeak())
	@post Map(this, #mp, -u- (-{ {{ #k, #v }} }-, #rkvs), #keys) * MapProto(#mp) * initialHeapPostWeak() 
*/
Map.prototype.put = function (k, v) {
	/* @tactic assert( DataProp(this, "_contents", #c) * scope (v : #v) ) */
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