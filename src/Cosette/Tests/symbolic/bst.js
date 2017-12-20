/**
	
*/

/**
	@id makeNode
	
	
*/
function make_node(v)
{
  var node = {
    value : v,
    left  : null,
    right : null
  };
  return node;
}

/**
	@id insert

	
*/
function insert(v, t)
{
  var result;
  

  if (t === null) {
  
  	result = make_node(v);
  	
  	
    return result
  }

  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value) 
    t.right = insert(v, t.right);

  
  return t;
}

/**
	@id find
	
	
*/
function find (v, t)
{
	var result;

	
	if (t === null)
		result = false;
	else if (v === t.value)
		result = true;
	else {
		if (v < t.value)
		  result = find(v, t.left) 
		else
		  result = find(v, t.right);
	}
	
	
	return result;
}

/**
	@id findMin
	
	
*/
function find_min(t)
{
	
	var result;
		
	
	if (t.left === null)
		result = t.value;
	else
		result = find_min(t.left);
		
	
	return result;
}

/**
	@id remove
		

*/
function remove(v, t)
{
	
	if (t === null)
		
		return null;

	
	if (v === t.value) {
		
		if (t.left === null) {	
				
				return t.right;
			}
		else 
		
		if (t.right === null) {
	  			return t.left;
			}
		else {
			var min = find_min(t.right);
			t.right = remove(min, t.right);
			t.value = min;
		}
	}
	else if (v < t.value)
		t.left = remove(v, t.left);
	else
		t.right = remove(v, t.right);	


  	return t;
}

var n1 = symb_number(n1);
var n2 = n1 - 1;
var n = make_node(n1); 

n = insert(n2,n);
var res = find_min(n); 
Assert(res = n2)
n = remove(n2,n);
var res2 = find_min(n);
Assert(res2 = n1)
