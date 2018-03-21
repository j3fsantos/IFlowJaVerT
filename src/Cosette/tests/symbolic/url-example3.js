var url = "banana"; 
var id = symb_string(id);

// read from DOM
var name = symb_string(name);
var account = symb_string(account);

//if (!url.includes("?")) { throw "bananas" } 

// check name non-empty
if ((name.length > 0) && (!name.includes("?"))) {  
    url += ("?name="+name);
}

// check valid account
var useAcct = (account.length == 10 && account.startsWith("0123"));
if (useAcct) {
    url += ("?acct="+account);
}

// check valid id 
var useId = (id.length == 8 && id.startsWith("id"));
if (useId) { url += ("?id"+id); }
 
Assert( (!useAcct && !useId) && (url.includes("?id") || url.includes("?acct")));



