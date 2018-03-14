var url = "banana"; 
var id = jsil_make_symbolic_string(id);

// read from DOM
var name = jsil_make_symbolic_string(name);
var account = jsil_make_symbolic_string(account);

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
 
jsil_Assert( (!useAcct && !useId) && (url.includes("?id") || url.includes("?acct")));



