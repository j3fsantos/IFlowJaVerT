var url = jsil_make_symbolic_string();

// read from DOM
var name = jsil_make_symbolic_string(name);

// check name non-empty
if (name.length > 0) {
    
    url += ("?name="+name);

    var account = jsil_make_symbolic_string(account);
    var useAcct = (account.length == 10 && account.startsWith("0123"));
    if (useAcct) {
	url += ("?acct="+account);
    }

    var id = jsil_make_symbolic_string(id);
    var useId = (id.length == 8 && id.startsWith("id"));
    if (useId) {
	url += ("?id"+id);
    }
}

jsil_assert( url.includes("access_token") );