var url = symb_string();

// read from DOM
var name = symb_string(name);

// check name non-empty
if (name.length > 0) {
    
    url += ("?name="+name);

    var account = symb_string(account);
    var useAcct = (account.length == 10 && account.startsWith("0123"));
    if (useAcct) {
	url += ("?acct="+account);
    }

    var id = symb_string(id);
    var useId = (id.length == 8 && id.startsWith("id"));
    if (useId) {
	url += ("?id"+id);
    }
}

Assert( url.includes("access_token") );