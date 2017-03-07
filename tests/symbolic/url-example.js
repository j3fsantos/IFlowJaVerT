var base = "https://randombank.ru/api/service/account";

// read from DOM
var name = jsil_make_symbolic_string();

// check name non-empty
if (name.length > 0) {
    
    base += ("?name="+name);

    var account = jsil_make_symbolic_string();
    var useAcct = (account.length == 10 && account.startsWith("0123"));
    if (useAcct) {
	base += ("?acct="+account);
    }

    var id = jsil_make_symbolic_string();
    var useId = (id.length == 8 && id.startsWith("id"));
    if (useId) {
	base += ("?id"+id);
    }
}

base

jsil_assert(base.includes("?id"))

