var url = jsil_make_symbolic_string();

if (url != "") {
    if (url.substring(0,14) == '#access_token=') {
        url = "https://api.instagram.com/v1/users/self/?access_token="+url.substring(14, url.length);
    } 
}

jsil_assert( url.includes("access_token") );



