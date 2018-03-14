var latitude = jsil_make_symbolic_string();
var longitude = jsil_make_symbolic_string();
var distance = jsil_make_symbolic_string();

var url = 'https://api.instagram.com/v1/media/search?lat=%1&lng=%2&distance=%3?client_id=%4&access_token=%5'
    .replace('%1', latitude);

jsil_Assert( url.includes("12345") );
