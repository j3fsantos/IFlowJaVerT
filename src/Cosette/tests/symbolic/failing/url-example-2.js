var latitude = symb_string(latitude);

var url = 'https://api.instagram.com/v1/media/search?lat=%1&lng=%2&distance=%3?client_id=%4&access_token=%5'.replace('%1', latitude);

var res = url.includes("12345");
Assert((not res));
