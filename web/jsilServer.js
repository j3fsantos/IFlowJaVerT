const http = require('http');
const express = require('express');
const fs = require('fs');
const bodyParser = require('body-parser');
const cookie_parser = require('cookie-parser');
const session = require('express-session');
const hbs= require('express-hbs');
const utils = require('./controllers/utils.js');
const js2jsil_module = require('./controllers/js2jsil.js');
const javert_module = require('./controllers/javert.js')


const js2jsil = js2jsil_module.js2jsil;
const javert = javert_module.javert;
const getJavertExamples = javert_module.getJavertExamples;
const createCFG = js2jsil_module.createCFG;

var js_verify_examples;

/*
  Setting up infrastructure
*/
const server = express();

server.set('port', 3000);

server.set('view engine', 'hbs');

server.engine('hbs', hbs.express4({
  defaultLayout: __dirname + '/views/layouts/main.hbs',
  partialsDir: __dirname + '/views/partials',
  layoutsDir: __dirname + '/views/layouts'
}));

/*
 Middleware
 */
server.use(express.static(__dirname + '/public'));

server.use(bodyParser.urlencoded({ extended: true }));

server.use(cookie_parser('nosecret'));

server.use(session({
    secret: 'keyboard cat',
    cookie: { maxAge: 60000 },
    resave: true,
    saveUninitialized: true }));

server.use('/run-js2jsil', bodyParser.json());

server.use('/run-javert', bodyParser.json());

server.use('/run-jsverify', bodyParser.json());

server.use('/createCFGImg', bodyParser.text());

server.use(function(req, res, next) {
	if (!req.session.myId) {
		req.session.myId = newSessionId();
	}
	next();
});

var newSessionId = (function () {
	var id = 0;
	return function () {
		return "-Id"+id++;
	}
})();

/*
 Routes
 */
server.get('/', function (req, res) {
	res.type('text/html');
	res.render('javert')
});

server.get('/index', function (req, res) {
	res.type('text/html');
	res.render('home')
});

server.get('/home', function (req, res) {
	res.type('text/html');
	res.render('home')
});

server.get('/js2jsil', function (req, res) {
	res.type('text/html');
	res.render('js2jsil')
});


server.get('/javert', function (req, res) {
	res.type('text/html');
	res.render('javert')
});


server.post('/run-js2jsil', function(req, res){
	var js_temp_file_name = 'test'+req.session.myId;

	console.log('Received request to run js2jsil');

	// Processing the request parameters
	const js_code = req.body.js_code;
	const specs = (req.body.specs === 'false' ? false : true);
	const ifs = (req.body.ifs === 'true' ? true : false);
	const simp = (req.body.simp === 'true' ? true : false);
	const smart_simp = (req.body.smart_simp === 'true' ? true : false);

    console.log('JS program to compile:');
    console.log(req.body.js_code);
    console.log('specs: ' + specs + '; ifs: ' + ifs + '; simp: ' + simp + '; smart_simp: ' + smart_simp);

    // create a .js file with the program that was received
    const input_path = __dirname + '/jsil_binaries/' + js_temp_file_name + '.js';
    fs.writeFile(input_path, js_code);

    js2jsil(req, res, js_temp_file_name, specs, ifs, simp, smart_simp);
});



server.post('/run-javert', function(req, res){
	var js_temp_file_name = 'test'+req.session.myId;

	console.log('Received request to run javert');

	// Processing the request parameters
	const js_code = req.body.js_code;

    console.log('JS program to compile:');
    console.log(req.body.js_code);

    // create a .js file with the program that was received
    const input_path = __dirname + '/jsil_binaries/' + js_temp_file_name + '.js';
    fs.writeFile(input_path, js_code);

    javert(req, res, js_temp_file_name);
});


server.post('/get-javert-examples', function(req, res) {
  try {
   getJavertExamples(req, res);
  } catch (e) {
    // this needs to be fixed - there may be clean up to do
    return;
  }
});


server.post('/createCFGImg', function(req, res) {
  try {
    var proc_name = req.query.proc;
    var cfg = req.body;
    createCFG(req, res, req.session.myId, proc_name, cfg)
  } catch (e) {
    // this needs to be fixed - there may be clean up to do
    return;
  }
});

server.use(function(req, res){
	res.type('text/plain');
	res.status(404);
	res.send('404 - Not Found');
});

server.use(function(err, req, res, next){
	console.error(err.stack);
	res.type('text/plain');
	res.status(500);
	res.send('500 - Server Error');
});

/*
 Setting up the Server
*/
server.listen(server.get('port'), function(){
	console.log('Express started on http://localhost:'+server.get('port')+'; press Ctrl-C to terminate.');
});
