const utils = require('./utils.js');
const spawn = require('child_process').spawn;
const fs = require('fs');

function jsilVerify (req, res, js_temp_file_name) {
	var output_ls;

	console.log('Going to run jsilverify');

	try {
		output_ls = spawn('./symb_execution_main.byte',
			['-file', js_temp_file_name + '.jsil'],
			{ cwd: __dirname + '/../jsil_binaries' });

	} catch (e) {
		// I need to deal with it
		console.log("Exception when running js2jsil - what just happened?")
		return;
	}

	output_ls.on('exit', (output_status) => {
		try {
			console.log('I finished running this!!! I got the output status: ' + output_status);
			var path = __dirname + '/../jsil_binaries/';
			var encoding = 'utf8';

			res.type('application/json');
			res.send({
				success: output_status
			});

			fs.unlinkSync(path + js_temp_file_name + '.jsil');
		} catch (e) {
			// I need to deal with it
			console.log("Exception when reading the files produced by symb_execution_main - this is just embarrassing" + e)
			return;
		}
	});
}


function js2jsil (req, res, js_temp_file_name) {
	var output_ls;

	console.log('Going to run js2jsil');

	try {
		output_ls = spawn('./js2jsil_main.native',
			['-file', js_temp_file_name + '.js', '-line_numbers', '-sep_procs'],
			{ cwd: __dirname + '/../jsil_binaries' });

	} catch (e) {
		// I need to deal with it
		console.log("Exception when running js2jsil - what just happened?")
		return;
	}

	output_ls.on('exit', (output_status) => {
		try {
			console.log('I finished running this!!!');
			var path = __dirname + '/../jsil_binaries/';
			var encoding = 'utf8';

			var output_folder = path + js_temp_file_name;
			var line_info_file_path = path + js_temp_file_name + '_line_numbers.txt';

			var line_info = fs.readFileSync(line_info_file_path, encoding);
			fs.unlinkSync(line_info_file_path);

			var procs = readJSILProcedures(output_folder);
			res.type('application/json');
			res.send({
				success: output_status,
				code: procs,
				line_info: line_info
			});

			cleanup(path + js_temp_file_name);
		} catch (e) {
			// I need to deal with it
			console.log("Exception when reading the files produced by js2jsil - this is just embarrassing" + e)
			return;
		}
	});
}

function readJSILProcedures (path) {
	var procedures_code = {};
	var encoding = 'utf8';
	fs.readdirSync(path).forEach(function(file,index){
		var cur_path = path+'/'+file;
		if(!fs.lstatSync(cur_path).isDirectory()) {
      			var compiled_code = fs.readFileSync(cur_path, encoding);
			var file_name_without_extension = file.substring(0, file.lastIndexOf("."));
      			procedures_code[file_name_without_extension] = compiled_code;
      		}
	});
	return procedures_code;
}



function cleanup (path) {
	console.log('unlinking ' + 1)
	utils.deleteFolderRecursive(path + '/');
	console.log('unlinking ' + 2)
	fs.unlinkSync(path + '.js');
	console.log('unlinking ' + 3)
	fs.unlinkSync(path + '_line_numbers.txt');
}



module.exports = {
	js2jsil: js2jsil,
	jsilVerify: jsilVerify
};
