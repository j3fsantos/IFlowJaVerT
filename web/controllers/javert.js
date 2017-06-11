const utils = require('./utils.js');
const spawn = require('child_process').spawn;
const fs = require('fs');
const path = __dirname + '/../jsil_binaries/';
const javert_output_file_name = "javert_output.txt";
const javert_examples_path = "jsil_binaries/javert_examples";


function javert (req, res, js_temp_file_name) {
	var output_js2jsil;
	var output_jsilverify;

	console.log('Going to run javert on. Dirname: ' + __dirname + '\nPath: ' + path);

	try {
		output_js2jsil = spawn('./js2jsil.native',
			['-file', js_temp_file_name + '.js', '-logic'],
			{ cwd: __dirname + '/../jsil_binaries' });

	} catch (e) {
		// I need to deal with it
		console.log("Exception when running js2jsil")
		return;
	}

	output_js2jsil.on('exit', (output_status) => {
		try {
			console.log('I finished running js2jsil! I got the output status: ' + output_status);
			var javert_out = fs.openSync(path + javert_output_file_name, 'a');
			console.log('created the file for the standardoutput of jsilverify');
			console.log('Now going to run jsilverify on ' + js_temp_file_name + '.jsil\n');

			output_jsilverify = spawn('./jsilverify.native',
				['-file', js_temp_file_name + '.jsil', '-js'],
				{
					cwd:   __dirname + '/../jsil_binaries',
					stdio: ['ignore', javert_out, 'pipe']
				});


			output_jsilverify.on('exit', (output_status => {
				try {
					console.log('I finished running jsilverify! I got the output status: ' + output_status);
					var encoding = 'utf8';
					var jsil_output = fs.readFileSync(path + js_temp_file_name + '.jsil', encoding);
					var javert_output = fs.readFileSync(path + javert_output_file_name, encoding);
					console.log('I read the output files successfully:\n' + jsil_output + '\n' + javert_output + '\n');
					res.type('application/json');
					res.send({
						jsil_output: jsil_output,
						javert_output: javert_output
					});

                    fs.unlinkSync(path + js_temp_file_name + '.js');
					fs.unlinkSync(path + js_temp_file_name + '.jsil');
					fs.unlinkSync(path + javert_output_file_name);
				} catch (e) {
					console.log("Exception when processing the output of js2jsil and jsilverify:\n" + e)
				}
			}));

		} catch (e) {
			// I need to deal with it
			console.log("Exception when running jsilVerify")
			return;
		}
	});
}


function getJavertExamples (req, res) {
	console.log("Getting JaVerT examples.");
	var filter = function (name) {
		var last_dot_index = name.lastIndexOf(".");
		if (last_dot_index === -1) { return false }
		else {
			return (name.substring(last_dot_index+1) === "js")
		}
	};
	var examples = utils.loadExamples(javert_examples_path, filter);
	console.log ("here they are: " + examples);

	res.type('application/json');
	res.send({
		examples: examples
	});
}

module.exports = {
	javert: javert,
	getJavertExamples: getJavertExamples
};
