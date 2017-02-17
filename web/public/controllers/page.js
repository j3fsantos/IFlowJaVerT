

$(function(){

	// code mirror for input and output
	var cm_input, cm_output; 
	cm_input = CodeMirror.fromTextArea(document.getElementById('ta-input'), 
		{lineNumbers: true, mode: "javascript"});
	cm_output = CodeMirror.fromTextArea(document.getElementById('ta-output'), 
          {lineNumbers: true, mode: "javascript"});

	$('#btn-translate').click(function (evt) {
		var code = cm_input.getValue();
		$.ajax({
			type: 'POST',
			url: '/run-js2jsil', 
			data: {
				js_code: code
			},
			success: js2jsilResponse
		})
	});
    
    var cats_output = ['functions', 'builtins', 'specs'];
	var output_code; 

	$('#select-proc-type').change(function (evt) {
		$('#select-proc')[0].length = 0; 
		populateSelectOutputCode(); 
		$('#select-proc').trigger('change');
	});

 	$('#select-proc').change(function (evt) { 
 		 var cur_cat = $('#select-proc-type :selected').text(); 
		 var proc_name = $(this).find(':selected').text();
		 var cur_code = output_code[cur_cat][proc_name]; 
		 cm_output.setValue(cur_code);
	});

	var populateSelectOutputCode = function () {
		var cur_cat =  $('#select-proc-type :selected').val();
		var select = document.getElementById('select-proc');
		var procs = output_code[cats_output[cur_cat]];

		for (var proc_name in procs) {
			if (procs.hasOwnProperty(proc_name)) {
				select.options.add(new Option(proc_name));
			}
		}	
	}

	var populateSelectOutputCat = function () {
		var select = document.getElementById('select-proc-type');

		for (var i=0, len = cats_output.length; i < len; i++) {
      		select.options.add(new Option(cats_output[i], i));
   		}
	}
	populateSelectOutputCat(); 

	var js2jsilResponse = function (data) {
		alert('your resquest has been processed!'); 
		alert('the response was: success = ' + data.success); 

		output_code = data.code; 
		cm_output.setValue(data.code.functions['main.pulp']);
		populateSelectOutputCode(); 
	};
}); 
