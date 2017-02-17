var javert_output;
var jsil_output;
var global_examples;

window.onload = function () {

   id('show_verification_output').onclick = function () {
      id('tab_verification_output').className = id('show_verification_output').className = 'active';
      id('tab_verification_output').style.display = '';
      id('tab_jsil_output').className = id('show_jsil_output').className = '';
      id('tab_jsil_output').style.display = 'none';
      myAlert('Ready.');
   };

   id('show_jsil_output').onclick = function () {
      id('tab_jsil_output').className = id('show_jsil_output').className = 'active';
      id('tab_jsil_output').style.display = '';
      id('tab_verification_output').className = id('show_verification_output').className = '';
      id('tab_verification_output').style.display = 'none';
      myAlert('Ready.');
   };


    try {
        require(['custom/editor'], function (editor) {
            var queries, elements, code, i, iz, pair;

            window.editor = editor({ parent: 'editor', lang: 'js' });
            $('#ta_verification_output').val('');
            $('#ta_jsil_output').val('');
        });
    } catch (e) { }

    $('#btn-javert').click(function (evt) {
        var code = window.editor.getText();
        var data = {
            js_code: code
            //simp: id('simp').checked
        };
        alert ("Sending:\n" + code + "\n to the server!!!");
        $.ajax({
            type: 'POST',
            url: '/run-javert',
            data: data,
            success: javertResponse
        });
    });


    var javertResponse = function (data) {

      alert ('the response arrived: ' + data.javert_output);

      //myAlert('Program successfully compiled.', 'success');
      javert_output = data.javert_output;
      jsil_output = data.jsil_output;

      $(ta_verification_output).val(javert_output);
      $(ta_jsil_output).val(jsil_output)

    };


   $.ajax({
       type: 'POST',
       url: '/get-javert-examples',
       data: {},
       success: getJavertExamples
    });

    $('#select-example').change(function (evt) {
        var ex_name = $(this).find(':selected').text();
        var cur_code = global_examples[ex_name];
        window.editor.setText(cur_code);
    });
};



var getJavertExamples = function (data) {
   global_examples = data.examples;
   var select = id('select-example');
   select.options.length = 0;
   for (var ex_name in global_examples) {
      if (global_examples.hasOwnProperty(ex_name)) {
         select.options.add(new Option(ex_name));
     }
   }
   $(select).trigger('change');
}
