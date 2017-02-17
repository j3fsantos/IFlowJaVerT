var line_info;
var output_code;
var output_code_lines;

window.onload = function () {

    id('show_syntax').onclick = function () {
        id('tab_syntax').className = id('show_syntax').className = 'active';
        id('tab_syntax').style.display = '';
        myAlert('Ready.');
    };


    try {
        require(['custom/editor'], function (editor) {
            var queries, elements, code, i, iz, pair;

            window.editor = editor({ parent: 'editor', lang: 'js' });
            $('#syntax').val('');
        });
    } catch (e) { }

    $('#btn-translate').click(function (evt) {
        var code = window.editor.getText();
        var data = {
            js_code: code
            //simp: id('simp').checked
        };
        $.ajax({
            type: 'POST',
            url: '/run-js2jsil',
            data: data,
            success: js2jsilResponse
        });
    });


    var js2jsilResponse = function (data) {

        myAlert('Program successfully compiled.', 'success');
        //alert ('the response arrived: ' + data.code);
        //alert ('line info: ' + data.line_info);
        output_code = data.code;
        output_code_lines = {};

        for (var proc in output_code) {
                if (output_code.hasOwnProperty(proc)) {
                        output_code_lines[proc] = strToLines(output_code[proc]);
                }
        }
        var ret = parseLineNumbers(data.line_info);
        line_info = ret.parsed_info;
        line_info_proc = ret.parsed_info_proc;
        //$('#syntax').val(data.code);
        populateSelectOutputCode();
    };



     $('#js_lines_show').click(function (evt) {
        var js_init_line, js_final_line;
        var code_to_show, code_to_show_by_lines;

        //alert("About to show some lines of interest!")

        if (!output_code) {
            myAlert('Nothing to show.', 'warning');
            return;
        }

        js_init_line = parseInt($('#js_init_line').val());
        js_final_line = parseInt($('#js_final_line').val());

        if ((js_final_line > output_code_lines.length + 1) || js_final_line < 1) {
             myAlert('Illegal value specified for final line.', 'warning');
             return;
        }

        if ((js_init_line > output_code_lines.length + 1) || js_init_line < 1) {
             myAlert('Illegal value specified for initial line.', 'warning');
             return;
        }

        if (js_init_line > js_final_line) {
             myAlert('The initial line cannot be greater than the final line.', 'warning');
             return;
        }

        var cur_proc = $('#select-proc :selected').text();
        var line_proc = line_info_proc[js_init_line];
        lines_to_print = getLines(line_proc, js_init_line, js_final_line);
        //alert ("js_init: " + js_init_line + " js_final: " + js_final_line + " number_of_jsil_lines: " + lines_to_print.length);
        code_to_show_by_lines = filter_lines(output_code_lines[line_proc], lines_to_print);
        code_to_show = linesToStr(code_to_show_by_lines);

        $('#select-proc option:contains(' + line_proc + ')')[0].selected = true;
        $('#syntax').val(code_to_show);
    });

    $('#js_lines_reset').click(function (evt) {
        $('#select-proc').trigger('change');
    });


    var populateSelectOutputCode = function () {
        var select = document.getElementById('select-proc');

        select.options.length = 0;
        for (var proc_name in output_code) {
            if (output_code.hasOwnProperty(proc_name)) {
                select.options.add(new Option(proc_name));
            }
        }
        $('#select-proc').trigger('change');
    }

    $('#select-proc').change(function (evt) {
         var proc_name = $(this).find(':selected').text();
         var cur_code = output_code[proc_name];
         $('#syntax').val(cur_code);
    });
};



function parseLineNumbers (str) {
    var parsed_info, parsed_info_proc, cur_proc;

    function parseLine (offset) {
        if (offset >= str.length) return;

        if (str.substring(offset, offset+4) === 'Proc') {
            parseProcLine(offset);
        } else if (str[offset] === '(') {
            parseOffsetLine(offset);
        } else {
            throw new Error('Invalid syntax in line info');
        }
    }

    function parseProcLine (offset) {
        var index = offset + 6;
        var proc_name;

        while (str[index] !== '\n') {
            index++;
        }

        proc_name = str.substring(offset + 6, index);
        parsed_info[proc_name] = [];
        cur_proc = proc_name;
        parseLine(index + 1);
    }

    function parseOffsetLine (offset) {
        var index, comma_index, last_parenthesis_index;
        var jsil_offset, js_offset;

        index = offset + 1;
        while (str[index] !== ',') {
            index++;
        }
        comma_index = index;

        while (str[index] !== ')') {
            index++;
        }
        last_parenthesis_index = index;

        jsil_offset = parseInt(str.substring(offset + 1, comma_index));
        js_offset = parseInt(str.substring(comma_index + 1, last_parenthesis_index));

        //alert("Parsing a offset mapping: " + jsil_offset + ", " + js_offset);

        parsed_info_proc[js_offset] = cur_proc;
        if (!parsed_info[cur_proc][js_offset]) {
                parsed_info[cur_proc][js_offset] = [ jsil_offset ]
        } else {
                parsed_info[cur_proc][js_offset].push(jsil_offset)
        }
        parseLine(index + 2);
    }

    parsed_info = {};
    parsed_info_proc = [];
    parseLine(0);
    var ret = {
            parsed_info: parsed_info,
            parsed_info_proc: parsed_info_proc
    };
    return ret;
}


function getLines (proc, js_start, js_finish) {
    if (!(line_info[proc] instanceof Array)) {
         myAlert('The lines you asked to see do not have a JSIL counterpart.', 'warning');
    }
    var code_lines_to_show = [];
    for (var i=js_start; i<=js_finish; i++) {
        code_lines_to_show = code_lines_to_show.concat(line_info[proc][i])
    }
    //alert ("getLines: " + code_lines_to_show.length)
    return code_lines_to_show
}

function strToLines (str) {
    var str_arr = [];
    var index;
    var original_str = str;

    while ((index = str.indexOf('\n')) !== -1) {
        cur_str = str.substring(0, index + 1);
        str_arr.push(cur_str);
        str = str.substring(index+1);
    }
    return str_arr;
}

function linesToStr (str_arr) {
    var str = '';
    for (var i = 0, len = str_arr.length; i < len; i++) {
        str += str_arr[i];
    }
    return str;
}

function filter_lines (lines, line_numbers_to_show) {
    var lines_to_show = [];
    for (var i = 0, len = line_numbers_to_show.length; i < len; i++) {
        var index = line_numbers_to_show[i];
        lines_to_show.push(lines[index+1]);
    }
    return lines_to_show;
}
