const fs = require('fs');

function deleteFolderRecursive (path) {
	if( fs.existsSync(path) ) {
		fs.readdirSync(path).forEach(function(file,index){
			var curPath = path + '/' + file;
      if(fs.lstatSync(curPath).isDirectory()) {
        // recurse
        deleteFolderRecursive(curPath);
      } else {
        // delete file
        fs.unlinkSync(curPath);
      }
    });
    fs.rmdirSync(path);
  }
}

function loadExamples (path, filter) {
  var examples = {};
  var encoding = 'utf8';

  if (!filter) {
	  filter = function (x) { return true }
  }
  console.log('I am fetching your examples baby');
  console.log(path);

  if( fs.existsSync(path) ) {
	 console.log ('the path exists!!!');
    fs.readdirSync(path).forEach(function(file,index){
      var cur_path = path + '/' + file;
      console.log(cur_path);
      if ((!fs.lstatSync(cur_path).isDirectory()) && filter(cur_path)) {
        // read cont
        var cur_example = fs.readFileSync(cur_path, encoding);
        examples[file] = cur_example;
      }
    });
  }
  return examples;
}



module.exports = {
  deleteFolderRecursive: deleteFolderRecursive,
  loadExamples: loadExamples
};
