/*
 * @id  Test
 * @rec false
 */
function Test (data) {
	this.data = data;
}

Test.prototype = {
	/*
	 * @id  getData
	 * @rec false
	 */
	getData : function () {
		return this.data;
	}
}

var t = new Test(5);

t.getData();