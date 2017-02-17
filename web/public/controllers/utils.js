function myAlert (msg, type) {
    var info = $('#info');
    info.text(msg);

    if (!type) type = 'secondary';
    switch(type) {
        case 'success':
            info.removeClass('secondary');
            info.removeClass('warning');
            info.addClass('success');
            break;
        case 'warning':
            info.removeClass('secondary');
            info.removeClass('success');
            info.addClass('warning');
            break;
        default:
            info.removeClass('success');
            info.removeClass('warning');
            info.addClass('secondary');
    }
}

function id(i) {
    return document.getElementById(i);
}

function clearChildren (node) {
    while (node.firstChild) {
        node.removeChild(node.firstChild);
    }
}
