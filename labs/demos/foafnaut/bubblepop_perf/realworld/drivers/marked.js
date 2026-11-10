// marked: render a generated Markdown document of N sections.
(function () {
  var marked = module.exports;
  if (N === 0) { console.log('RESULT 0'); return; }
  var parts = [];
  for (var i = 0; i < N; i++) {
    parts.push('## Section ' + i + '\n\nSome *emphasis*, some **strong text**, `code ' + i + '` and a [link ' + i +
      '](https://example.org/p/' + i + ').\n\n- item one ' + i + '\n- item two with `x' + i + '`\n- item three\n\n' +
      '| a | b |\n|---|---|\n| ' + i + ' | ' + (i * 3) + ' |\n\n> A quoted line ' + i + '.\n\n```\nvar v' + i + ' = ' + i + ';\n```\n\n');
  }
  var html = marked.parse(parts.join(''));
  var h = html.length;
  for (var j = 0; j < html.length; j += 3) h = mix(h, html.charCodeAt(j));
  console.log('RESULT ' + h);
})();
