export const fixtures=[
 {path:"sources/alice.xml",xml:'<records><person id="alice"><name>Alice</name><knows ref="bob"/></person></records>'},
 {path:"sources/bob.xml",xml:'<records><person id="bob"><name>Bob</name><knows ref="cara"/></person></records>'},
 {path:"sources/cara.xml",xml:'<records><person id="cara"><name>Cara</name><knows ref="alice"/></person></records>'}
];
