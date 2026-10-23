const patterns = ['a$', '^a', '^a$', 'a|b$', '^a|b$', '^$', 'a**', 'a++', 'a??', 'a{2,1}', 'a{1,2}', '[a-z]', '[a-\\d]', '[\\d-a]', '[a-\\w]', '[\\w-a]', '[a-\\s]', '[\\s-a]', '[[]', '[]]', '[^]', '[]', '[a[]', '[a[]].', '[^[]', '[\\D]', '[\\W]', '[\\S]', '\\v', '\\f', 'a{', 'a}', '{a}', '\\-', '\\/', 'a^b', 'a$b', '^^a', 'a$$', '(a*)a', '(a|ab)c', '[a--c]', '[a^]', '[^a]', '.', '^.$', '[.]', '\\.', '^\\s.$', '^\\S.$'];
const texts=['','a','b','aa','ab','abc','a\n','a\r','\na','\ra','\n','\r','\v','\f',' ',']','[','-','a-','1','_','Ω','\u2028','\u00a0','{a}','a{','a}'];
const cases=[]; for(const p of patterns){let r;try{r=new RegExp(p);}catch{continue;}for(const s of texts)cases.push([p,s,r.test(s)]);}
console.log(JSON.stringify(cases));
