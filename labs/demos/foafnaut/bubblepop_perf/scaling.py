#!/usr/bin/env python3
"""Scaling of common operations: each runs at N and 4N; a ratio far above 4 is super-linear
cost. Usage: scaling.py ENGINE_CMD... (the script path is the last argument).
"""
import os, re, resource, subprocess, sys, tempfile

OPS = {
  "concat +=": "var s='';for(var i=0;i<N;i++)s+='x';print(s.length)",
  "concat number": "var s='';for(var i=0;i<N;i++)s+=i;print(s.length)",
  "charAt": "var s='ab'.repeat(N),t=0;for(var i=0;i<s.length;i++)if(s.charAt(i)=='a')t++;print(t)",
  "indexing s[i]": "var s='ab'.repeat(N),t=0;for(var i=0;i<s.length;i++)if(s[i]=='a')t++;print(t)",
  "split+join": "var a='a,b,c,'.repeat(N).split(',');print(a.join('-').length)",
  "indexOf": "var s='ab'.repeat(N),p=0,c=0;while((p=s.indexOf('b',p))>=0){c++;p++}print(c)",
  "replace global": "var s='ab '.repeat(N);print(s.replace(/a/g,'x').length)",
  "push": "var a=[];for(var i=0;i<N;i++)a.push(i);print(a.length)",
  "pop": "var a=[];for(var i=0;i<N;i++)a.push(i);while(a.length)a.pop();print(a.length)",
  "shift": "var a=[];for(var i=0;i<N;i++)a.push(i);var c=0;while(a.length&&c<N/8){a.shift();c++}print(c)",
  "a[len]=": "var a=[];for(var i=0;i<N;i++)a[a.length]=i;print(a.length)",
  "a[i]+=": "var a=[];for(var i=0;i<N;i++)a.push(i);for(var i=0;i<N;i++)a[i]+=1;print(a[0])",
  "map filter": "var a=[];for(var i=0;i<N;i++)a.push(i);print(a.map(function(x){return x+1}).filter(function(x){return x%2}).length)",
  "sort numbers": "var a=[];for(var i=0;i<N;i++)a.push((i*7919)%N);a.sort(function(x,y){return x-y});print(a[0])",
  "slice concat": "var a=[1,2,3];var t=0;for(var i=0;i<N;i++)t+=a.concat([i]).slice(1).length;print(t)",
  "spread": "var a=[];for(var i=0;i<N/8;i++){a=[...a.slice(-8),i]}print(a.length)",
  "keys new": "var o={};for(var i=0;i<N;i++)o['k'+i]=i;print(Object.keys(o).length)",
  "delete": "var o={};for(var i=0;i<N;i++)o['k'+i]=i;for(var i=0;i<N;i++)delete o['k'+i];print(Object.keys(o).length)",
  "for in": "var o={};for(var i=0;i<N;i++)o['k'+i]=i;var c=0;for(var k in o)c++;print(c)",
  "Map": "var m=new Map();for(var i=0;i<N;i++)m.set('k'+i,i);var t=0;for(var i=0;i<N;i++)t+=m.get('k'+i);print(t)",
  "Set of numbers": "var s=new Set();for(var i=0;i<N;i++)s.add(i);print(s.size)",
  "JSON roundtrip": "var a=[];for(var i=0;i<N;i++)a.push({i:i,s:'x'+i});print(JSON.parse(JSON.stringify(a)).length)",
  "closures": "var fs=[];for(var i=0;i<N;i++)fs.push(function(){return i});print(fs.length)",
  "classes": "class P{constructor(x){this.x=x}g(){return this.x}};var t=0;for(var i=0;i<N;i++)t+=new P(i).g();print(t)",
  "args array": "function f(){return arguments.length}var t=0;for(var i=0;i<N;i++)t+=f(1,2,3);print(t)",
  "template": "var t=0;for(var i=0;i<N;i++){t+=(`a${i}b`).length}print(t)",
  "typed array": "var a=new Float64Array(N);for(var i=0;i<N;i++)a[i]=i;var t=0;for(var i=0;i<N;i++)t+=a[i];print(t)",
  "try catch": "var c=0;for(var i=0;i<N;i++){try{if(i%3==0)throw i;}catch(e){c++}}print(c)",
}

def cpu(cmd, src):
    with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
        f.write("globalThis.print ??= (...a) => console.log(a.join(' '));\n" + src); path = f.name
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run(cmd + [path], capture_output=True, text=True, timeout=300)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    os.unlink(path)
    if p.returncode != 0: return None, p.stderr[:80]
    return (r1.ru_utime - r0.ru_utime + r1.ru_stime - r0.ru_stime) * 1000, ""

def main():
    n = int(os.environ.get("N", "40000"))
    cmd = sys.argv[1:]
    base = cpu(cmd, "print(1)")[0] or 0
    print(f"base {base:.0f} ms, N = {n}")
    for name, src in OPS.items():
        t1, e1 = cpu(cmd, re.sub(r"\bN\b", str(n), src))
        t4, e4 = cpu(cmd, re.sub(r"\bN\b", str(4 * n), src))
        if t1 is None or t4 is None:
            print(f"{name:18s} fail {e1 or e4}"); continue
        small = max(t1 - base, 0.5); large = max(t4 - base, 0.5)
        flag = " <-- super-linear" if large / small > 7 else ""
        print(f"{name:18s} {small:9.1f} {large:9.1f}  x{large / small:5.1f}{flag}")

main()
