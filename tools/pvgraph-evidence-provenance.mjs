import {execFileSync} from "node:child_process";
import {readFileSync,existsSync} from "node:fs";
import {createHash} from "node:crypto";
import {resolve} from "node:path";
import {fileURLToPath} from "node:url";

const root=fileURLToPath(new URL("../",import.meta.url));
const hash=path=>createHash("sha256").update(readFileSync(path)).digest("hex");
/** A HEAD alone never identifies uncommitted tests. Record every source delta
 * beside that HEAD, plus the actual Wasm bytes when an artifact is supplied. */
export function sourceProvenance(expectedHead,artifactPath=null,artifactKind="wasm"){
  const git=(...args)=>execFileSync("git",["-C",root,...args],{encoding:"utf8"});
  const head=git("rev-parse","HEAD").trim();
  if(head!==expectedHead)throw Error("requested evidence commit differs from the working HEAD");
  const changes=new Set([
    ...git("diff","--name-only","-z","HEAD").split("\0"),
    ...git("ls-files","--others","--exclude-standard","-z").split("\0")
  ].filter(Boolean));
  const changedSources=[...changes].sort().map(path=>({path,
    sha256:existsSync(resolve(root,path))?hash(resolve(root,path)):null}));
  return {head,workingTreeDirty:changedSources.length>0,changedSources,
    ...(artifactPath?{[artifactKind]:{path:artifactPath,sha256:hash(resolve(artifactPath))}}:{})};
}
