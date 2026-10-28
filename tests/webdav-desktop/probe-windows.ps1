# Probe a lab served by serve-labs.mjs with the Windows WebDAV client (WebClient).
# https://github.com/danbri/factoidal/issues/1079 (checks with real file browsers)
#
#   powershell -ExecutionPolicy Bypass -File tests\webdav-desktop\probe-windows.ps1 -Origin http://127.0.0.1:8091/ [-Out DIR]
#
# Uses the WebDAV redirector (the WebClient service) that Windows Explorer
# uses, through the UNC path \\HOST@PORT\DavWWWRoot and a mapped drive.
# Microsoft lists WebClient as deprecated; it may be absent on new builds.
# Each check prints "ok", "FAIL" or "info" and the evidence; the script does
# not stop at a failed check. Output: OUT\probe-windows.md. Exit 0 when no
# check failed, 1 when one failed, 2 when the WebClient service is missing.
# Written for Windows PowerShell 5.1 and PowerShell 7.

param(
  [string]$Origin = 'http://127.0.0.1:8091/',
  [string]$Out = '.'
)

$ErrorActionPreference = 'Continue'
New-Item -ItemType Directory -Force -Path $Out | Out-Null
$Report = Join-Path $Out 'probe-windows.md'
Set-Content -Path $Report -Value '' -Encoding UTF8
$script:Pass = 0; $script:Fail = 0; $script:Info = 0
function Say([string]$s) { Write-Output $s; Add-Content -Path $Report -Value $s -Encoding UTF8 }
function Ok([string]$s) { $script:Pass++; Say "- ok    $s" }
function Bad([string]$s) { $script:Fail++; Say "- FAIL  $s" }
function Inf([string]$s) { $script:Info++; Say "- info  $s" }
function Evidence($lines) { Say '  ```'; foreach ($l in @($lines | Select-Object -First 40)) { Say "  $l" }; Say '  ```' }

$u = [Uri]$Origin
$Root = "\\$($u.Host)@$($u.Port)\DavWWWRoot"
$Work = Join-Path ([IO.Path]::GetTempPath()) ("factoidal-probe-" + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force -Path $Work | Out-Null

Say "# probe-windows: $((Get-Date).ToUniversalTime().ToString('yyyy-MM-ddTHH:mm:ssZ'))"
Say ''
Say "- origin: $Origin (UNC $Root)"
Say "- system: $([Environment]::OSVersion.VersionString); PowerShell $($PSVersionTable.PSVersion)"

# 1. The WebClient service and its limits.
$svc = Get-Service -Name WebClient -ErrorAction SilentlyContinue
if ($null -eq $svc) { Say ''; Bad 'the WebClient service is not installed (Settings > Optional features, or Server: Add-WindowsFeature WebDAV-Redirector)'; exit 2 }
Say "- WebClient: $($svc.Status), start type $($svc.StartType)"
if ($svc.Status -ne 'Running') {
  try { Start-Service WebClient -ErrorAction Stop; Inf 'started the WebClient service' } catch { Inf "could not start WebClient (needs an administrator): $($_.Exception.Message)" }
}
$p = Get-ItemProperty -Path 'HKLM:\SYSTEM\CurrentControlSet\Services\WebClient\Parameters' -ErrorAction SilentlyContinue
if ($p) {
  Say "- BasicAuthLevel: $($p.BasicAuthLevel) (0 none, 1 SSL only, 2 SSL and non-SSL)"
  Say "- FileSizeLimitInBytes: $($p.FileSizeLimitInBytes) (default 50000000)"
  Say "- FileAttributesLimitInBytes: $($p.FileAttributesLimitInBytes) (default 1000000; limits a PROPFIND response)"
}
Say ''

# 2. Reach the root by UNC, then map a drive.
if (Test-Path -LiteralPath $Root) { Ok "UNC $Root reachable" } else { Bad "UNC $Root not reachable" }
$net = & net use * $Origin /persistent:no 2>&1
$drive = ($net | Select-String -Pattern 'Drive ([A-Z]):' | ForEach-Object { $_.Matches[0].Groups[1].Value } | Select-Object -First 1)
if ($drive) { Ok "net use mapped drive ${drive}:" } else { Inf 'net use did not map a drive (the UNC path is used below)'; Evidence $net }
$R = if ($drive) { "${drive}:\" } else { $Root }

$rootNames = Get-ChildItem -LiteralPath $R -Name -ErrorAction SilentlyContinue
Ok "root lists $(@($rootNames).Count) folders: $($rootNames -join ' ')"

# 3. Names.
$names = Get-ChildItem -LiteralPath (Join-Path $R 'names') -Force -Name -ErrorAction SilentlyContinue
Inf "names\ lists $(@($names).Count) entries (seeded: 18 names + NAMES.txt + 2 folders = 21); Windows refuses ? * : < > | \ and CON in names"
Evidence $names
foreach ($n in @('with space.txt', "caf$([char]0xE9)-nfc.txt", 'hash#.txt', 'percent%25.txt', 'CON.txt', 'nul.txt', 'trailing-dot.')) {
  try { $c = Get-Content -LiteralPath (Join-Path (Join-Path $R 'names') $n) -Raw -ErrorAction Stop; Ok "read names\$n" } catch { Inf "cannot read names\$n : $($_.Exception.Message)" }
}
$cp = Get-ChildItem -LiteralPath (Join-Path $R 'names\case-pair') -Name -ErrorAction SilentlyContinue
Inf "case-pair\ (Readme.txt, README.txt): $(@($cp).Count) listed: $($cp -join ', ')"

# 4. Sizes: copy each to local disk and compare SHA-256 with SHA256SUMS.
$sumsPath = Join-Path $R 'sizes\SHA256SUMS'
$sums = Get-Content -LiteralPath $sumsPath -ErrorAction SilentlyContinue
foreach ($line in $sums) {
  $parts = $line -split '\s+'; $hex = $parts[0]; $name = $parts[1]
  $dst = Join-Path $Work $name
  $sw = [Diagnostics.Stopwatch]::StartNew()
  try {
    Copy-Item -LiteralPath (Join-Path $R "sizes\$name") -Destination $dst -ErrorAction Stop
    $h = (Get-FileHash -Algorithm SHA256 -LiteralPath $dst).Hash.ToLower()
    if ($h -eq $hex) { Ok "sizes\$name copied in $([math]::Round($sw.Elapsed.TotalSeconds,1)) s, SHA-256 matches" } else { Bad "sizes\$name SHA-256 differs" }
  } catch { if ($name -eq '51MB.bin') { Inf "sizes\$name not copied (expected when FileSizeLimitInBytes is 50000000): $($_.Exception.Message)" } else { Bad "copy sizes\$name : $($_.Exception.Message)" } }
}

# 5. Types and hidden files: attributes Windows gives each file.
Inf 'types\: name, length, attributes'
Evidence (Get-ChildItem -LiteralPath (Join-Path $R 'types') -Force | ForEach-Object { "$($_.Name)`t$($_.Length)`t$($_.Attributes)" })
Inf 'hidden\: name, attributes (does a dot file or desktop.ini get Hidden or System?)'
Evidence (Get-ChildItem -LiteralPath (Join-Path $R 'hidden') -Force | ForEach-Object { "$($_.Name)`t$($_.Attributes)" })

# 6. Writes.
$cfg = Join-Path $R 'config'
try { Set-Content -LiteralPath (Join-Path $cfg 'probe-windows.txt') -Value "probe-windows $(Get-Date -Format o)" -ErrorAction Stop; Ok 'create config\probe-windows.txt' } catch { Bad "create: $($_.Exception.Message)" }
$rs = Join-Path $cfg 'config\example-sparql\remote_sparql.txt'
try { Set-Content -LiteralPath $rs -Value 'https://dbpedia.org/sparql' -NoNewline -ErrorAction Stop; Ok 'overwrite remote_sparql.txt (Set-Content)' } catch { Bad "overwrite: $($_.Exception.Message)" }
if ((Get-Content -LiteralPath $rs -Raw) -eq 'https://dbpedia.org/sparql') { Ok 'overwritten content reads back' } else { Bad 'overwritten content does not read back' }
try { Rename-Item -LiteralPath (Join-Path $cfg 'probe-windows.txt') -NewName 'probe-windows-renamed.txt' -ErrorAction Stop; Ok 'rename' } catch { Bad "rename: $($_.Exception.Message)" }
try { New-Item -ItemType Directory -Path (Join-Path $cfg 'probe-windows-dir') -ErrorAction Stop | Out-Null; Ok 'mkdir' } catch { Bad "mkdir: $($_.Exception.Message)" }
try { Move-Item -LiteralPath (Join-Path $cfg 'probe-windows-renamed.txt') -Destination (Join-Path $cfg 'probe-windows-dir\') -ErrorAction Stop; Ok 'move into a folder' } catch { Bad "move: $($_.Exception.Message)" }
try { Remove-Item -LiteralPath (Join-Path $cfg 'probe-windows-dir') -Recurse -ErrorAction Stop; Ok 'delete a folder with a file in it' } catch { Bad "delete: $($_.Exception.Message)" }

# 7. Links, many, deep.
$url = Get-Content -LiteralPath (Join-Path $R 'links\open-dashboard.url') -ErrorAction SilentlyContinue
if ($url -match 'URL=http') { Ok 'open-dashboard.url reads' } else { Bad 'open-dashboard.url' }
$sw = [Diagnostics.Stopwatch]::StartNew(); $m = @(Get-ChildItem -LiteralPath (Join-Path $R 'many') -Name).Count
if ($m -eq 1000) { Ok "many\ lists 1000 files in $([math]::Round($sw.Elapsed.TotalSeconds,1)) s" } else { Bad "many\ lists $m files" }
$leaf = Join-Path $R ('deep\' + ((1..32 | ForEach-Object { 'level-{0:D2}' -f $_ }) -join '\') + '\leaf.txt')
Inf "deep leaf path length: $($leaf.Length) characters"
if (Test-Path -LiteralPath $leaf) { Ok 'deep leaf reachable' } else { Inf 'deep leaf not reachable (MAX_PATH 260 unless long paths are on)' }

# 8. Unmap.
if ($drive) { & net use "${drive}:" /delete /y | Out-Null; Ok "unmapped ${drive}:" }
Remove-Item -LiteralPath $Work -Recurse -Force -ErrorAction SilentlyContinue

Say ''
Say "probe-windows: $($script:Pass) ok, $($script:Fail) FAIL, $($script:Info) info (out of $($script:Pass + $script:Fail + $script:Info) lines)"
if ($script:Fail -eq 0) { exit 0 } else { exit 1 }
