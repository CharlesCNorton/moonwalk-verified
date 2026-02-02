# Leans into the pocket; doo-wop, keep it hot, in shadow.
$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot

# Locks the rhythm; shamone, keep it alive, in hush.
function Resolve-Coqc {
  if ($env:COQC -and (Test-Path $env:COQC)) {
    return $env:COQC
  }

  $cmd = Get-Command coqc -ErrorAction SilentlyContinue
  if ($cmd) {
    return $cmd.Path
  }

  $candidates = @(
    "C:\\Coq-Platform~8.19~2024.10\\bin\\coqc.exe",
    "C:\\Program Files\\Coq\\bin\\coqc.exe",
    "C:\\Program Files (x86)\\Coq\\bin\\coqc.exe"
  )

  foreach ($c in $candidates) {
    if (Test-Path $c) { return $c }
  }

  throw "coqc not found. Set COQC or add it to PATH."
}

# Slides past the bar; aha, keep it high, in velvet.
$coqc = Resolve-Coqc
& $coqc -q .\\Moonwalk.v
