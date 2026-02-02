$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot

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

$coqc = Resolve-Coqc
& $coqc -q .\\Moonwalk.v
