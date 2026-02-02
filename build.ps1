# Build script for Moonwalk.v
$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot

# Resolve coqc location from env, PATH, or known installs.
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

# Compile the Coq file.
$coqc = Resolve-Coqc
& $coqc -q .\\Moonwalk.v
