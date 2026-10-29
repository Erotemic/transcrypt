<#
.SYNOPSIS
Install a transcrypt-v3 release binary on Windows (x86_64).

.DESCRIPTION
  powershell -ExecutionPolicy Bypass -File install.ps1 [-Tag v3-X.Y.Z] [-From DIR] [-Prefix DIR]

  -Tag TAG     the release to install (default: the newest v3-* release)
  -From DIR    install from archives built locally by scripts/build-release.sh
               (no network)
  -Prefix DIR  install into DIR\bin (default: %LOCALAPPDATA%\transcrypt-v3)

The archive is checked against the release's SHA256SUMS before anything is
installed. Checking it against the GitHub build attestation as well needs the
GitHub CLI: gh attestation verify ARCHIVE --repo Erotemic/transcrypt
transcrypt-v3 needs Git for Windows (2.34 or later), whose sh runs its hooks.
#>
param(
    [string]$Tag = "",
    [string]$From = "",
    [string]$Prefix = (Join-Path $env:LOCALAPPDATA "transcrypt-v3")
)
$ErrorActionPreference = "Stop"
$repo = "Erotemic/transcrypt"

function Fail($message) {
    Write-Error "install: $message"
    exit 1
}

if (-not [Environment]::Is64BitOperatingSystem -or $env:PROCESSOR_ARCHITECTURE -ne "AMD64") {
    Fail "release binaries exist for Windows x86_64 only so far; build from source: cd rust; cargo build --release"
}
if (-not (Get-Command git -ErrorAction SilentlyContinue)) { Fail "transcrypt-v3 needs Git for Windows (2.34 or later)" }

$work = Join-Path ([IO.Path]::GetTempPath()) ("transcrypt-v3-install-" + [Guid]::NewGuid())
New-Item -ItemType Directory -Path $work | Out-Null
try {
    if ($From) {
        Copy-Item (Join-Path $From "SHA256SUMS") (Join-Path $work "SHA256SUMS")
        $candidate = Get-ChildItem -Path $From -Filter "transcrypt-v3-*-x86_64-windows.zip" | Select-Object -Last 1
        if (-not $candidate) { Fail "no x86_64-windows archive in $From" }
        $archive = $candidate.Name
        Copy-Item $candidate.FullName (Join-Path $work $archive)
    } else {
        if (-not $Tag) {
            $releases = Invoke-RestMethod -UseBasicParsing "https://api.github.com/repos/$repo/releases"
            $Tag = ($releases | Where-Object { $_.tag_name -like "v3-*" } | Select-Object -First 1).tag_name
            if (-not $Tag) { Fail "no v3 release found; pass -Tag" }
        }
        $archive = "transcrypt-v3-$($Tag.Substring(3))-x86_64-windows.zip"
        $base = "https://github.com/$repo/releases/download/$Tag"
        Invoke-WebRequest -UseBasicParsing "$base/SHA256SUMS" -OutFile (Join-Path $work "SHA256SUMS")
        Invoke-WebRequest -UseBasicParsing "$base/$archive" -OutFile (Join-Path $work $archive)
    }

    $expected = Get-Content (Join-Path $work "SHA256SUMS") | ForEach-Object {
        $fields = $_ -split "\s+"
        if ($fields.Count -ge 2 -and $fields[1] -eq $archive) { $fields[0] }
    } | Select-Object -First 1
    if (-not $expected) { Fail "$archive is not listed in SHA256SUMS" }
    $actual = (Get-FileHash -Algorithm SHA256 (Join-Path $work $archive)).Hash.ToLower()
    if ($actual -ne $expected.ToLower()) { Fail "$archive does not match SHA256SUMS; nothing installed" }

    Expand-Archive -Path (Join-Path $work $archive) -DestinationPath $work
    $bin = Join-Path $Prefix "bin"
    New-Item -ItemType Directory -Force -Path $bin | Out-Null
    $name = [IO.Path]::GetFileNameWithoutExtension($archive)
    Copy-Item (Join-Path $work "$name\transcrypt-v3.exe") (Join-Path $bin "transcrypt-v3.exe.new") -Force
    Move-Item (Join-Path $bin "transcrypt-v3.exe.new") (Join-Path $bin "transcrypt-v3.exe") -Force
    & (Join-Path $bin "transcrypt-v3.exe") --version

    $userPath = [Environment]::GetEnvironmentVariable("Path", "User")
    if (-not (($userPath -split ";") -contains $bin)) {
        $joined = (@($userPath, $bin) | Where-Object { $_ }) -join ";"
        [Environment]::SetEnvironmentVariable("Path", $joined, "User")
        Write-Host "install: added $bin to your PATH (open a new terminal to use it)"
    }
} finally {
    Remove-Item -Recurse -Force $work
}
