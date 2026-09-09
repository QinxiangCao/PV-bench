# Download the QCP binaries (symexec, StrategyCheck) into backend/binary/.
#
# The Windows counterpart of fetch-backend-binaries.sh. Same release, same
# archive, same destination; PowerShell so it needs no POSIX shell.
#
#   tools\fetch-backend-binaries.ps1                # the release named below
#   tools\fetch-backend-binaries.ps1 v2026.09.07    # a specific one
#
# Or fetch them yourself: unpack the archive so that backend\binary\ holds
# linux-binary\, mac-arm64-binary\, mac-x86-64-binary\ and win-binary\.

[CmdletBinding()]
param([string]$Tag)

$ErrorActionPreference = 'Stop'

$root = Split-Path -Parent $PSScriptRoot
$dest = Join-Path $root 'backend\binary'

# Which repo carries the release: read from origin, so a fork or a moved
# repo fetches its own binaries. Override with QCP_BINARY_REPO.
function Get-OriginRepo {
    $url = & git -C $root remote get-url origin 2>$null
    if ($LASTEXITCODE -ne 0 -or -not $url) { return $null }
    if ($url -notmatch 'github\.com[:/](.+?)(\.git)?$') { return $null }
    return $Matches[1]
}

$repo = if ($env:QCP_BINARY_REPO) { $env:QCP_BINARY_REPO } else { Get-OriginRepo }
if (-not $repo) {
    throw "cannot tell which repo holds the release: no github.com origin remote. Set QCP_BINARY_REPO=<owner>/<repo> and retry."
}
$tag   = if ($Tag) { $Tag } elseif ($env:QCP_BINARY_TAG) { $env:QCP_BINARY_TAG } else { 'backend-binaries' }
$asset = 'qcp-binaries.tar.gz'

# bsdtar ships with Windows 10 1803 and later; it reads .tar.gz.
if (-not (Get-Command tar -ErrorAction SilentlyContinue)) {
    throw 'tar is required (Windows 10 1803 and later ship it)'
}

$url = "https://github.com/$repo/releases/download/$tag/$asset"
$tmp = Join-Path ([System.IO.Path]::GetTempPath()) ([System.IO.Path]::GetRandomFileName())
New-Item -ItemType Directory -Path $tmp | Out-Null

try {
    $archive = Join-Path $tmp $asset
    Write-Host "fetching $url"
    try {
        Invoke-WebRequest -Uri $url -OutFile $archive -UseBasicParsing
    } catch {
        throw "download failed. check that the release '$tag' has a '$asset' asset."
    }

    New-Item -ItemType Directory -Force -Path $dest | Out-Null
    & tar -xzf $archive -C $dest --strip-components=1 2>$null
    if ($LASTEXITCODE -ne 0) { & tar -xzf $archive -C $dest }

    Write-Host 'installed:'
    Get-ChildItem -Path $dest -Directory | ForEach-Object { Write-Host "  $($_.Name)" }
} finally {
    Remove-Item -Recurse -Force $tmp -ErrorAction SilentlyContinue
}
