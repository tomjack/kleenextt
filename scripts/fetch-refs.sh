#!/usr/bin/env bash
# Fetch reference material into refs/ (gitignored).
#   arxiv entries -> refs/tex/<slug>/   (extracted e-print source, usually .tex)
#   git entries   -> refs/repos/<slug>/ (shallow clone; <url>#<branch> for a branch)
#   pdf/url entries -> refs/misc/<slug>.<ext>
# Manifest: scripts/refs.tsv, tab-separated: <slug> <kind> <locator>
# Idempotent: existing targets are skipped. Re-fetch one by deleting its dir.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
manifest="$root/scripts/refs.tsv"
refs="$root/refs"
mkdir -p "$refs/tex" "$refs/repos" "$refs/misc"

fetch_arxiv() {
  local slug=$1 id=$2 dest="$refs/tex/$1"
  [[ -e $dest ]] && { echo "skip  $slug (exists)"; return; }
  echo "arxiv $slug ($id)"
  local tmp
  tmp=$(mktemp)
  curl -fsSL "https://arxiv.org/e-print/$id" -o "$tmp"
  mkdir -p "$dest"
  # e-print is a gzipped tarball, a gzipped single .tex, or (rarely) raw pdf
  case "$(file -b --mime-type "$tmp")" in
    application/gzip|application/x-gzip)
      if tar -tzf "$tmp" &>/dev/null; then
        tar -xzf "$tmp" -C "$dest"
      else
        gunzip -c "$tmp" > "$dest/$slug.tex"
      fi ;;
    application/x-tar) tar -xf "$tmp" -C "$dest" ;;
    application/pdf)   mv "$tmp" "$dest/$slug.pdf"; tmp= ;;
    *) echo "  !! unrecognized payload for $slug" >&2; rmdir "$dest"; return 1 ;;
  esac
  [[ -n $tmp ]] && rm -f "$tmp"
  sleep 3  # be polite to arxiv
}

fetch_git() {
  local slug=$1 url=$2 dest="$refs/repos/$1" branch=()
  [[ $url == *#* ]] && { branch=(--branch "${url##*#}"); url=${url%%#*}; }
  [[ -e $dest ]] && { echo "skip  $slug (exists)"; return; }
  echo "git   $slug ($url ${branch[1]:-})"
  git clone --depth 1 --quiet "${branch[@]}" "$url" "$dest"
}

fetch_url() {
  local slug=$1 url=$2 dest="$refs/misc/$1"
  compgen -G "$dest.*" >/dev/null && { echo "skip  $slug (exists)"; return; }
  echo "url   $slug ($url)"
  curl -fsSL "$url" -o "$dest.${url##*.}"
}

status=0
while IFS=$'\t' read -r slug kind locator; do
  [[ -z $slug || $slug == \#* ]] && continue
  case $kind in
    arxiv) fetch_arxiv "$slug" "$locator" || status=1 ;;
    git)   fetch_git   "$slug" "$locator" || status=1 ;;
    url)   fetch_url   "$slug" "$locator" || status=1 ;;
    *) echo "unknown kind '$kind' for $slug" >&2; status=1 ;;
  esac
done < "$manifest"
exit $status
