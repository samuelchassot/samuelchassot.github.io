#!/usr/bin/env bash
# Regenerates the static parts of index.html (currently: the publication list
# from res/publications.bib). Run after editing the bib file.
set -euo pipefail
cd "$(dirname "$0")"
node scripts/build-publications.mjs
