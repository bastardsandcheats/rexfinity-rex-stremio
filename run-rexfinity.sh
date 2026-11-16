#!/usr/bin/env bash
set -euo pipefail
exec python3 /opt/rexfinity/rex-stremio/rex_stremio.py \
  --config /opt/rexfinity/state/stremio/config.json
