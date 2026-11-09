#!/bin/bash
# Build every Lean file under Examples/Quint (all their model checks run during the build).
cd "$(dirname "$0")/.."
mods=()
while IFS= read -r f; do mods+=("$(echo "${f%.lean}" | tr '/' '.')"); done < <(find Examples/Quint -name "*.lean" | sort)
lake build "${mods[@]}"
