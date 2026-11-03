#!/bin/bash
set -euo pipefail
LAB="$(cd "$(dirname "$0")" && pwd)"
PACKAGED_SVG="$LAB/Solving Showcase.svg"
if [ -f "$PACKAGED_SVG" ]; then
  echo "Solving static browser SVG scene: $PACKAGED_SVG"
  if ! open "$PACKAGED_SVG"; then
    echo 'Open this file in your browser:'
    echo "$PACKAGED_SVG"
  fi
  exit 0
fi
REPO="$(cd "$LAB/../../.." && pwd)"
PROJECT="$REPO/formal/lean4"
BUILD="$LAB/.build"
mkdir -p "$BUILD/olean"
LEAN_PATH="$BUILD/olean:$PROJECT/.lake/build/lib/lean"
export LEAN_PATH
cd "$PROJECT"

lean -R "$LAB" -o "$BUILD/olean/Graphics.olean" "$LAB/Graphics.lean"
lean -R "$LAB" -o "$BUILD/olean/Font.olean" "$LAB/Font.lean"
lean -R "$LAB" -o "$BUILD/olean/Geometry.olean" "$LAB/Geometry.lean"
lean -R "$LAB" -o "$BUILD/olean/SceneSVG.olean" "$LAB/SceneSVG.lean"
lean -R "$LAB" -o "$BUILD/olean/Solving.olean" "$LAB/Solving.lean"
lean -R "$LAB" -o "$BUILD/olean/SolvingPolicy.olean" "$LAB/SolvingPolicy.lean"
lean -R "$LAB" --run "$LAB/SolvingArtifact.lean" "$BUILD/Solving Showcase.svg"
echo "Solving SVG scene: $BUILD/Solving Showcase.svg"
if ! open "$BUILD/Solving Showcase.svg"; then
  echo 'The scene was generated. Open this file in your browser:'
  echo "$BUILD/Solving Showcase.svg"
fi
