#!/bin/sh
# Build, then check the quick examples; Bench*, Hope and Pi4S3 are slow.
set -e
cd "$(dirname "$0")/.."
lake build
exec .lake/build/bin/kleenextt check \
  examples/ElabZoo.ktt examples/Prelude.ktt examples/Cubical.ktt \
  examples/Brunerie.ktt examples/HLevel.ktt examples/S1Mod2.ktt \
  examples/Tubes.ktt examples/LocalGlobal.ktt examples/S2Mod2.ktt \
  examples/J2S2.ktt
