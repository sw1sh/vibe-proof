#!/bin/sh
# Build the verifier image on Prime Intellect's builders and push it to the team registry:
#
#   sh agents/verifier/build_image.sh [tag]     (default tag: 1)
#
# The context is the kit's committed state (the submodule WolframInstitute/Rule30PrizeKit, through
# git archive, so work in progress in the checkout stays out), plus the commit it is at. Sandboxes
# then use prime/team-<team id>/rule30-verifier:<tag>.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
kit=$(cd "$here/../../kit" && pwd)
tag=${1:-1}
ctx=$(mktemp -d)
trap 'rm -rf "$ctx"' EXIT
mkdir -p "$ctx/kit"
git -C "$kit" archive HEAD | tar -x -C "$ctx/kit"
git -C "$kit" rev-parse HEAD > "$ctx/commit"
cp "$here/Dockerfile" "$ctx/Dockerfile"
echo "context: $(du -sh "$ctx" | cut -f1), kit commit $(cat "$ctx/commit")"
PRIME_DISABLE_VERSION_CHECK=1 prime images push "rule30-verifier:$tag" --context "$ctx" --dockerfile "$ctx/Dockerfile" --plain
