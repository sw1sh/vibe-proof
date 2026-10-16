#!/bin/sh
# Build the verifier image on Prime Intellect's builders and push it to the team registry:
#
#   sh agents/verifier/build_image.sh [tag]     (default tag: 1)
#
# The context is the kit (the submodule WolframInstitute/Rule30PrizeKit) without its .lake folders,
# plus the commit it is at. Sandboxes then use prime/team-<team id>/rule30-verifier:<tag>.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
kit=$(cd "$here/../../kit" && pwd)
tag=${1:-1}
ctx=$(mktemp -d)
trap 'rm -rf "$ctx"' EXIT
rsync -a --exclude .lake --exclude .git --exclude .DS_Store "$kit/" "$ctx/kit/"
git -C "$kit" rev-parse HEAD > "$ctx/commit"
cp "$here/Dockerfile" "$ctx/Dockerfile"
echo "context: $(du -sh "$ctx" | cut -f1), kit commit $(cat "$ctx/commit")"
PRIME_DISABLE_VERSION_CHECK=1 prime images push "rule30-verifier:$tag" --context "$ctx" --dockerfile "$ctx/Dockerfile" --plain
