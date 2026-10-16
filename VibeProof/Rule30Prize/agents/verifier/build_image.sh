#!/bin/sh
# Build the verifier image on Prime Intellect's builders and push it to the team registry:
#
#   sh agents/verifier/build_image.sh [tag]     (default tag: 1)
#
# The context is lean/, equivalents/ and kit/ without their .lake folders and research notes, plus
# the commit they come from. Sandboxes then use prime/team-<team id>/rule30-verifier:<tag>.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
r30=$(cd "$here/../.." && pwd)
tag=${1:-1}
ctx=$(mktemp -d)
trap 'rm -rf "$ctx"' EXIT
for d in lean equivalents kit; do
  rsync -a --exclude .lake --exclude research --exclude .DS_Store "$r30/$d/" "$ctx/$d/"
done
git -C "$r30" rev-parse HEAD > "$ctx/commit"
cp "$here/Dockerfile" "$ctx/Dockerfile"
echo "context: $(du -sh "$ctx" | cut -f1), commit $(cat "$ctx/commit")"
PRIME_DISABLE_VERSION_CHECK=1 prime images push "rule30-verifier:$tag" --context "$ctx" --dockerfile "$ctx/Dockerfile" --plain
