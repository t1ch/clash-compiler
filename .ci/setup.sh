#!/bin/bash
set -xou pipefail

grep -E ' $' -n -r . --include=*.{hs,hs-boot,sh} --exclude-dir=dist-newstyle
if [[ $? == 0 ]]; then
    echo "EOL whitespace detected. See ^"
    exit 1;
fi

set -e

# Check whether version numbers in
# clash-{prelude{,-hedgehog},lib{,-hedgehog},ghc,cores} are the same
cabal_files="clash-prelude/clash-prelude.cabal clash-prelude-hedgehog/clash-prelude-hedgehog.cabal clash-lib/clash-lib.cabal clash-lib-hedgehog/clash-lib-hedgehog.cabal clash-ghc/clash-ghc.cabal clash-cores/clash-cores.cabal"
versions=$(grep "^[vV]ersion" $cabal_files | grep -Eo '[0-9]+(\.[0-9]+)+')

if [[ $(echo $versions | tr ' ' '\n' | wc -l) == 6 ]]; then
    if [[ $(echo $versions | tr ' ' '\n' | uniq | wc -l) != 1 ]]; then
        echo "Expected all distributions to have the same version number. Found: $versions"
        exit 1;
    fi
else
    echo "Expected to find version number in all distributions. Found: $versions";
    exit 1;
fi

# You'd think comparing v${version} with ${CI_COMMIT_TAG} would do the
# trick, but no..
CI_COMMIT_TAG=${CI_COMMIT_TAG:-}
version=$(echo $versions | tr ' ' '\n' | head -n 1)
tag_version=${CI_COMMIT_TAG:1:${#CI_COMMIT_TAG}-1}  # Strip first character (v0.99 -> 0.99)

# `tag_version` is set when a tag has been created on GitHub. We use this to
# trigger a release pipeline (release to Hackage).
if [[ ${tag_version} != "" ]]; then

    if [[ ${version} != ${tag_version} ]]; then
        if [[ "${CI_COMMIT_TAG:0:1}" == "v" ]]; then
            echo "Tag name and distribution's release number should match:"
            echo "  Tag version:          ${CI_COMMIT_TAG}"
            echo "  Distribution version: v${version}"
            exit 1;
        else
            echo "\$CI_COMMIT_TAG should start with a 'v'. Found: ${CI_COMMIT_TAG}"
            exit 1;
        fi
    fi

    set +e
    grep "flag multiple-hidden" -A 7 clash-prelude/clash-prelude.cabal | grep -q "default: False"
    if [[ $? != 0 ]]; then
        echo "multiple_hidden flag should be disabled by default on releases!"
        exit 1;
    fi
    set -e
fi

# Print out versions for debugging purposes
cabal --version
ghc --version

# This might happen during tags on GitLab CI
CI_COMMIT_BRANCH=${CI_COMMIT_BRANCH:-no_branch_set_by_ci}

# Set MULTIPLE_HIDDEN on when not building a tag, unless it is already set.
if [[ $CI_COMMIT_TAG != "" ]]; then
  MULTIPLE_HIDDEN=${MULTIPLE_HIDDEN:-no}
else
  MULTIPLE_HIDDEN=${MULTIPLE_HIDDEN:-yes}
fi

# File may exist as part of a dist.tar.zst
if [ ! -f cabal.project.local ]; then
  cp .ci/cabal.project.local .

  if [[ "$MULTIPLE_HIDDEN" == "no" ]]; then
    sed -i 's/+multiple-hidden/-multiple-hidden/g' cabal.project.local
  fi

  set +u
  if [[ "$WORKAROUND_GHC_MMAP_CRASH" == "yes" ]]; then
    sed -i 's/-workaround-ghc-mmap-crash/+workaround-ghc-mmap-crash/g' cabal.project.local
  fi

  if [[ "$GHC_HEAD" == "yes" ]]; then
    cat .ci/cabal.project.local.append-HEAD >> cabal.project.local
  fi
  set -u

  # Fix index-state to prevent rebuilds if Hackage changes between build -> test.
  sed -i "s/HEAD/$(date -u +%FT%TZ)/g" cabal.project.local
fi

cat cabal.project.local

rm -f ${HOME}/.cabal/config
cabal user-config init
sed -i "s/-- ghc-options:/ghc-options: -j$THREADS/g" ${HOME}/.cabal/config
sed -i "s/^[- ]*jobs:.*/jobs: $CABAL_JOBS/g" ${HOME}/.cabal/config
sed -i "/remote-repo-cache:.*/d" ${HOME}/.cabal/config
cat ${HOME}/.cabal/config

set +u

# run v2-update first to generate the cabal config file that we can then modify
# retry 5 times, as hackage servers are not perfectly reliable
NEXT_WAIT_TIME=0
until cabal v2-update || [ $NEXT_WAIT_TIME -eq 5 ]; do
  sleep $(( NEXT_WAIT_TIME++ ))
done
