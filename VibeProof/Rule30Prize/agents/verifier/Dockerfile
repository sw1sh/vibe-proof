# The Rule 30 Prize verifier image: wolframinstitute/wolfram:15.0-lean (PrimeIntellect's
# Dockerfile.lean: Wolfram 15.0, Lean 4.30.0 in /opt/elan, LeanLink) with the Rule 30 Prize kit
# prebuilt. Rule30PrizeVerifier.wl starts Prime Intellect sandboxes from it: one builds a
# submission, a fresh one checks it. Everything a submission may import is built here, so a
# sandbox compiles without fetching anything: Mathlib, the Ruliology catalog, the equivalences,
# the kit.
#
# build_image.sh stages the context (the kit repository WolframInstitute/Rule30PrizeKit without
# .lake, and the commit it is at) and builds and pushes this image with `prime images push`, on
# Prime Intellect's builders.
FROM wolframinstitute/wolfram:15.0-lean

COPY kit /opt/rule30/kit
COPY commit /opt/rule30/commit

WORKDIR /opt/rule30/kit

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Prebuilt Mathlib, then the rest. The catalog builds one module at a time, in the order of
# lean/README.md: a cold parallel build of its certificate modules needs about 12.5 GB.
RUN lake exe cache get \
    && lake build Rule30PrizeKit Rule30Challenge Rule30Submission \
    && for m in Rule30Predecessors Rule30PredecessorCounts BusyBeaverLifetimes Rule30Blocks Rule30Jen \
        Rule30Prize Rule30Window Rule30MaskedJen Rule30Diagonals Rule30BlackRuns Rule30BlackRunBlocks \
        Rule30StripCertificates Rule30StripCertificateTable Rule30DrivenLeft Rule30RightPeriods \
        Rule30WhiteSeed Rule30Realization Rule30FactorWindow Rule30PeriodTwo Rule30ZeroBoundary \
        Rule30ZeroBoundaryStripe Rule30ZeroBoundarySmall Rule30ZeroBoundaryBarriers Rule30Ether \
        Rule30PeriodTwoCoupled Rule30PeriodFourSkeleton Rule30ZeroBoundaryLanes \
        Rule30Certificates.ZeroBoundaryWidth52Chunks{0,1,2,3} Rule30ZeroBoundaryWidth52 \
        Rule30ZeroBoundaryStripeFront Rule30Certificates.ZeroBoundaryStripeCycles{0,1,2} \
        Rule30ZeroBoundaryStripeFamily Rule30EtherTrap Rule30Certificates.EtherTrap{0,1,2,3,4,5} \
        Rule30EtherTrapWidth20 Rule30PeriodTwoLanguage Rule30PeriodTwoWidth5 Rule30PeriodTwoWidth6 \
        Rule30EtherThree Rule30EtherThreeNoWall Rule30EtherThreeTrap Rule30EtherThreeReach \
        Rule30EtherThreeLeft Rule30EtherThreeSkeleton; do \
         lake build "Ruliology.CellularAutomata.$m"; \
       done \
    && lake build Ruliology

# The sandboxes' environment. /work, where a submission lives, comes first on LEAN_PATH.
RUN printf 'export RULE30_KIT=%s\nexport LEAN_SYSROOT=%s\nexport RULE30_LEAN=%s\nexport LEAN_PATH=/work:%s\n' \
        "$PWD" "$(lake env printenv LEAN_SYSROOT)" "$(lake env printenv LEAN_SYSROOT)/bin/lean" "$(lake env printenv LEAN_PATH)" > /opt/rule30/env.sh \
    && chmod -R a+rX /opt/rule30

# Smoke check: the template passes. Then remove its build, so that only a submission's own
# compiled module can ever be found as Rule30Submission.
RUN . /opt/rule30/env.sh \
    && LEAN_PATH="$(lake env printenv LEAN_PATH)" "$RULE30_LEAN" --run Check.lean Rule30Submission \
        --claim partial --headline Rule30Submission.no_period_one \
    && rm -f .lake/build/lib/lean/Rule30Submission.* .lake/build/ir/Rule30Submission.*

WORKDIR /work
