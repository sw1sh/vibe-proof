#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Run the submission and verifier tests against a local store and the local kit (build the kit
   first: kit/setup.sh). Exits 1 if any test fails.

       wolframscript -f run.wls *)

$testDirectory = DirectoryName[$InputFileName]

Get[FileNameJoin[{$testDirectory, "..", "cloud", "Rule30PrizeSite.wl"}]]

Get[FileNameJoin[{$testDirectory, "..", "verifier", "Rule30PrizeVerifier.wl"}]]

{seconds, report} = AbsoluteTiming @ TestReport[FileNameJoin[{$testDirectory, "Rule30Prize.wlt"}]]

Scan[
    Print["FAIL ", #["TestID"], "\n  expected: ", InputForm[#["ExpectedOutput"]], "\n  actual:   ", InputForm[#["ActualOutput"]]]&,
    Join[Values[report["TestsFailedWrongResults"]], Values[report["TestsFailedWithMessages"]], Values[report["TestsFailedWithErrors"]]]
]

Print[report["TestsSucceededCount"], " passed, ", report["TestsFailedCount"], " failed, ", Round[seconds], " s"]

Exit[If[report["AllTestsSucceeded"], 0, 1]]
