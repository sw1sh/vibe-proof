#!/usr/bin/env wolframscript
(* ::Package:: *)

(* verify.wls - run the Rule 30 Prize verifier once, as the account that owns the submissions.

       wolframscript -f verify.wls                     check up to 5 queued submissions on Prime Intellect
       wolframscript -f verify.wls -n 20               more of them
       wolframscript -f verify.wls -method Local -kit ../../kit -store DIR
                                                       on this machine, against a local test store

   Options: -root (default Rule30Prize), -n, -image, -method (PrimeIntellect or Local), -kit,
   -store (a local directory instead of the cloud: for tests). The Prime Intellect method uses the
   prime CLI's API key (~/.prime/config.json); the cloud store needs this kernel to be
   connected to the Wolfram Cloud as the submissions' owner. -method Local runs submitted code on
   this machine: use it only for inputs you trust. *)

$here = DirectoryName[$InputFileName]

Get[FileNameJoin[{$here, "..", "cloud", "Rule30PrizeSite.wl"}]]

Get[FileNameJoin[{$here, "Rule30PrizeVerifier.wl"}]]

args = Rest[$ScriptCommandLine]

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

store = option["store", None]

attached = If[ StringQ[store],
    Rule30PrizeSite`$Rule30PrizeStore = ExpandFileName[store],
    Rule30PrizeAttach[option["root", "Rule30Prize"]]
]

If[ FailureQ[attached],
    Print[attached["Message"]];
    Exit[1]
]

results = Rule30PrizeVerify[
    "MaxItems" -> ToExpression[option["n", "5"]],
    "Method" -> option["method", "PrimeIntellect"],
    "Kit" -> Replace[option["kit", Automatic], k_String :> ExpandFileName[k]],
    "Image" -> option["image", $Rule30PrizeVerifierImage]
]

Scan[Print[#id, ": ", #verdict, If[ListQ[#reasons] && #reasons =!= {}, " (" <> StringRiffle[#reasons, "; "] <> ")", ""]]&, results]

Print[Length[results], " submission(s) checked"]
