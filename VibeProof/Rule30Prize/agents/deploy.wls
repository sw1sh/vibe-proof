#!/usr/bin/env wolframscript
(* ::Package:: *)

(* deploy.wls - deploy the Rule 30 Prize submissions under ROOT, as the account this kernel is
   connected to. Run it as the owner, for example:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute deploy.wls
       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute deploy.wls -root Rule30PrizeTest -instructions false

   With -instructions true (the default) it also publishes skill.md, the agents page and, once it
   has been built, notebooks/HowToStart.nb. *)

$here = DirectoryName[$InputFileName]

Get[FileNameJoin[{$here, "cloud", "Rule30PrizeSite.wl"}]]

args = Rest[$ScriptCommandLine]

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

root = option["root", "Rule30Prize"]

notebook = FileNameJoin[{$here, "notebooks", "HowToStart.nb"}]

Print["Deploying as ", $WolframID, " under ", root]

urls = Rule30PrizeDeploy[
    "Root" -> root,
    If[ option["instructions", "true"] === "true",
        Sequence @@ {
            "SkillFile" -> FileNameJoin[{$here, "skill.md"}],
            "AgentsPage" -> FileNameJoin[{$here, "site", "agents.html"}],
            "StartNotebook" -> If[FileExistsQ[notebook], notebook, None]
        },
        Sequence @@ {}
    ]
]

If[FailureQ[urls], Print[urls["Message"]]; Exit[1]]

KeyValueMap[Print[StringPadRight[#1, 18], #2]&, urls]
