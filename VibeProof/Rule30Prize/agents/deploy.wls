#!/usr/bin/env wolframscript
(* ::Package:: *)

(* deploy.wls - deploy the Rule 30 Prize submissions under ROOT, as the account this kernel is
   connected to. Run it as the owner, for example:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute deploy.wls
       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute deploy.wls -root Rule30PrizeTest -instructions false

   Options:
   - -instructions true (the default) also publishes the public pages: ROOT/ (the landing page,
     index.html), skill.md and HowToStart.nb (once notebooks/build.wls has built it). They link
     the kit, the repository WolframInstitute/Rule30PrizeKit (the submodule ../kit).
   - -autoverify true (the default) makes the submission API start the verification of every new
     submission in the cloud. That needs the Prime Intellect key and paclet in the cloud: run
     verifier/store_prime_key.wls once. *)

$here = DirectoryName[$InputFileName]

Get[FileNameJoin[{$here, "cloud", "Rule30PrizeSite.wl"}]]

Get[FileNameJoin[{$here, "verifier", "Rule30PrizeVerifier.wl"}]]

args = $ScriptCommandLine

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

root = option["root", "Rule30Prize"]

rootURL = First @ CloudObject[root]

(* The notebook as a deployed notebook, without the essay template's docked toolbar. *)
publishedNotebook[file_String] := Replace[Import[file, "NB"], Notebook[cells_, opts___] :> Notebook[cells, DockedCells -> {}, Sequence @@ FilterRules[{opts}, Except[DockedCells]]]]

Print["Deploying as ", $WolframID, " under ", root]

If[ option["autoverify", "true"] === "true",
    Rule30PrizeVerifier`$Rule30PrizePrimeAccess = <|
        "Key" -> rootURL <> "/private/prime-key",
        "Paclet" -> rootURL <> "/private/PrimeIntellect.paclet",
        "TeamID" -> Lookup[Replace[Quiet @ Developer`ReadRawJSONFile[FileNameJoin[{$HomeDirectory, ".prime", "config.json"}]], Except[_Association] -> <||>], "team_id", Automatic]
    |>;
    Rule30PrizeSite`$Rule30PrizeOnSubmit = Function[id, CloudSubmit[Rule30PrizeVerifier`Rule30PrizeVerifyID[id]]]
]

urls = Rule30PrizeDeploy["Root" -> root, If[option["instructions", "true"] === "true", "SkillFile" -> FileNameJoin[{$here, "skill.md"}], Sequence @@ {}]]

If[FailureQ[urls], Print[urls["Message"]]; Exit[1]]

If[ option["instructions", "true"] === "true",
    urls["index.html"] = First @ CloudDeploy[
        HTTPResponse[StringToByteArray[StringReplace[Import[FileNameJoin[{$here, "site", "agents.html"}], "Text", CharacterEncoding -> "UTF-8"], "{{ROOT}}" -> rootURL], "UTF-8"], <|"ContentType" -> "text/html; charset=utf-8"|>],
        CloudObject[rootURL <> "/index.html"],
        Permissions -> "Public"
    ];
    With[{nb = FileNameJoin[{$here, "notebooks", "HowToStart.nb"}]},
        If[FileExistsQ[nb], urls["HowToStart.nb"] = First @ CloudDeploy[publishedNotebook[nb], CloudObject[rootURL <> "/HowToStart.nb"], Permissions -> "Public"]]
    ];
    (* Earlier deployments published ROOT/agents, now ROOT/, and the kit archive
       rule30prize-kit.tar.gz, now the kit repository. *)
    Quiet @ DeleteObject[CloudObject[rootURL <> "/agents"]];
    Quiet @ DeleteObject[CloudObject[rootURL <> "/rule30prize-kit.tar.gz"]]
]

KeyValueMap[Print[StringPadRight[#1, 24], #2]&, urls]
