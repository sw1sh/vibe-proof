#!/usr/bin/env wolframscript
(* ::Package:: *)

(* deploy.wls - deploy the Rule 30 Prize submissions under ROOT, as the account this kernel is
   connected to. Run it as the owner, for example:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute deploy.wls
       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute deploy.wls -root Rule30PrizeTest -instructions false

   Options:
   - -instructions true (the default) also publishes the public pages: ROOT/ (the landing page,
     index.html), skill.md, HowToStart.nb (once notebooks/build.wls has built it) and the kit
     archive rule30prize-kit.tar.gz.
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

run[cmd_List] := Replace[RunProcess[cmd], {r_Association /; r["ExitCode"] === 0 :> r["StandardOutput"], r_ :> (Print["failed: ", StringRiffle[cmd, " "], "\n", r["StandardError"]]; Exit[1])}]

(* The kit archive: lean/, equivalents/ (without research notes), kit/ and the write-up, under
   rule30prize/, with a README and the commit they come from. Links to the write-up's old public
   address become links to the copy inside the archive, and no file names the old repository. *)
kitArchive[] := Block[{r30 = ExpandFileName[FileNameJoin[{$here, ".."}]], stage = CreateDirectory[], top, commit, archive},
    top = FileNameJoin[{stage, "rule30prize"}];
    CreateDirectory[top];
    Scan[run[{"rsync", "-a", "--exclude", ".lake", "--exclude", "research", "--exclude", ".DS_Store", FileNameJoin[{r30, #}] <> "/", FileNameJoin[{top, #}] <> "/"}]&, {"lean", "equivalents", "kit", "writeup"}];
    Scan[
        Function[file, Export[file, StringReplace[Import[file, "Text", CharacterEncoding -> "UTF-8"], {"https://sw1sh.github.io/vibe-proof/rule30-prize/" -> "../writeup/rule30-state.html", RegularExpression[" Our own repository, sw1sh/vibe-proof, [^.]*\\."] -> ""}], "Text", CharacterEncoding -> "UTF-8"]],
        Select[FileNames["*.md", top, Infinity], StringContainsQ[Import[#, "Text", CharacterEncoding -> "UTF-8"], "sw1sh"]&]
    ];
    commit = StringTrim @ run[{"git", "-C", r30, "rev-parse", "HEAD"}];
    Export[FileNameJoin[{top, "README.md"}], StringJoin[
        "# Rule 30 Prize kit\n\n",
        "The reference Lean environment for submissions to the Rule 30 Prize, with everything it builds on. ",
        "The instructions for agents are at " <> rootURL <> "/skill.md.\n\n",
        "- `kit/`: the Lake project you work in. Your proof goes in `Rule30Submission.lean`; `Check.lean` is the verifier's checker; `setup.sh` sets it up; `tests/` and `comparator/` show how proofs are checked.\n",
        "- `lean/`: the official statements `Problem1` and `Problem2`, and the catalog of proved partial results (namespace `Ruliology.CellularAutomata`).\n",
        "- `equivalents/`: 96 proved equivalent forms of Problem 1; `CATALOG.md` lists 53 forms and `TECHNIQUES.md` recent proof techniques.\n",
        "- `writeup/rule30-state.html`: the write-up of a 2026 attempt, with what is proved, what failed and why.\n\n",
        "Set up with [elan](https://github.com/leanprover/elan) installed: `sh kit/setup.sh`.\n\n",
        "Kit version 1, built from commit " <> commit <> ".\n"
    ], "Text", CharacterEncoding -> "UTF-8"];
    archive = FileNameJoin[{$TemporaryDirectory, "rule30prize-kit.tar.gz"}];
    run[{"tar", "-czf", archive, "-C", stage, "rule30prize"}];
    DeleteDirectory[stage, DeleteContents -> True];
    archive
]

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
    urls["rule30prize-kit.tar.gz"] = First @ CopyFile[kitArchive[], CloudObject[rootURL <> "/rule30prize-kit.tar.gz", Permissions -> "Public"], OverwriteTarget -> True];
    With[{nb = FileNameJoin[{$here, "notebooks", "HowToStart.nb"}]},
        If[FileExistsQ[nb], urls["HowToStart.nb"] = First @ CloudDeploy[publishedNotebook[nb], CloudObject[rootURL <> "/HowToStart.nb"], Permissions -> "Public"]]
    ];
    (* The landing page used to be ROOT/agents; it is ROOT/ now. *)
    Quiet @ DeleteObject[CloudObject[rootURL <> "/agents"]]
]

KeyValueMap[Print[StringPadRight[#1, 24], #2]&, urls]
