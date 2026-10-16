#!/usr/bin/env wolframscript
(* Builds HowToStart.nb from HowToStart.md, both beside this script, with every cell evaluated:
       wl -f build.wls [path/to/MarkdownToNotebook.wl] [--root=URL] *)

(* The essay's {{ROOT}} becomes the root, by default where the Rule 30 Prize is published, in
   memory only: the markdown keeps the placeholder. The converter is the published MarkdownToNotebook
   unless a local MarkdownToNotebook.wl is given. The cells find the kit through RULE30PRIZE_KIT,
   by default the kit of this checkout, and need LeanLink 1.0.14 or later. *)
$ProgressReporting = False;

dir = DirectoryName[$InputFileName];
args = Rest[$ScriptCommandLine];
root = Replace[
    FirstCase[args, s_String /; StringStartsQ[s, "--root="] :> StringDrop[s, StringLength["--root="]]],
    Missing[___] -> "https://www.wolframcloud.com/obj/wolframinstitute/Rule30Prize"
];
local = FirstCase[args, s_String /; StringEndsQ[s, ".wl"] :> ExpandFileName[s], None];

If[ ! StringQ[Environment["RULE30PRIZE_KIT"]],
    SetEnvironment["RULE30PRIZE_KIT" -> FileNameJoin[{ParentDirectory[dir, 2], "kit"}]]];
If[ ! DirectoryQ[Environment["RULE30PRIZE_KIT"]], Print["no kit at ", Environment["RULE30PRIZE_KIT"]]; Exit[1]];

(* LeanLink 1.0.14 adds "KernelCheck". It installs from its address until the repository's index lists it. *)
With[{leanlink = First[PacletFind["Wolfram/LeanLink"], None]},
    If[ leanlink === None || PacletNewerQ["1.0.14", leanlink["Version"]], PacletInstall["https://resources.wolframcloud.com/PacletRepository/pacletsitecontent/Paclets/Wolfram__LeanLink-1.0.14.paclet"]]];

markdownToNotebook = If[ local === None,
    ResourceFunction[ResourceObject["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"]],
    Get[local]; Symbol["MarkdownToNotebook"]
];

markdown = StringReplace[Import[FileNameJoin[{dir, "HowToStart.md"}], "Text", CharacterEncoding -> "UTF-8"], "{{ROOT}}" -> root];
result = markdownToNotebook[markdown, FileNameJoin[{dir, "HowToStart.nb"}]];
Print[If[StringQ[result] && FileExistsQ[result], "built " <> result, "the build failed"]];
Exit[If[StringQ[result] && FileExistsQ[result], 0, 1]];
