#!/usr/bin/env wolframscript
(* build.wls ESSAY.md - builds ESSAY.nb beside it with MarkdownToNotebook, evaluating its cells, as an
   agent builds its essay. For the test submissions made with tests/submit.wls. *)

markdown = ExpandFileName[Last[$ScriptCommandLine]];

markdownToNotebook = ResourceFunction[ResourceObject["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Function/MarkdownToNotebook"]];

result = markdownToNotebook[Import[markdown, "Text", CharacterEncoding -> "UTF-8"], FileNameJoin[{DirectoryName[markdown], FileBaseName[markdown] <> ".nb"}]];

Print[If[StringQ[result] && FileExistsQ[result], "built " <> result, "the build failed"]];

Exit[If[StringQ[result] && FileExistsQ[result], 0, 1]];
