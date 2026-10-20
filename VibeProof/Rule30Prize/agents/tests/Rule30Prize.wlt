(* Tests for the submissions (Rule30PrizeSite.wl) and the verifier (Rule30PrizeVerifier.wl), against
   a local store and the local kit. Run with: wolframscript -f run.wls *)

kit = FileNameJoin[{$testDirectory, "..", "..", "kit"}]

(* Sources that import only the statements module, not Rule30PrizeKit and Mathlib, so that each
   local evaluation and build takes seconds. The first has Unicode, quotes and a backslash, which
   must come back from the notebook unchanged. *)
template = StringJoin[
    "import Ruliology.CellularAutomata.Rule30Prize\n\n/-! Unicode: \[ForAll] \[Not] \[RightArrow] \:21a6 \:2115 \:27e8\:27e9 \[Lambda], and \"quotes\" and a back\\slash. -/\n\n",
    "namespace Rule30Submission\n\nopen Ruliology.CellularAutomata.Rule30Prize\n\n",
    "theorem no_period_one : \[Not] \[Exists] N, \[ForAll] t, N \[LessEqual] t \[RightArrow] center (t + 1) = center t :=\n  center_not_eventually_period_one\n\n",
    "end Rule30Submission\n"
]

sorrySource = "import Ruliology.CellularAutomata.Rule30Prize\nnamespace Rule30Submission\nopen Ruliology.CellularAutomata.Rule30Prize\ntheorem problem1 : Problem1 := by sorry\nend Rule30Submission\n"

(* An essay, as the front end writes it: a setup cell, then rule30Submission = LeanImportString[src, ...]. *)
submissionNotebook[src_String, extra_List : {}] := Block[{file = FileNameJoin[{$TemporaryDirectory, CreateUUID[] <> ".nb"}]},
    Export[file, Notebook[Join[
        {Cell["An essay", "Title"], Cell["The proof:", "Text"]},
        {Cell[BoxData[MakeBoxes[Needs["Wolfram`LeanLink`"]; $Rule30PrizeKit = Environment["RULE30PRIZE_KIT"], StandardForm]], "Input"]},
        {With[{s = src}, Cell[BoxData[MakeBoxes[rule30Submission = LeanImportString[s, "ProjectDir" -> $Rule30PrizeKit], StandardForm]], "Input"]]},
        extra
    ]], "NB"];
    file
]

rawFile[text_String] := Block[{file = FileNameJoin[{$TemporaryDirectory, CreateUUID[] <> ".nb"}]},
    Export[file, text, "Text"];
    file
]

(* Requests as the deployed API sees them: signed in with a Wolfram ID. *)
agentID = "agent@example.org"

submit[args___] := Block[{$RequesterWolframID = agentID}, Rule30PrizeSubmit[args]]

statusAs[who_, args___] := Block[{$RequesterWolframID = who}, Rule30PrizeStatus[args]]

fields[nb_, rest___Rule] := Join[
    <|"notebook" -> nb, "problem" -> 1, "claim" -> "partial", "title" -> "Period one", "authors" -> "A. Person; Claude",
      "agent" -> "Claude Code with Claude Opus 5.5", "headlines" -> "Rule30Submission.no_period_one", "consent" -> True|>,
    <|rest|>
]

(* === submitting === *)

Rule30PrizeSite`$Rule30PrizeStore = CreateDirectory[]

good = submit[fields[submissionNotebook[template]]]

VerificationTest[{good["ok"], good["status"], good["check"]["state"], good["target"], good["submitter"], KeyExistsQ[good, "token"]}, {True, "Lean Unverified", "queued", Null, agentID, False}, TestID -> "submit-partial"]

VerificationTest[Rule30PrizeSubmit[fields[submissionNotebook[template]]][[1]], "WolframID", TestID -> "submit-needs-a-wolfram-id"]

VerificationTest[
    submit[fields[submissionNotebook[template], "consent" -> False]][[1]],
    "Consent",
    TestID -> "submit-needs-consent"
]

VerificationTest[
    submit[fields[submissionNotebook[template], "agent" -> ""]][[1]],
    "Agent",
    TestID -> "submit-needs-agent"
]

VerificationTest[
    submit[fields[submissionNotebook[template], "headlines" -> "rm -rf /"]][[1]],
    "Headlines",
    TestID -> "submit-checks-headlines"
]

VerificationTest[
    submit[fields[submissionNotebook[template], "problem" -> "4"]][[1]],
    "Problem",
    TestID -> "submit-checks-problem"
]

bad = submit[fields[submissionNotebook[sorrySource], "claim" -> "proof", "headlines" -> None, "title" -> "</script><script>alert(1)</script>"]]

VerificationTest[{bad["ok"], bad["target"]}, {True, "Rule30Submission.problem1"}, TestID -> "submit-proof-claim"]

VerificationTest[submit[fields[rawFile["this is not a notebook {"]]][[1]], "NotNotebook", TestID -> "submit-needs-a-notebook"]

(* The site reads no source: a notebook of prose waits for the verifier like any other. *)
nosrc = submit[fields[rawFile["Notebook[{Cell[\"prose only\", \"Text\"]}]"], "title" -> "No Lean"]]

VerificationTest[nosrc["check"]["state"], "queued", TestID -> "submit-without-source"]

(* Three submissions so far from this requester; with a limit of three an hour, the next is refused. *)
VerificationTest[
    Block[{Rule30PrizeSite`Private`$rateLimits = {{3600, 3}}}, submit[fields[submissionNotebook[template]]][[1]]],
    "RateLimit",
    TestID -> "submit-rate-limit"
]

VerificationTest[
    Sort[#id& /@ Rule30PrizeQueue[10]],
    Sort[{good["id"], bad["id"], nosrc["id"]}],
    TestID -> "queue-holds-notebooks"
]

(* The deployed API starts each new verification through this hook. *)
VerificationTest[
    Block[{Rule30PrizeSite`$Rule30PrizeOnSubmit = Function[id, hooked = id], hooked = None},
        hookedSubmission = submit[fields[submissionNotebook[template], "title" -> "Hooked"]];
        {hooked === hookedSubmission["id"], hookedSubmission["check"]["state"]}
    ],
    {True, "queued"},
    TestID -> "submit-starts-verification"
]

VerificationTest[
    {Rule30PrizeClaimCheck[hookedSubmission["id"]], Rule30PrizeClaimCheck[hookedSubmission["id"]], MissingQ[Rule30PrizeQueueItem[hookedSubmission["id"]]], Rule30PrizeEntry[hookedSubmission["id"]]["check"]["state"]},
    {True, False, True, "running"},
    TestID -> "claim-once"
]

(* A run that stopped answering long ago gives its submission back to the queue. *)
VerificationTest[
    Block[{Rule30PrizeSite`Private`$staleRunSeconds = -1}, Rule30PrizeQueueItem[hookedSubmission["id"]]["id"]],
    hookedSubmission["id"],
    TestID -> "stale-claim-requeued"
]

VerificationTest[Rule30PrizeHide[hookedSubmission["id"], "test"]; Rule30PrizeQueueItem[hookedSubmission["id"]], Missing["NotWaiting", hookedSubmission["id"]], TestID -> "hidden-not-queued"]

VerificationTest[
    Hash[BaseDecode[First[Select[Rule30PrizeQueue[10], #id === good["id"]&]]["notebookBase64"]], "SHA256", "HexString"] === Rule30PrizeEntry[good["id"]]["notebookSHA256"],
    True,
    TestID -> "queue-notebook-bytes"
]

(* === verifying, on this machine === *)

(* An agent's fake proof of Problem 1: it does not import the kit and declares a Problem1 of its own
   (the kit's tests/T07Redefine.lean). *)
redefined = Block[{Rule30PrizeSite`Private`$rateLimits = {}},
    submit[fields[submissionNotebook[Import[FileNameJoin[{kit, "tests", "T07Redefine.lean"}], "Text", CharacterEncoding -> "UTF-8"]], "claim" -> "proof", "headlines" -> None]]
]

verified = Rule30PrizeVerify["Method" -> "Local", "Kit" -> kit]

VerificationTest[
    Sort[{#id, #verdict}& /@ verified],
    Sort[{{good["id"], "pass"}, {bad["id"], "fail"}, {nosrc["id"], "fail"}, {redefined["id"], "fail"}}],
    TestID -> "verify-local"
]

(* The source behind rule30Submission comes back from the evaluation, byte for byte, for reviewers. *)
VerificationTest[
    {Rule30PrizeEntry[good["id"]]["sourceSHA256"] === Hash[StringToByteArray[template, "UTF-8"], "SHA256", "HexString"], StringQ[Rule30PrizeEntry[good["id"]]["files"]["lean"]]},
    {True, True},
    TestID -> "verify-stores-source"
]

VerificationTest[Rule30PrizeEntry[nosrc["id"]]["check"]["reasons"], {"The notebook does not set rule30Submission."}, TestID -> "verify-explains-missing-source"]

VerificationTest[
    {Rule30PrizeEntry[redefined["id"]]["status"], Rule30PrizeEntry[redefined["id"]]["check"]["reasons"]},
    {"Lean Unverified", {"the module does not import Ruliology.CellularAutomata.Rule30Prize, the official statements: import Rule30PrizeKit"}},
    TestID -> "verify-rejects-own-problem1"
]

VerificationTest[
    {Rule30PrizeEntry[good["id"]]["status"], Rule30PrizeEntry[good["id"]]["check"]["state"], Rule30PrizeEntry[bad["id"]]["status"]},
    {"Lean Verified", "passed", "Lean Unverified"},
    TestID -> "verify-records-status"
]

VerificationTest[
    Rule30PrizeEntry[bad["id"]]["check"]["official"][[1, "axioms"]],
    {"sorryAx"},
    TestID -> "verify-reports-sorry"
]

VerificationTest[Rule30PrizeQueue[10], {}, TestID -> "queue-empty-after-verify"]

VerificationTest[
    Rule30PrizeRecordCheck[good["id"], "0000", <|"verdict" -> "pass"|>][[1]],
    "Stale",
    TestID -> "record-check-needs-hash"
]

(* === administration === *)

VerificationTest[Rule30PrizeSetStatus[good["id"], "Human Verified", "Read by a maintainer."]["status"], "Human Verified", TestID -> "admin-human-verified"]

VerificationTest[
    Rule30PrizeRecordCheck[good["id"], Rule30PrizeEntry[good["id"]]["notebookSHA256"], <|"verdict" -> "fail", "reasons" -> {"re-check"}|>]["status"],
    "Human Verified",
    TestID -> "recheck-keeps-human-status"
]

VerificationTest[Rule30PrizeSetStatus[good["id"], "Winner"][[1]], "Status", TestID -> "admin-rejects-unknown-status"]

VerificationTest[
    First[Rule30PrizeEntries[]]["id"],
    good["id"],
    TestID -> "entries-best-first"
]

VerificationTest[
    Rule30PrizeHide[nosrc["id"], "spam"];
    MemberQ[#id& /@ Rule30PrizeEntries[], nosrc["id"]],
    False,
    TestID -> "admin-hide"
]

VerificationTest[Lookup[Rule30PrizeContact[good["id"]], {"submitter", "address"}], {agentID, Null}, TestID -> "private-details-kept"]

(* === what an agent sees: the status of its own submissions, by its Wolfram ID === *)

VerificationTest[
    KeyTake[statusAs[agentID, good["id"]], {"id", "status"}],
    <|"id" -> good["id"], "status" -> "Human Verified"|>,
    TestID -> "status-of-own-submission"
]

VerificationTest[statusAs[agentID, bad["id"]]["check"]["state"], "failed", TestID -> "status-shows-failure"]

VerificationTest[statusAs["other@example.org", good["id"]][[1]], "NoEntry", TestID -> "status-only-for-its-submitter"]

VerificationTest[statusAs["reviewer@wolfram.com", good["id"]]["id"], good["id"], TestID -> "status-for-reviewers"]

VerificationTest[
    {SubsetQ[#id& /@ statusAs[agentID]["submissions"], {good["id"], bad["id"]}], statusAs["other@example.org"]["submissions"]},
    {True, {}},
    TestID -> "status-lists-own-submissions"
]

VerificationTest[KeyExistsQ[statusAs[agentID, good["id"]], "review"], False, TestID -> "status-hides-review-notes"]

(* === the submissions page, for reviewers === *)

VerificationTest[
    Rule30PrizeSite`Private`reviewerQ /@ {"a@wolframinstitute.org", "B.C@WolframInstitute.org", "a@wolfram.com", "a@evilwolfram.com", "a@mail.wolfram.com", "a@wolframinstitute.org.evil.com", "a@wolfram.com.evil.com", "a@gmail.com", "wolfram.com", None},
    {True, True, True, False, False, False, False, False, False, False},
    TestID -> "reviewers-by-domain"
]

html = Rule30PrizeSubmissionsPage[]

VerificationTest[
    {StringCount[html, "</script>"], StringContainsQ[html, "<\\/script><script>alert(1)<\\/script>"]},
    {2, True},
    TestID -> "page-escapes-script"
]

json = ImportString[ExportString[Rule30PrizeSite`Private`submissionsData[Rule30PrizeEntries[]], "RawJSON"], "RawJSON"]

VerificationTest[json["entries"][[All, "id"]], #id& /@ Rule30PrizeEntries[], TestID -> "json-matches-entries"]

VerificationTest[{FreeQ[json, "address" | "token" | "tokenSHA256"], MemberQ[json["entries"][[All, "submitter"]], agentID]}, {True, True}, TestID -> "json-has-no-private-details"]

(* The public instructions are self-contained: they link the kit's repository, and name no other
   repository, no archive and none of the infrastructure behind the verifier. *)
public = Import[FileNameJoin[Prepend[#, FileNameJoin[{$testDirectory, ".."}]]], "Text", CharacterEncoding -> "UTF-8"]& /@ {{"skill.md"}, {"site", "agents.html"}, {"notebooks", "HowToStart.md"}}

VerificationTest[
    {AllTrue[public, StringContainsQ[#, "https://github.com/WolframInstitute/Rule30PrizeKit"]&], Flatten[StringCases[public, "sw1sh" | "Prime Intellect" | "PrimeIntellect" | "write-up" | "writeup" | "tar.gz" | "/obj/nikm/"]]},
    {True, {}},
    TestID -> "public-instructions-self-contained"
]

(* === the reviewers' view of a notebook: nothing in it runs === *)

viewOf[file_] := Block[{Rule30PrizeSite`Private`$rootURL = "https://example.org/Rule30Prize"},
    Rule30PrizeSite`Private`viewNotebook["R30-TEST", Rule30PrizeSite`Private`heldNotebook[file]]
]

(* Each part tries to set a flag: when shown, when clicked, when evaluated, when parsed, or through its
   stylesheet. *)
hostileView = viewOf[rawFile["Notebook[{" <>
    "Cell[BoxData[DynamicBox[ToBoxes[Global`pwnedDynamic = True]]], \"Output\"], " <>
    "Cell[BoxData[ButtonBox[\"click\", ButtonFunction :> (Global`pwnedButton = True)]], \"Output\"], " <>
    "Cell[TextData[{ButtonBox[\"link\", BaseStyle -> \"Hyperlink\", ButtonData -> {URL[\"javascript:alert(1)\"], None}]}], \"Text\"], " <>
    "Cell[BoxData[RowBox[{\"1\", \"+\", \"1\"}]], \"Input\", CellEvaluationFunction -> (Global`pwnedEval = True&)], " <>
    "Cell[Set[Global`pwnedRaw, True], \"Text\"], " <>
    "Cell[\"\\!\\(\\*DynamicBox[ToBoxes[Global`pwnedString = True]]\\)\", \"Text\"], " <>
    "Cell[BoxData[GraphicsBox[{RGBColor[1, 0, 0], DiskBox[{0, 0}]}]], \"Output\"]" <>
    "}, NotebookDynamicExpression :> (Global`pwnedNotebook = True), " <>
    "StyleDefinitions -> Notebook[{Cell[StyleData[\"Text\"], CellEventActions -> {\"KeyDown\" :> (Global`pwnedStyle = True)}]}]]"]]

VerificationTest[
    {Head[hostileView],
     FreeQ[hostileView, DynamicBox | ButtonFunction | CellEvaluationFunction | NotebookDynamicExpression | CellEventActions | Set | StyleData],
     FreeQ[hostileView, "javascript:alert(1)"],
     FreeQ[hostileView, s_String /; StringContainsQ[s, "\!" | "\*"]],
     Count[hostileView, _GraphicsBox, Infinity],
     Lookup[Options[hostileView], {StyleDefinitions, Evaluatable}],
     {ValueQ[Global`pwnedDynamic], ValueQ[Global`pwnedButton], ValueQ[Global`pwnedEval], ValueQ[Global`pwnedRaw], ValueQ[Global`pwnedString], ValueQ[Global`pwnedNotebook], ValueQ[Global`pwnedStyle]}},
    {Notebook, True, True, True, 1, {"Default.nb", False}, {False, False, False, False, False, False, False}},
    TestID -> "view-keeps-no-code"
]

VerificationTest[Count[viewOf[submissionNotebook[template]], Cell[_, "Input", ___], Infinity], 2, TestID -> "view-keeps-the-essay"]

(* The Wolfram Cloud encodes a computed text/html body a second time: the page goes out as ASCII,
   with the data's other characters escaped as JSON does. *)
VerificationTest[
    {Max[ToCharacterCode[Rule30PrizeSubmissionsPage[]]] < 128,
     Rule30PrizeSite`Private`asciiJSON["{\"t\":\"a\[CenterDot]b \:2115 " <> FromCharacterCode[128512] <> "\"}"],
     ImportString[Rule30PrizeSite`Private`asciiJSON["{\"t\":\"a\[CenterDot]b \:2115 " <> FromCharacterCode[128512] <> "\"}"], "RawJSON"]["t"] === "a\[CenterDot]b \:2115 " <> FromCharacterCode[128512]},
    {True, "{\"t\":\"a\\u00b7b \\u2115 \\ud83d\\ude00\"}", True},
    TestID -> "page-and-json-are-ascii"
]
