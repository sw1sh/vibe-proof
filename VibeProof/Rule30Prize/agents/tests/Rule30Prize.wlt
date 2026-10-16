(* Tests for the submissions (Rule30PrizeSite.wl) and the verifier (Rule30PrizeVerifier.wl), against
   a local store and the local kit. Run with: wolframscript -f run.wls *)

kit = FileNameJoin[{$testDirectory, "..", "..", "kit"}]

template = Import[FileNameJoin[{kit, "Rule30Submission.lean"}], "Text", CharacterEncoding -> "UTF-8"]

unicodeSource = StringJoin[
    "import Rule30PrizeKit\n\n/-! Unicode: \[ForAll] \[Not] \[RightArrow] \:21a6 \:2115 \:27e8\:27e9 \[Lambda], and \"quotes\" and a back\\slash. -/\n\n",
    "namespace Rule30Submission\n\nopen Ruliology.CellularAutomata.Rule30Prize\n\n",
    "theorem no_period_one : \[Not] \[Exists] N, \[ForAll] t, N \[LessEqual] t \[RightArrow] center (t + 1) = center t :=\n  center_not_eventually_period_one\n\n",
    "theorem anon : \[Exists] n : \:2115, n = 0 := \:27e80, rfl\:27e9\n\nend Rule30Submission\n"
]

sorrySource = "import Rule30PrizeKit\nnamespace Rule30Submission\nopen Ruliology.CellularAutomata.Rule30Prize\ntheorem problem1 : Problem1 := by sorry\nend Rule30Submission\n"

(* A notebook file whose input cell is `rule30Submission = LeanImportString[src, ...]`, written as
   the front end writes it: boxes of strings. *)
submissionNotebook[src_String, extra_List : {}] := Block[{file = FileNameJoin[{$TemporaryDirectory, CreateUUID[] <> ".nb"}]},
    Export[file, Notebook[Join[
        {Cell["An essay", "Title"], Cell["The proof:", "Text"]},
        {With[{s = src}, Cell[BoxData[MakeBoxes[rule30Submission = LeanImportString[s, "ProjectDir" -> $Rule30PrizeKit], StandardForm]], "Input"]]},
        extra
    ]], "NB"];
    file
]

rawFile[text_String] := Block[{file = FileNameJoin[{$TemporaryDirectory, CreateUUID[] <> ".nb"}]},
    Export[file, text, "Text"];
    file
]

fields[nb_, rest___Rule] := Join[
    <|"notebook" -> nb, "problem" -> 1, "claim" -> "partial", "title" -> "Period one", "authors" -> "A. Person; Claude",
      "agent" -> "Claude Code with Claude Opus 5.5", "headlines" -> "Rule30Submission.no_period_one", "consent" -> True|>,
    <|rest|>
]

(* === reading notebooks without evaluating them === *)

VerificationTest[
    Rule30PrizeNotebookSource[submissionNotebook[unicodeSource]] === unicodeSource,
    True,
    TestID -> "extract-unicode-exact"
]

VerificationTest[
    Rule30PrizeNotebookSource[submissionNotebook[template, {Cell[BoxData[MakeBoxes[other = LeanImportString["theorem x : True := trivial"], StandardForm]], "Input"]}]] === template,
    True,
    TestID -> "extract-ignores-other-cells"
]

VerificationTest[
    Rule30PrizeNotebookSource[submissionNotebook[template, {Cell[BoxData[MakeBoxes[rule30Submission = LeanImportString["x"], StandardForm]], "Input"]}]][[1]],
    "AmbiguousSource",
    TestID -> "extract-ambiguous"
]

VerificationTest[
    Rule30PrizeNotebookSource[rawFile["Notebook[{Cell[\"no code here\", \"Text\"]}]"]][[1]],
    "NoSource",
    TestID -> "extract-none"
]

VerificationTest[
    Rule30PrizeNotebookSource[rawFile["this is not a notebook {"]][[1]],
    "NotNotebook",
    TestID -> "extract-not-a-notebook"
]

(* A hostile file: code where boxes belong, and an option that assigns when evaluated. Nothing in it
   may run. *)
VerificationTest[
    Block[{hostile},
        hostile = rawFile["Notebook[{Cell[BoxData[RowBox[{\"rule30Submission\", \"=\", RowBox[{\"LeanImportString\", \"[\", Set[Global`pwnedCell, True], \"]\"}]}]], \"Input\"], Cell[BoxData[Set[Global`pwnedBoxes, True]], \"Input\"]}, WindowTitle :> (Global`pwnedFile = True)]"];
        {Rule30PrizeNotebookSource[hostile][[1]], ValueQ[Global`pwnedCell], ValueQ[Global`pwnedBoxes], ValueQ[Global`pwnedFile]}
    ],
    {"NoSource", False, False, False},
    TestID -> "extract-never-evaluates"
]

(* === submitting === *)

Rule30PrizeSite`$Rule30PrizeStore = CreateDirectory[]

good = Rule30PrizeSubmit[fields[submissionNotebook[template]]]

VerificationTest[{good["ok"], good["status"], good["check"]["state"], good["target"], StringLength[good["token"]]}, {True, "Lean Unverified", "queued", Null, 32}, TestID -> "submit-partial"]

VerificationTest[
    Rule30PrizeSubmit[fields[submissionNotebook[template], "consent" -> False]][[1]],
    "Consent",
    TestID -> "submit-needs-consent"
]

VerificationTest[
    Rule30PrizeSubmit[fields[submissionNotebook[template], "agent" -> ""]][[1]],
    "Agent",
    TestID -> "submit-needs-agent"
]

VerificationTest[
    Rule30PrizeSubmit[fields[submissionNotebook[template], "headlines" -> "rm -rf /"]][[1]],
    "Headlines",
    TestID -> "submit-checks-headlines"
]

VerificationTest[
    Rule30PrizeSubmit[fields[submissionNotebook[template], "problem" -> "4"]][[1]],
    "Problem",
    TestID -> "submit-checks-problem"
]

bad = Rule30PrizeSubmit[fields[submissionNotebook[sorrySource], "claim" -> "proof", "headlines" -> None, "title" -> "</script><script>alert(1)</script>"]]

VerificationTest[{bad["ok"], bad["target"]}, {True, "Rule30Submission.problem1"}, TestID -> "submit-proof-claim"]

nosrc = Rule30PrizeSubmit[fields[rawFile["Notebook[{Cell[\"prose only\", \"Text\"]}]"], "title" -> "No Lean"]]

VerificationTest[nosrc["check"]["state"], "no-source", TestID -> "submit-without-source"]

(* Three submissions so far from this requester; with a limit of three an hour, the next is refused. *)
VerificationTest[
    Block[{Rule30PrizeSite`Private`$rateLimits = {{3600, 3}}}, Rule30PrizeSubmit[fields[submissionNotebook[template]]][[1]]],
    "RateLimit",
    TestID -> "submit-rate-limit"
]

VerificationTest[
    Sort[#id& /@ Rule30PrizeQueue[10]],
    Sort[{good["id"], bad["id"]}],
    TestID -> "queue-holds-sources"
]

(* The deployed API starts each new verification through this hook. *)
VerificationTest[
    Block[{Rule30PrizeSite`$Rule30PrizeOnSubmit = Function[id, hooked = id], hooked = None},
        hookedSubmission = Rule30PrizeSubmit[fields[submissionNotebook[template], "title" -> "Hooked"]];
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
    ByteArrayToString[BaseDecode[First[Select[Rule30PrizeQueue[10], #id === good["id"]&]]["sourceBase64"]], "UTF-8"] === template,
    True,
    TestID -> "queue-source-bytes"
]

(* === verifying, on this machine === *)

(* An agent's fake proof of Problem 1: it does not import the kit and declares a Problem1 of its own
   (the kit's tests/T07Redefine.lean). *)
redefined = Block[{Rule30PrizeSite`Private`$rateLimits = {}},
    Rule30PrizeSubmit[fields[submissionNotebook[Import[FileNameJoin[{kit, "tests", "T07Redefine.lean"}], "Text", CharacterEncoding -> "UTF-8"]], "claim" -> "proof", "headlines" -> None]]
]

verified = Rule30PrizeVerify["Method" -> "Local", "Kit" -> kit]

VerificationTest[
    Sort[{#id, #verdict}& /@ verified],
    Sort[{{good["id"], "pass"}, {bad["id"], "fail"}, {redefined["id"], "fail"}}],
    TestID -> "verify-local"
]

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
    Rule30PrizeRecordCheck[good["id"], Rule30PrizeEntry[good["id"]]["sourceSHA256"], <|"verdict" -> "fail", "reasons" -> {"re-check"}|>]["status"],
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

VerificationTest[Lookup[Rule30PrizeContact[good["id"]], {"requester", "tokenSHA256"}], {"local", Missing["KeyAbsent", "tokenSHA256"]}, TestID -> "private-details-kept"]

(* === what an agent sees: its status, with its token === *)

VerificationTest[
    KeyTake[Rule30PrizeStatus[good["id"], good["token"]], {"id", "status"}],
    <|"id" -> good["id"], "status" -> "Human Verified"|>,
    TestID -> "status-with-token"
]

VerificationTest[Rule30PrizeStatus[bad["id"], bad["token"]]["check"]["state"], "failed", TestID -> "status-shows-failure"]

VerificationTest[Rule30PrizeStatus[good["id"], bad["token"]][[1]], "NoEntry", TestID -> "status-needs-its-own-token"]

VerificationTest[KeyExistsQ[Rule30PrizeStatus[good["id"], good["token"]], "review"], False, TestID -> "status-hides-review-notes"]

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

VerificationTest[FreeQ[json, "email" | "requester" | "tokenSHA256" | "token"], True, TestID -> "json-has-no-private-details"]

(* The public instructions are self-contained: they link the kit's repository, and name no other
   repository, no archive and none of the infrastructure behind the verifier. *)
public = Import[FileNameJoin[Prepend[#, FileNameJoin[{$testDirectory, ".."}]]], "Text", CharacterEncoding -> "UTF-8"]& /@ {{"skill.md"}, {"site", "agents.html"}, {"notebooks", "HowToStart.md"}}

VerificationTest[
    {AllTrue[public, StringContainsQ[#, "https://github.com/WolframInstitute/Rule30PrizeKit"]&], Flatten[StringCases[public, "sw1sh" | "Prime Intellect" | "PrimeIntellect" | "write-up" | "writeup" | "tar.gz" | "/obj/nikm/"]]},
    {True, {}},
    TestID -> "public-instructions-self-contained"
]
