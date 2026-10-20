(* ::Package:: *)

(* Rule30PrizeSite.wl - submissions to the Rule 30 Prize, in the Wolfram Cloud.

   Agents submit through the API only; there is no form. The API serves authenticated requests only:
   the Wolfram ID that makes the request is the submitter, and any Wolfram ID may submit, with or
   without a subscription. A submitter reads the status of their own submissions through the same
   identity. Reviewers - Wolfram IDs at $Rule30PrizeReviewerDomains - read the submissions page, its
   JSON and the files. Nothing is public but the instructions.

   Load it locally to deploy, administer or test:

       Get["Rule30PrizeSite.wl"]
       Rule30PrizeDeploy[]                      (* deploys under $Rule30PrizeRoot *)
       Rule30PrizeSetStatus[id, "Human Verified", "note"]

   The deployed APIs carry these definitions with them (CloudDeploy with IncludeDefinitions -> True)
   and run as the account that deployed them.

   The site never evaluates an uploaded notebook: it only checks that the file parses as one, held.
   The verifier evaluates it in a sandbox of its own and reads the LeanEnvironment its
   rule30Submission holds; the Lean source behind it comes back with the verifier's result. *)

BeginPackage["Rule30PrizeSite`"]

$Rule30PrizeRoot::usage = "$Rule30PrizeRoot is the cloud directory of the submissions, relative to the account's home."

$Rule30PrizeStore::usage = "$Rule30PrizeStore is \"Cloud\", or a local directory that stands in for the cloud in tests."

$Rule30PrizeStatuses::usage = "$Rule30PrizeStatuses lists the statuses of a submission, in order."

$Rule30PrizeReviewerDomains::usage = "$Rule30PrizeReviewerDomains lists the email domains of the Wolfram IDs that may read the submissions."


Rule30PrizeSubmit::usage = "Rule30PrizeSubmit[assoc] validates and stores a submission from the requesting Wolfram ID and gives an association with its id and status, or a Failure."

Rule30PrizeStatus::usage = "Rule30PrizeStatus[id] gives the status of a submission to the Wolfram ID that submitted it, or to a reviewer. Rule30PrizeStatus[] gives the status of all of the requester's submissions."

Rule30PrizeEntries::usage = "Rule30PrizeEntries[] gives the entries of the submissions page, best first."

Rule30PrizeEntry::usage = "Rule30PrizeEntry[id] gives the entry of one submission."

Rule30PrizeSubmissionsPage::usage = "Rule30PrizeSubmissionsPage[] gives the submissions page as an HTML string."

Rule30PrizeQueue::usage = "Rule30PrizeQueue[n] gives up to n submissions waiting for the Lean verifier, with their sources (the owner's kernel)."

Rule30PrizeQueueItem::usage = "Rule30PrizeQueueItem[id] gives submission id as the verifier needs it, if it is waiting for the verifier."

Rule30PrizeClaimCheck::usage = "Rule30PrizeClaimCheck[id] marks a waiting submission as being checked, and gives True if it did."

$Rule30PrizeOnSubmit::usage = "$Rule30PrizeOnSubmit is None, or a function applied to the id of each new submission."

Rule30PrizeDeployView::usage = "Rule30PrizeDeployView[id] deploys a view of a submission's notebook for reviewers, without the parts that run code, and gives its address."

Rule30PrizeProgress::usage = "Rule30PrizeProgress[id, detail] records what the verifier is doing on a submission it is checking."

Rule30PrizeRecordCheck::usage = "Rule30PrizeRecordCheck[id, sha, result] records the verifier's result for submission id, whose Lean source has SHA-256 sha."

Rule30PrizeSetStatus::usage = "Rule30PrizeSetStatus[id, status, note] sets the status of a submission (an administrator's action)."

Rule30PrizeRequeue::usage = "Rule30PrizeRequeue[id] sends a submission back to the Lean verifier."

Rule30PrizeHide::usage = "Rule30PrizeHide[id, reason] hides a submission from the submissions page; Rule30PrizeHide[id, False] shows it again."

Rule30PrizeContact::usage = "Rule30PrizeContact[id] gives the private contact details of a submission."

Rule30PrizeAttach::usage = "Rule30PrizeAttach[root] points the kernel at the submissions deployed under root, for administration and verification."

Rule30PrizeDeploy::usage = "Rule30PrizeDeploy[] deploys the submission API, the status API, the reviewers' submissions page and the instructions under $Rule30PrizeRoot."

Begin["`Private`"]

(* === settings === *)

$Rule30PrizeRoot = "Rule30Prize"

$Rule30PrizeStore = "Cloud"

$Rule30PrizeStatuses = {"Lean Unverified", "Lean Verified", "Human Verified", "Prize Claimed"}

$Rule30PrizeReviewerDomains = {"wolframinstitute.org", "wolfram.com"}

(* Rule30PrizeDeploy sets it to start the verification of each new submission in the cloud. *)
$Rule30PrizeOnSubmit = None

(* A check that has been running this long without a result is presumed dead, and queued again. *)
$staleRunSeconds = 7200

$kitVersion = "2"

$maxNotebookBytes = 30 * 2^20

$maxSourceBytes = 2 * 2^20

(* Submissions per requester: at most 5 an hour and 20 a day; at most 300 a day in all. *)
$rateLimits = {{3600, 5}, {86400, 20}}

$dailyLimit = 300

$problems = <|
    1 -> "Does the center column always remain non-periodic?",
    2 -> "Does each color of cell occur on average equally often in the center column?",
    3 -> "Does computing the nth cell of the center column require at least O(n) computational effort?"
|>

$claims = {"proof", "disproof", "partial"}

(* The theorem that settles each problem. Problem 3 has no official Lean statement. *)
$officialTargets = <|
    {1, "proof"} -> "Rule30Submission.problem1",
    {1, "disproof"} -> "Rule30Submission.not_problem1",
    {2, "proof"} -> "Rule30Submission.problem2",
    {2, "disproof"} -> "Rule30Submission.not_problem2"
|>

$headlinePattern = RegularExpression["Rule30Submission(\\.[A-Za-z_][A-Za-z0-9_'!?]*)+"]

$idPattern = RegularExpression["R30-[0-9]{8}-[0-9a-f]{6}"]

(* Filled in by Rule30PrizeAttach, and carried into the deployed code. *)
$rootURL = None

$indexCE = None

$privateCE = None

$rateCE = None

(* As UTF-8 bytes: deployed definitions carry strings outside ASCII garbled, and bytes intact. *)
$submissionsTemplateBytes = Quiet @ ReadByteArray[FileNameJoin[{DirectoryName[$InputFileName], "submissions.html"}]]

(* === small helpers === *)

failure[tag_String, msg_String] := Failure[tag, <|"MessageTemplate" -> msg|>]

nowUnix[] := Round @ UnixTime[]

isoTime[unix_Integer] := DateString[FromUnixTime[unix, TimeZone -> 0], "ISODateTime", TimeZone -> 0] <> "Z"

sha256[ba_ByteArray] := Hash[ba, "SHA256", "HexString"]

sha256[s_String] := sha256[utf8[s]]

utf8[s_String] := StringToByteArray[s, "UTF-8"]

cleanText[s_String, max_Integer] := StringTake[StringTrim @ StringReplace[s, RegularExpression["[\\x00-\\x08\\x0B\\x0C\\x0E-\\x1F\\x7F]"] -> ""], UpTo[max]]

cleanText[_, _] := ""

nullIfEmpty[s_String] := If[s === "", Null, s]

nullIfEmpty[_] := Null

(* The submitter: the Wolfram ID that signed the request. The submission and status APIs are deployed
   for authenticated requests only, so every call to them carries one. *)
submitterID[] := Replace[$RequesterWolframID, Except[_String] -> None]

requesterAddress[] := Replace[$RequesterAddress, Except[_String] -> Null]

newToken[] := IntegerString[RandomInteger[2^128 - 1], 16, 32]

newID[] := "R30-" <> DateString[{"Year", "Month", "Day"}, TimeZone -> 0] <> "-" <> IntegerString[RandomInteger[16^6 - 1], 16, 6]

(* Wolfram IDs at the reviewers' domain. A Wolfram ID is a verified email address. *)
reviewerQ[id_String] := AnyTrue[$Rule30PrizeReviewerDomains, StringEndsQ[ToLowerCase[StringTrim[id]], "@" <> ToLowerCase[#]]&]

reviewerQ[_] := False

(* JSON that can sit inside a <script> element. *)
(* JSON in ASCII, with \uXXXX escapes (UTF-16 surrogate pairs beyond the BMP): the Wolfram Cloud
   encodes the body of a computed text/html response a second time, so the reviewers' page must be
   ASCII, and the JSON responses are too. *)
jsonEscape[c_String] := StringJoin @ Map[
    If[# > 65535,
        With[{u = # - 65536}, "\\u" <> IntegerString[55296 + BitShiftRight[u, 10], 16, 4] <> "\\u" <> IntegerString[56320 + BitAnd[u, 1023], 16, 4]],
        "\\u" <> IntegerString[#, 16, 4]
    ]&,
    ToCharacterCode[c]
]

asciiJSON[s_String] := StringReplace[s, c : RegularExpression["[^\\x00-\\x7F]"] :> jsonEscape[c]]

scriptJSON[expr_] := StringReplace[asciiJSON @ ExportString[expr, "RawJSON", "Compact" -> True], {"</" -> "<\\/", "<!--" -> "<\\!--"}]

(* === storage: the cloud, or a local directory for tests === *)

localStoreQ[] := StringQ[$Rule30PrizeStore] && $Rule30PrizeStore =!= "Cloud"

localFile[parts__String] := FileNameJoin[{$Rule30PrizeStore, parts}]

readLocal[name_String] := Replace[Quiet @ Get[localFile[name]], Except[_Association] -> <||>]

writeLocal[name_String, value_] := Block[{},
    Quiet @ CreateDirectory[$Rule30PrizeStore];
    Put[value, localFile[name]];
    value
]

storeIndex[] := If[localStoreQ[], readLocal["index.wl"], Replace[$indexCE[], Except[_Association] -> <||>]]

storeEntry[id_String] := Lookup[storeIndex[], id, Missing["NoEntry", id]]

storeSetEntry[id_String, entry_Association] := If[ localStoreQ[],
    writeLocal["index.wl", Append[readLocal["index.wl"], id -> entry]],
    $indexCE[id] = entry
]

storeSetPrivate[id_String, data_Association] := If[ localStoreQ[],
    writeLocal["private.wl", Append[readLocal["private.wl"], id -> data]],
    $privateCE[id] = data
]

storePrivate[id_String] := If[ localStoreQ[],
    Lookup[readLocal["private.wl"], id, Missing["NoEntry", id]],
    Replace[$privateCE[id], Except[_Association] -> Missing["NoEntry", id]]
]

storeRate[key_String] := If[localStoreQ[], Lookup[readLocal["rate.wl"], key, {}], Replace[$rateCE[key], Except[_List] -> {}]]

storeSetRateTimes[key_String, times_List] := If[ localStoreQ[],
    writeLocal["rate.wl", Append[readLocal["rate.wl"], key -> times]],
    $rateCE[key] = times
]

(* A submission's files live under data/<id>/, private. In the cloud each one is a ByteArray stored
   with CloudPut: a deployed API cannot CopyFile a local file into the cloud. *)
submissionURL[id_String, name_String] := If[ localStoreQ[],
    localFile["data", id, name],
    $rootURL <> "/data/" <> id <> "/" <> name
]

storeBytes[id_String, name_String, bytes_ByteArray] := If[ localStoreQ[],
    Quiet @ CreateDirectory[localFile["data", id], CreateIntermediateDirectories -> True];
    BinaryWrite[localFile["data", id, name], bytes];
    Close[localFile["data", id, name]],
    CloudPut[bytes, CloudObject[submissionURL[id, name], Permissions -> "Private"]]
]

storeReadBytes[id_String, name_String] := If[ localStoreQ[],
    Quiet @ ReadByteArray[localFile["data", id, name]],
    Replace[Quiet @ CloudGet[CloudObject[submissionURL[id, name]]], Except[_ByteArray] -> $Failed]
]

endpointURL[name_String] := If[localStoreQ[], "#" <> name, $rootURL <> "/" <> name]

(* A public page: a stored HTTP response, served as it is, without an evaluation per view. *)
publishText[name_String, text_String, mime_String] := CloudDeploy[
    HTTPResponse[utf8[text], <|"ContentType" -> mime|>],
    CloudObject[$rootURL <> "/" <> name],
    Permissions -> "Public"
]

(* === checking that an upload is a notebook === *)

(* The file parsed, held: nothing in it is evaluated here. *)
heldNotebook[path_String] := Block[{text, held},
    text = Quiet @ ReadString[path];
    If[ ! StringQ[text], Return[failure["Unreadable", "The file could not be read."], Block]];
    held = Block[{$Context = "Rule30PrizeSite`Parsed`", $ContextPath = {"System`"}},
        TimeConstrained[MemoryConstrained[Quiet @ ToExpression[text, InputForm, HoldComplete], 4 * 2^30, $Failed], 120, $Failed]
    ];
    (* The comments around the Notebook expression in the file parse to Nulls. *)
    Replace[held, {HoldComplete[Null ..., nb_Notebook, Null ...] :> HoldComplete[nb], _ -> failure["NotNotebook", "The file is not a Wolfram notebook (.nb)."]}]
]

(* === a view of a submitted notebook, for reviewers === *)

(* A submitted notebook is untrusted: its dynamic content, buttons, links and initialization would
   run in the session of whoever opens it. The view keeps what the notebook shows and drops what it
   runs. It is built from the held expression, so nothing in the notebook is evaluated: every head
   that is not a box, cell or graphics form becomes a note, code-running options go, links keep only
   web addresses, strings lose embedded box code, and the view's cells cannot be evaluated. The
   notebook's own stylesheet is replaced by the standard one: an embedded stylesheet carries code of
   its own, such as event actions and compressed data that evaluates to arbitrary expressions. *)

$viewNote = StyleBox["[removed from this view]", FontSlant -> "Italic", FontColor -> GrayLevel[0.5]]

$viewHeadNames = Join[
    Context[#] <> SymbolName[#]& /@ {Notebook, Cell, CellGroupData, BoxData, TextData, List, Rule, RuleDelayed, Association, URL,
        Directive, RGBColor, GrayLevel, Hue, CMYKColor, LABColor, Opacity, Thickness, AbsoluteThickness, Dashing, AbsoluteDashing,
        PointSize, AbsolutePointSize, EdgeForm, FaceForm, CapForm, JoinForm, Arrowheads, Offset, Scaled, ImageScaled,
        Function, Slot, SlotSequence, TemplateSlot, TemplateSlotSequence, Part, Times, Plus, Power, Log, Exp, Rational, Complex,
        FrontEndResource, Spacer},
    {"FrontEnd`FileName"}
]

(* Boxes that hold controls or update themselves. *)
$viewDeniedBoxNames = Context[#] <> SymbolName[#]& /@ {DynamicBox, DynamicModuleBox, DynamicWrapperBox, ActionMenuBox, AnimatorBox,
    CheckboxBox, ColorSetterBox, InputFieldBox, ListPickerBox, LocatorPaneBox, OpenerBox, PopupMenuBox, ProgressIndicatorBox,
    RadioButtonBox, SetterBox, Slider2DBox, SliderBox, TogglerBox}

$viewCodeOptions = Alternatives[CellEvaluationFunction, CellDynamicExpression, CellProlog, CellEpilog, InitializationCell,
    Initialization, Deinitialization, NotebookDynamicExpression, NotebookEventActions, CellEventActions, FrontEndEventActions,
    ButtonFunction, DockedCells, DynamicModuleValues, UnsavedVariables, Evaluator, StyleDefinitions, TaggingRules]

SetAttributes[{viewHeadQ, viewSymbolQ}, HoldAllComplete]

viewHeadQ[h_Symbol] := With[{name = Context[Unevaluated[h]] <> SymbolName[Unevaluated[h]]},
    MemberQ[$viewHeadNames, name] || StringStartsQ[name, "Charting`"] ||
        (StringStartsQ[name, "System`"] && StringEndsQ[name, "Box"] && ! MemberQ[$viewDeniedBoxNames, name])
]

viewHeadQ[_] := False

viewSymbolQ[s_Symbol] := MemberQ[{"System`", "FrontEnd`", "Charting`"}, Context[Unevaluated[s]]]

(* Every replacement inserts a constant, a string or a symbol's name, never a part of the notebook to
   be evaluated. *)
viewHeld[held_HoldComplete] := Module[{h = held},
    h = DeleteCases[h, (Rule | RuleDelayed)[$viewCodeOptions, _], Infinity];
    h = Replace[h, URL[s_String /; ! StringMatchQ[s, ("https://" | "http://" | "mailto:") ~~ ___]] :> URL["about:blank"], {1, Infinity}];
    h = Replace[h, _[___]?(Function[e, ! viewHeadQ @@ Head[Unevaluated[e], Hold], HoldAllComplete]) :> $viewNote, {1, Infinity}];
    h = Replace[h, s_Symbol /; ! viewSymbolQ[s] :> SymbolName[Unevaluated[s]], {1, Infinity}];
    Replace[h, s_String :> StringDelete[s, "\!" | "\*" | "\(" | "\)"], {1, Infinity}]
]

viewNotebook[id_String, held_HoldComplete] := Replace[viewHeld[held], {
    HoldComplete[Notebook[cells_List, opts___]] :> Notebook[
        Prepend[cells, Cell[TextData[{
            "A view of submission " <> id <> " for reviewers. Its interactive content and anything that runs code are removed, and its cells cannot be evaluated. ",
            ButtonBox["Download the original notebook", BaseStyle -> "Hyperlink", ButtonData -> {URL[endpointURL["api/file"] <> "?id=" <> id <> "&kind=notebook"], None}],
            "."
        }], "Text", Background -> RGBColor[1., 0.97, 0.88]]],
        Sequence @@ FilterRules[{opts}, Except[Editable | Evaluatable | Saveable]],
        Editable -> False, Evaluatable -> False, Saveable -> False, StyleDefinitions -> "Default.nb"
    ],
    _ -> $Failed
}]

(* Deployed at an address no one can guess, since Wolfram Cloud permissions cannot name the reviewers'
   domains. The submission API starts this in the cloud for every new submission. *)
Rule30PrizeDeployView[id_String] := Block[{e = storeEntry[id], bytes, file, held, nb, obj},
    If[MissingQ[e], Return[failure["NoEntry", "No submission " <> id <> "."], Block]];
    bytes = storeReadBytes[id, "essay.nb"];
    If[ ! ByteArrayQ[bytes], Return[failure["NoNotebook", "The submission has no notebook."], Block]];
    file = FileNameJoin[{$TemporaryDirectory, CreateUUID[] <> ".nb"}];
    BinaryWrite[file, bytes];
    Close[file];
    held = heldNotebook[file];
    Quiet @ DeleteFile[file];
    If[FailureQ[held], Return[held, Block]];
    nb = viewNotebook[id, held];
    If[ ! MatchQ[nb, _Notebook], Return[failure["View", "The notebook could not be turned into a view."], Block]];
    obj = CloudDeploy[nb, CloudObject[$rootURL <> "/view/" <> id <> "-" <> newToken[] <> ".nb"], Permissions -> {"Authenticated" -> {"Read"}}];
    If[ ! MatchQ[obj, _CloudObject], Return[failure["View", "The view could not be deployed."], Block]];
    e = storeEntry[id];
    If[StringQ[e["files"]["view"]], Quiet @ DeleteObject[CloudObject[e["files"]["view"]]]];
    storeSetEntry[id, Join[e, <|"files" -> Append[e["files"], "view" -> First[obj]]|>]];
    First[obj]
]

(* === validating a submission === *)

headlineNames[s_String] := DeleteDuplicates @ StringSplit[s, RegularExpression["[\\s,;]+"]]

headlineNames[_] := {}

(* The fields of a submission, cleaned; or a Failure naming the first problem. *)
validFields[a_Association] := Block[{problem, claim, title, authors, agent, headlines, repository, supersedes},
    problem = Replace[a["problem"], {s_String /; StringMatchQ[StringTrim[s], DigitCharacter ..] :> FromDigits[StringTrim[s]], n_Integer :> n, _ -> None}];
    claim = ToLowerCase @ Replace[a["claim"], Except[_String] -> ""];
    title = cleanText[a["title"], 200];
    authors = cleanText[a["authors"], 300];
    agent = cleanText[a["agent"], 200];
    headlines = headlineNames[Replace[a["headlines"], Except[_String] -> ""]];
    repository = Replace[a["repository"], {URL[u_String] :> u, s_String :> StringTrim[s], _ -> ""}];
    supersedes = Replace[a["supersedes"], {s_String :> StringTrim[s], _ -> ""}];
    Which[
        ! MemberQ[{1, 2, 3}, problem], failure["Problem", "The problem must be 1, 2 or 3."],
        ! MemberQ[$claims, claim], failure["Claim", "The claim must be proof, disproof or partial."],
        StringLength[title] < 3, failure["Title", "Give a title of at least 3 characters."],
        StringLength[authors] < 2, failure["Authors", "Name the contributors: the people and the agents."],
        StringLength[agent] < 2, failure["Agent", "Name the agent and model that made the submission, for example Claude Code with Claude Opus 5.5."],
        ! TrueQ[a["consent"]], failure["Consent", "The submission needs consent=true: the human behind the agent agrees to submit it."],
        Length[headlines] > 20, failure["Headlines", "List at most 20 headline theorems."],
        ! AllTrue[headlines, StringMatchQ[#, $headlinePattern]&], failure["Headlines", "Headline theorems are full names in the Rule30Submission namespace, such as Rule30Submission.no_period_two."],
        repository =!= "" && ! StringMatchQ[repository, RegularExpression["https?://[^\\s\"<>]+"]], failure["Repository", "The repository must be an http(s) URL."],
        supersedes =!= "" && ! StringMatchQ[supersedes, $idPattern], failure["Supersedes", "Supersedes takes a submission id such as R30-20261016-1a2b3c."],
        True,
            <|
                "problem" -> problem,
                "claim" -> claim,
                "title" -> title,
                "authors" -> authors,
                "agent" -> agent,
                "abstract" -> cleanText[a["abstract"], 3000],
                "headlines" -> headlines,
                "repository" -> repository,
                "supersedes" -> supersedes
            |>
    ]
]

(* Requests in the last hour and day, per requester and overall. *)
rateLimited[who_String, now_Integer] := Block[{mine, all},
    mine = Select[storeRate[who], now - # < 86400&];
    all = Select[storeRate["*"], now - # < 86400&];
    Which[
        Length[all] >= $dailyLimit, failure["RateLimit", "The submission API takes at most " <> ToString[$dailyLimit] <> " submissions a day. Try again tomorrow."],
        AnyTrue[$rateLimits, Count[mine, t_ /; now - t < First[#]] >= Last[#]&], failure["RateLimit", "Too many submissions from your address. Try again later."],
        True, storeSetRateTimes[who, Append[mine, now]]; storeSetRateTimes["*", Append[all, now]]; False
    ]
]

(* The theorem the verifier must find, and the state of the check, for new submissions. *)
checkPlan[fields_Association] := Block[{target = Lookup[$officialTargets, Key[{fields["problem"], fields["claim"]}], Null]},
    Which[
        target === Null && fields["headlines"] === {}, {target, <|"state" -> "no-target", "detail" -> "No headline theorem, so the verifier has nothing to check: reviewers read it as an essay."|>},
        True, {target, <|"state" -> "queued", "detail" -> "Waiting for the Lean verifier."|>}
    ]
]

(* === submitting === *)

notebookPath[nb_] := Replace[nb, {File[p_String] :> p, p_String /; FileExistsQ[p] :> p, _ -> $Failed}]

(* The notebook at an https URL, fetched into a temporary file. *)
fetchNotebook[url_String] /; StringMatchQ[url, RegularExpression["https://[^\\s\"<>]+"]] := Block[{file = FileNameJoin[{$TemporaryDirectory, CreateUUID[] <> ".nb"}], got},
    got = TimeConstrained[Quiet @ URLDownload[url, file], 60, $Failed];
    If[MatchQ[got, _File] && FileExistsQ[file], file, failure["Notebook", "Could not fetch the notebook from " <> url <> "."]]
]

fetchNotebook[_] := failure["Notebook", "Attach the notebook (.nb) of your computational essay, or give notebookURL, an https URL of it."]

Rule30PrizeSubmit[a_Association] := Block[{who = submitterID[], path, fields, now, limited, held, bytes, id, target, check, entry, files},
    If[ ! StringQ[who], Return[failure["WolframID", "Submit with a Wolfram ID: call the API from a Wolfram Language kernel connected to the Wolfram Cloud (CloudConnect)."], Block]];
    fields = validFields[a];
    If[FailureQ[fields], Return[fields, Block]];
    now = nowUnix[];
    limited = rateLimited[who, now];
    If[FailureQ[limited], Return[limited, Block]];
    path = Replace[notebookPath[a["notebook"]], $Failed :> fetchNotebook[a["notebookURL"]]];
    If[FailureQ[path], Return[path, Block]];
    If[FileByteCount[path] > $maxNotebookBytes, Return[failure["Notebook", "The notebook is larger than 30 MB."], Block]];
    held = heldNotebook[path];
    If[FailureQ[held], Return[held, Block]];
    bytes = ReadByteArray[path];
    id = newID[];
    {target, check} = checkPlan[fields];
    storeBytes[id, "essay.nb", bytes];
    (* The Lean source arrives with the verifier's result. *)
    files = <|"notebook" -> endpointURL["api/file"] <> "?id=" <> id <> "&kind=notebook", "lean" -> Null|>;
    entry = <|
        "id" -> id,
        "title" -> fields["title"],
        "problem" -> fields["problem"],
        "claim" -> fields["claim"],
        "authors" -> fields["authors"],
        "agent" -> fields["agent"],
        "abstract" -> nullIfEmpty[fields["abstract"]],
        "repository" -> nullIfEmpty[fields["repository"]],
        "supersedes" -> nullIfEmpty[fields["supersedes"]],
        "submitted" -> isoTime[now],
        "submittedUnix" -> now,
        "submitter" -> who,
        "status" -> "Lean Unverified",
        "target" -> target,
        "headlines" -> fields["headlines"],
        "check" -> check,
        "review" -> Null,
        "files" -> files,
        "hidden" -> False,
        "kit" -> $kitVersion,
        "notebookSHA256" -> sha256[bytes],
        "notebookBytes" -> Length[bytes],
        "sourceSHA256" -> Null,
        "sourceBytes" -> Null
    |>;
    storeSetEntry[id, entry];
    storeSetPrivate[id, <|"submitter" -> who, "address" -> requesterAddress[], "submittedUnix" -> now|>];
    (* Start the verification; a failure here must not lose the submission, which stays queued. *)
    If[$Rule30PrizeOnSubmit =!= None, Quiet @ Check[$Rule30PrizeOnSubmit[id], Null]];
    <|
        "ok" -> True,
        "id" -> id,
        "submitter" -> who,
        "status" -> entry["status"],
        "check" -> check,
        "target" -> target,
        "statusURL" -> endpointURL["api/status"] <> "?id=" <> id
    |>
]

(* What a submitter sees of their submission: the verdict and its reasons, nothing reviewers wrote. *)
statusView[e_Association] := <|
        "id" -> e["id"],
        "title" -> e["title"],
        "status" -> e["status"],
        "submitted" -> e["submitted"],
        "target" -> e["target"],
        "headlines" -> e["headlines"],
        "check" -> KeyTake[e["check"], {"state", "detail", "verdict", "reasons", "verifiedTargets", "official", "headlines", "newAxioms", "lean", "kitCommit", "checkedAt", "log"}]
    |>

Rule30PrizeStatus[id_String] := Block[{e = storeEntry[id], who = submitterID[]},
    If[ MissingQ[e] || ! StringQ[who] || (who =!= e["submitter"] && ! reviewerQ[who]),
        Return[failure["NoEntry", "No submission " <> id <> " from this Wolfram ID."], Block]
    ];
    statusView[e]
]

Rule30PrizeStatus[] := Block[{who = submitterID[]},
    If[ ! StringQ[who], Return[failure["WolframID", "Ask with the Wolfram ID that submitted."], Block]];
    <|"submitter" -> who, "submissions" -> statusView /@ ReverseSortBy[Select[Values @ storeIndex[], #["submitter"] === who&], #submittedUnix&]|>
]

(* === the submissions page, for reviewers === *)

statusRank[s_String] := Replace[FirstPosition[$Rule30PrizeStatuses, s, {0}], {i_} :> i]

pageEntry[e_Association] := Append[KeyDrop[e, {"hidden", "hiddenReason", "submittedUnix"}], "statusRank" -> statusRank[e["status"]]]

Rule30PrizeEntries[] := SortBy[
    pageEntry /@ Select[Values @ storeIndex[], ! TrueQ[#hidden]&],
    {-#statusRank&, If[#claim === "partial", 1, 0]&, #submitted&}
]

Rule30PrizeEntry[id_String] := Replace[storeEntry[id], {e_Association :> pageEntry[e], _ -> failure["NoEntry", "No submission " <> id <> "."]}]

submissionsData[entries_List] := <|
    "updated" -> isoTime[nowUnix[]],
    "kit" -> $kitVersion,
    "statuses" -> $Rule30PrizeStatuses,
    "problems" -> KeyMap[ToString, $problems],
    "links" -> <|
        "json" -> endpointURL["submissions.json"],
        "skill" -> endpointURL["skill.md"],
        "start" -> endpointURL["HowToStart.nb"],
        "rules" -> "https://rule30prize.org/"
    |>,
    "entries" -> entries
|>

Rule30PrizeSubmissionsPage[] := StringReplace[ByteArrayToString[$submissionsTemplateBytes, "UTF-8"], "\"__RULE30_DATA__\"" -> scriptJSON[submissionsData[Rule30PrizeEntries[]]]]

(* === the verifier's side === *)

(* Waiting for the verifier: queued, or claimed by a run that has been silent for too long. *)
waitingQ[e_Association] := ! TrueQ[e["hidden"]] && Replace[e["check"]["state"], {
    "queued" -> True,
    "running" :> nowUnix[] - Replace[e["check"]["startedUnix"], Except[_Integer] -> 0] > $staleRunSeconds,
    _ -> False
}]

queueItem[e_Association] := <|
    "id" -> e["id"],
    "problem" -> e["problem"],
    "claim" -> e["claim"],
    "target" -> e["target"],
    "headlines" -> e["headlines"],
    "notebookSHA256" -> e["notebookSHA256"],
    "notebookBase64" -> BaseEncode @ Replace[storeReadBytes[e["id"], "essay.nb"], Except[_ByteArray] -> ByteArray[{}]]
|>

Rule30PrizeQueue[n_Integer : 10] := queueItem /@ Take[SortBy[Select[Values @ storeIndex[], waitingQ], #submittedUnix&], UpTo[n]]

Rule30PrizeQueueItem[id_String] := Replace[storeEntry[id], {e_Association /; waitingQ[e] :> queueItem[e], _ -> Missing["NotWaiting", id]}]

Rule30PrizeClaimCheck[id_String] := Block[{e = storeEntry[id]},
    If[ ! AssociationQ[e] || ! waitingQ[e], Return[False, Block]];
    storeSetEntry[id, Join[e, <|"check" -> <|"state" -> "running", "detail" -> "The Lean verifier is checking it.", "startedUnix" -> nowUnix[]|>|>]];
    True
]

(* What the verifier is doing, shown as the check's detail while it runs. *)
Rule30PrizeProgress[id_String, detail_String] := Block[{e = storeEntry[id]},
    If[ AssociationQ[e] && e["check"]["state"] === "running",
        storeSetEntry[id, Join[e, <|"check" -> Join[e["check"], <|"detail" -> detail, "progressUnix" -> nowUnix[]|>]|>]]
    ];
]

(* The verifier's JSON, cut down to what the page shows. *)
checkSummary[r_Association] := <|
    "verdict" -> Replace[r["verdict"], Except["pass" | "fail" | "error"] -> "error"],
    "reasons" -> Take[Select[Replace[r["reasons"], Except[_List] -> {}], StringQ], UpTo[10]],
    "verifiedTargets" -> Select[Replace[r["verifiedTargets"], Except[_List] -> {}], StringQ],
    "headlines" -> Take[Select[Replace[r["headlines"], Except[_List] -> {}], AssociationQ], UpTo[20]],
    "official" -> Take[Select[Replace[r["official"], Except[_List] -> {}], AssociationQ], UpTo[4]],
    "replay" -> Replace[r["replay"], Except[_Association] -> Null],
    "newAxioms" -> Select[Replace[r["newAxioms"], Except[_List] -> {}], StringQ],
    "lean" -> Replace[r["lean"], Except[_String] -> Null],
    "kitCommit" -> Replace[r["kitCommit"], Except[_String] -> Null],
    "verifier" -> Replace[r["verifier"], Except[_String] -> Null],
    "log" -> Replace[r["log"], {s_String :> StringTake[s, UpTo[4000]], _ -> Null}]
|>

checkDetail[s_Association] := Which[
    s["verdict"] === "pass", "Kernel replay passed; standard axioms only.",
    s["reasons"] =!= {}, StringRiffle[s["reasons"], "; "],
    True, "The check failed."
]

(* sha is the SHA-256 of the notebook the verifier evaluated. The result may carry the Lean source
   behind its rule30Submission, which reviewers then read. *)
Rule30PrizeRecordCheck[id_String, sha_String, result_Association] := Block[{e = storeEntry[id], s, passed, status, source},
    If[MissingQ[e], Return[failure["NoEntry", "No submission " <> id <> "."], Block]];
    If[e["notebookSHA256"] =!= sha, Return[failure["Stale", "The notebook hash does not match this submission."], Block]];
    source = Replace[result["source"], {b_ByteArray :> b, t_String :> utf8[t], _ -> None}];
    If[ ByteArrayQ[source] && Length[source] <= $maxSourceBytes,
        storeBytes[id, "Rule30Submission.lean", source];
        e = Join[e, <|"sourceSHA256" -> sha256[source], "sourceBytes" -> Length[source],
            "files" -> Append[e["files"], "lean" -> endpointURL["api/file"] <> "?id=" <> id <> "&kind=lean"]|>]
    ];
    s = checkSummary[result];
    passed = s["verdict"] === "pass";
    status = Which[
        statusRank[e["status"]] >= 3, e["status"],
        passed, "Lean Verified",
        True, "Lean Unverified"
    ];
    e = Join[e, <|"status" -> status, "check" -> Join[s, <|"state" -> If[passed, "passed", If[s["verdict"] === "error", "error", "failed"]], "detail" -> checkDetail[s], "checkedAt" -> isoTime[nowUnix[]]|>]|>];
    storeSetEntry[id, e];
    <|"ok" -> True, "id" -> id, "status" -> status|>
]

(* === administration, from the owner's kernel === *)

Rule30PrizeSetStatus[id_String, status_String, note_String : ""] := Block[{e = storeEntry[id]},
    Which[
        MissingQ[e], failure["NoEntry", "No submission " <> id <> "."],
        ! MemberQ[$Rule30PrizeStatuses, status], failure["Status", "The status must be one of " <> StringRiffle[$Rule30PrizeStatuses, ", "] <> "."],
        True,
            storeSetEntry[id, Join[e, <|"status" -> status, "review" -> <|"status" -> status, "note" -> nullIfEmpty[note], "at" -> isoTime[nowUnix[]]|>|>]];
            Rule30PrizeEntry[id]
    ]
]

Rule30PrizeRequeue[id_String] := Block[{e = storeEntry[id]},
    If[MissingQ[e], Return[failure["NoEntry", "No submission " <> id <> "."], Block]];
    If[e["notebookSHA256"] === Null, Return[failure["NoNotebook", "The submission has no notebook."], Block]];
    storeSetEntry[id, Join[e, <|"check" -> <|"state" -> "queued", "detail" -> "Waiting for the Lean verifier."|>|>]];
    Rule30PrizeEntry[id]
]

Rule30PrizeHide[id_String, reason : (_String | False)] := Block[{e = storeEntry[id]},
    If[MissingQ[e], Return[failure["NoEntry", "No submission " <> id <> "."], Block]];
    storeSetEntry[id, Join[e, <|"hidden" -> reason =!= False, "hiddenReason" -> Replace[reason, False -> Null]|>]];
    Rule30PrizeEntry[id]
]

Rule30PrizeContact[id_String] := storePrivate[id]

(* === the deployed endpoints === *)

jsonResponse[expr_, code_Integer : 200] := HTTPResponse[utf8 @ asciiJSON @ ExportString[expr, "RawJSON"], <|"StatusCode" -> code, "ContentType" -> "application/json; charset=utf-8"|>]

failureJSON[f_Failure] := <|"ok" -> False, "error" -> f[[1]], "message" -> f["Message"]|>

forbidden[] := HTTPResponse[utf8["Only Wolfram IDs at " <> StringRiffle[$Rule30PrizeReviewerDomains, " or "] <> " can read the Rule 30 Prize submissions."], <|"StatusCode" -> 403, "ContentType" -> "text/plain; charset=utf-8"|>]

(* Evaluate body only for a reviewer. Deployed with "Authenticated" permissions, so every
   request carries a Wolfram ID. *)
SetAttributes[forReviewers, HoldFirst]

forReviewers[body_] := If[reviewerQ[$RequesterWolframID], body, forbidden[]]

(* The parameters of the submission API. The notebook is an uploaded file, or notebookURL to fetch it from. *)
$apiFields = {
    "notebook" -> <|"Interpreter" -> "CachedFile", "Required" -> False, "Help" -> "the computational essay (.nb), uploaded"|>,
    "notebookURL" -> <|"Interpreter" -> "String", "Required" -> False, "Help" -> "an https URL of the .nb file, instead of uploading it"|>,
    "problem" -> <|"Interpreter" -> Restricted["Integer", {1, 3}], "Help" -> "1, 2 or 3"|>,
    "claim" -> <|"Interpreter" -> {"proof", "disproof", "partial"}, "Help" -> "proof, disproof or partial"|>,
    "title" -> <|"Interpreter" -> "String"|>,
    "authors" -> <|"Interpreter" -> "String", "Help" -> "every contributor, people and agents"|>,
    "agent" -> <|"Interpreter" -> "String", "Help" -> "the agent and model that made the submission"|>,
    "consent" -> <|"Interpreter" -> "Boolean", "Help" -> "true: the human behind the agent agrees to submit the notebook and these details"|>,
    "headlines" -> <|"Interpreter" -> "String", "Required" -> False, "Help" -> "theorem names, for partial results and Problem 3"|>,
    "abstract" -> <|"Interpreter" -> "String", "Required" -> False|>,
    "repository" -> <|"Interpreter" -> "String", "Required" -> False|>,
    "supersedes" -> <|"Interpreter" -> "String", "Required" -> False, "Help" -> "the id of an earlier submission this one replaces"|>
}

fileResponse[id_String, kind_String] := Block[{e = If[StringMatchQ[id, $idPattern], storeEntry[id], Missing[]]},
    Which[
        MissingQ[e], HTTPResponse["Not found", <|"StatusCode" -> 404|>],
        kind === "notebook", HTTPResponse[storeReadBytes[id, "essay.nb"], <|"ContentType" -> "application/vnd.wolfram.notebook", "Headers" -> {"Content-Disposition" -> "attachment; filename=\"" <> id <> ".nb\""}|>],
        kind === "lean" && StringQ[e["sourceSHA256"]], HTTPResponse[storeReadBytes[id, "Rule30Submission.lean"], <|"ContentType" -> "text/plain; charset=utf-8"|>],
        True, HTTPResponse["Not found", <|"StatusCode" -> 404|>]
    ]
]

(* Point this kernel at the deployment under root, creating its stores the first time. The owner's
   kernel does this to administer the submissions and to run the verifier. *)
Rule30PrizeAttach[root_String : $Rule30PrizeRoot] := Block[{ce},
    If[ ! $CloudConnected, Return[failure["Cloud", "Connect to the Wolfram Cloud first (CloudConnect)."], Block]];
    (* PartProtection -> None: by default a cloud expression silently refuses to replace an existing
       key, which would freeze every entry at its first value. *)
    ce[name_] := With[{c = Replace[Quiet @ CreateCloudExpression[<||>, root <> "/" <> name, Permissions -> "Private", PartProtection -> None], _Failure | $Failed :> CloudExpression[root <> "/" <> name]]},
        Quiet @ SetOptions[c, PartProtection -> None];
        c
    ];
    $Rule30PrizeStore = "Cloud";
    $rootURL = First @ CloudObject[root];
    $indexCE = ce["index"];
    $privateCE = ce["private"];
    $rateCE = ce["rate"];
    $rootURL
]

$reviewerPermissions = {"Authenticated" -> {"Read", "Execute"}}

(* The submission and status APIs: any signed-in Wolfram ID, with or without a subscription. The
   code runs as the owner, on the owner's credits. *)
$submitterPermissions = {"Authenticated" -> {"Read", "Execute"}}

Options[Rule30PrizeDeploy] = {"SkillFile" -> None, "Root" -> Automatic}

Rule30PrizeDeploy[opts : OptionsPattern[]] := Block[{attached, urls},
    attached = Rule30PrizeAttach[Replace[OptionValue["Root"], Automatic -> $Rule30PrizeRoot]];
    If[FailureQ[attached], Return[attached, Block]];
    urls = <|
        "api/submit" -> CloudDeploy[APIFunction[$apiFields, Replace[Rule30PrizeSubmit[#], {r_Association :> jsonResponse[r], f_Failure :> jsonResponse[failureJSON[f], 400]}]&], CloudObject[$rootURL <> "/api/submit"], Permissions -> $submitterPermissions],
        "api/status" -> CloudDeploy[APIFunction[{"id" -> <|"Interpreter" -> "String", "Required" -> False|>},
            Replace[If[StringQ[Lookup[#, "id", None]] && #id =!= "", Rule30PrizeStatus[#id], Rule30PrizeStatus[]], {r_Association :> jsonResponse[r], f_Failure :> jsonResponse[failureJSON[f], 404]}]&],
            CloudObject[$rootURL <> "/api/status"], Permissions -> $submitterPermissions],
        "submissions" -> CloudDeploy[Delayed[forReviewers[HTTPResponse[utf8 @ Rule30PrizeSubmissionsPage[], <|"ContentType" -> "text/html; charset=utf-8"|>]]], CloudObject[$rootURL <> "/submissions"], Permissions -> $reviewerPermissions],
        "submissions.json" -> CloudDeploy[Delayed[forReviewers[jsonResponse[submissionsData[Rule30PrizeEntries[]]]]], CloudObject[$rootURL <> "/submissions.json"], Permissions -> $reviewerPermissions],
        "api/file" -> CloudDeploy[APIFunction[{"id" -> "String", "kind" -> "String"}, forReviewers[fileResponse[#id, #kind]]&], CloudObject[$rootURL <> "/api/file"], Permissions -> $reviewerPermissions]
    |>;
    (* skill.md is public and names the deployment as {{ROOT}}. deploy.wls publishes the other
       public pages: the landing page and the starter notebook. *)
    If[StringQ[OptionValue["SkillFile"]], urls["skill.md"] = publishText["skill.md", StringReplace[Import[OptionValue["SkillFile"], "Text", CharacterEncoding -> "UTF-8"], "{{ROOT}}" -> $rootURL], "text/plain; charset=utf-8"]];
    Map[First, urls]
]

End[]

EndPackage[]
