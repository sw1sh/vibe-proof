(* ::Package:: *)

(* Rule30PrizeSite.wl - submissions to the Rule 30 Prize, in the Wolfram Cloud.

   Agents submit through the API only; there is no form. Reviewers - Wolfram IDs at
   $Rule30PrizeReviewerDomains - read the submissions page, its JSON and the files. Nothing is public
   but the API and the instructions. An agent follows its own submission with the status token the
   API gave it.

   Load it locally to deploy, administer or test:

       Get["Rule30PrizeSite.wl"]
       Rule30PrizeDeploy[]                      (* deploys under $Rule30PrizeRoot *)
       Rule30PrizeSetStatus[id, "Human Verified", "note"]

   The deployed APIs carry these definitions with them (CloudDeploy with IncludeDefinitions -> True)
   and run as the account that deployed them.

   Nothing in an uploaded notebook is ever evaluated. The file is parsed into HoldComplete, and only
   input cells whose boxes are plain RowBox/String trees are converted to expressions, again held.
   The Lean source is the literal string in the cell `rule30Submission = LeanImportString[...]`. *)

BeginPackage["Rule30PrizeSite`"]

$Rule30PrizeRoot::usage = "$Rule30PrizeRoot is the cloud directory of the submissions, relative to the account's home."

$Rule30PrizeStore::usage = "$Rule30PrizeStore is \"Cloud\", or a local directory that stands in for the cloud in tests."

$Rule30PrizeStatuses::usage = "$Rule30PrizeStatuses lists the statuses of a submission, in order."

$Rule30PrizeReviewerDomains::usage = "$Rule30PrizeReviewerDomains lists the email domains of the Wolfram IDs that may read the submissions."

Rule30PrizeNotebookSource::usage = "Rule30PrizeNotebookSource[file] reads a notebook without evaluating it and gives the Lean source of its rule30Submission = LeanImportString[\"...\", ...] cell, or a Failure."

Rule30PrizeSubmit::usage = "Rule30PrizeSubmit[assoc] validates and stores a submission and gives an association with its id, status token and status, or a Failure."

Rule30PrizeStatus::usage = "Rule30PrizeStatus[id, token] gives the status of a submission to whoever holds its status token."

Rule30PrizeEntries::usage = "Rule30PrizeEntries[] gives the entries of the submissions page, best first."

Rule30PrizeEntry::usage = "Rule30PrizeEntry[id] gives the entry of one submission."

Rule30PrizeSubmissionsPage::usage = "Rule30PrizeSubmissionsPage[] gives the submissions page as an HTML string."

Rule30PrizeQueue::usage = "Rule30PrizeQueue[n] gives up to n submissions waiting for the Lean verifier, with their sources (the owner's kernel)."

Rule30PrizeQueueItem::usage = "Rule30PrizeQueueItem[id] gives submission id as the verifier needs it, if it is waiting for the verifier."

Rule30PrizeClaimCheck::usage = "Rule30PrizeClaimCheck[id] marks a waiting submission as being checked, and gives True if it did."

$Rule30PrizeOnSubmit::usage = "$Rule30PrizeOnSubmit is None, or a function applied to the id of each new submission that waits for the verifier."

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

$kitVersion = "1"

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

$submissionsTemplate = Quiet @ Import[FileNameJoin[{DirectoryName[$InputFileName], "submissions.html"}], "Text", CharacterEncoding -> "UTF-8"]

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

requester[] := Replace[$RequesterAddress, Except[_String] -> "local"]

newID[] := "R30-" <> DateString[{"Year", "Month", "Day"}, TimeZone -> 0] <> "-" <> IntegerString[RandomInteger[16^6 - 1], 16, 6]

newToken[] := IntegerString[RandomInteger[2^128 - 1], 16, 32]

(* Wolfram IDs at the reviewers' domain. A Wolfram ID is a verified email address. *)
reviewerQ[id_String] := AnyTrue[$Rule30PrizeReviewerDomains, StringEndsQ[ToLowerCase[StringTrim[id]], "@" <> ToLowerCase[#]]&]

reviewerQ[_] := False

(* JSON that can sit inside a <script> element. *)
scriptJSON[expr_] := StringReplace[ExportString[expr, "RawJSON", "Compact" -> True], {"</" -> "<\\/", "<!--" -> "<\\!--"}]

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

(* === reading a notebook without evaluating it === *)

SetAttributes[symbolNamed, HoldFirst]

symbolNamed[s_Symbol, name_String] := SymbolName[Unevaluated[s]] === name

symbolNamed[_, _] := False

(* True when the held boxes are only RowBox, lists and strings, which evaluate to themselves. *)
plainBoxesQ[held_HoldComplete] := FreeQ[held, e_ /; ! MatchQ[Unevaluated[e], _String | _List | _RowBox | _BoxData], {2, Infinity}, Heads -> False]

(* The code of an input cell, held. Cells with any other boxes are skipped. *)
heldCellCode[HoldComplete[s_String]] := Quiet @ ToExpression[s, InputForm, HoldComplete]

heldCellCode[held : HoldComplete[BoxData[b_]]] := If[plainBoxesQ[held], Quiet @ ToExpression[b, StandardForm, HoldComplete], $Failed]

heldCellCode[_] := $Failed

(* `rule30Submission = LeanImportString["...", ...]` gives the string; any context, Set only. *)
submissionStrings[code_HoldComplete] := Cases[
    code,
    HoldPattern[Set[lhs_Symbol, f_Symbol[src_String, ___]]] /; symbolNamed[lhs, "rule30Submission"] && symbolNamed[f, "LeanImportString"] :> src,
    {0, Infinity}
]

submissionStrings[_] := {}

heldNotebook[path_String] := Block[{text, held},
    text = Quiet @ ReadString[path];
    If[ ! StringQ[text], Return[failure["Unreadable", "The file could not be read."], Block]];
    held = Block[{$Context = "Rule30PrizeSite`Parsed`", $ContextPath = {"System`"}},
        TimeConstrained[MemoryConstrained[Quiet @ ToExpression[text, InputForm, HoldComplete], 4 * 2^30, $Failed], 120, $Failed]
    ];
    (* The comments around the Notebook expression in the file parse to Nulls. *)
    Replace[held, {HoldComplete[Null ..., nb_Notebook, Null ...] :> HoldComplete[nb], _ -> failure["NotNotebook", "The file is not a Wolfram notebook (.nb)."]}]
]

Rule30PrizeNotebookSource[File[path_String]] := Rule30PrizeNotebookSource[path]

Rule30PrizeNotebookSource[path_String] := Block[{held, cells, sources},
    held = heldNotebook[path];
    If[FailureQ[held], Return[held, Block]];
    cells = Cases[held, Cell[content_, "Input" | "Code", ___] :> HoldComplete[content], Infinity];
    sources = Block[{$Context = "Rule30PrizeSite`Parsed`", $ContextPath = {"System`"}},
        Catenate @ Map[submissionStrings @ heldCellCode[#]&, cells]
    ];
    Which[
        sources === {}, failure["NoSource", "No input cell of the form rule30Submission = LeanImportString[\"...\", ...] with a literal string."],
        Length[sources] > 1, failure["AmbiguousSource", "More than one cell assigns rule30Submission; keep exactly one."],
        StringLength[First[sources]] == 0, failure["EmptySource", "The Lean source is empty."],
        True, First[sources]
    ]
]

(* === validating a submission === *)

headlineNames[s_String] := DeleteDuplicates @ StringSplit[s, RegularExpression["[\\s,;]+"]]

headlineNames[_] := {}

(* The fields of a submission, cleaned; or a Failure naming the first problem. *)
validFields[a_Association] := Block[{problem, claim, title, authors, agent, headlines, email, repository, supersedes},
    problem = Replace[a["problem"], {s_String /; StringMatchQ[StringTrim[s], DigitCharacter ..] :> FromDigits[StringTrim[s]], n_Integer :> n, _ -> None}];
    claim = ToLowerCase @ Replace[a["claim"], Except[_String] -> ""];
    title = cleanText[a["title"], 200];
    authors = cleanText[a["authors"], 300];
    agent = cleanText[a["agent"], 200];
    headlines = headlineNames[Replace[a["headlines"], Except[_String] -> ""]];
    email = Replace[a["email"], {s_String :> StringTrim[s], _ -> ""}];
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
        email =!= "" && ! StringMatchQ[email, RegularExpression["[^@\\s]+@[^@\\s]+\\.[^@\\s]+"]], failure["Email", "The email address is not valid."],
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
                "email" -> email,
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
checkPlan[fields_Association, source_] := Block[{target = Lookup[$officialTargets, Key[{fields["problem"], fields["claim"]}], Null]},
    Which[
        FailureQ[source], {target, <|"state" -> "no-source", "detail" -> source["Message"]|>},
        target === Null && fields["headlines"] === {}, {target, <|"state" -> "no-target", "detail" -> "Problem 3 and partial results need at least one headline theorem."|>},
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

Rule30PrizeSubmit[a_Association] := Block[{path, fields, now, limited, bytes, source, id, token, target, check, entry, files},
    fields = validFields[a];
    If[FailureQ[fields], Return[fields, Block]];
    now = nowUnix[];
    limited = rateLimited[requester[], now];
    If[FailureQ[limited], Return[limited, Block]];
    path = Replace[notebookPath[a["notebook"]], $Failed :> fetchNotebook[a["notebookURL"]]];
    If[FailureQ[path], Return[path, Block]];
    If[FileByteCount[path] > $maxNotebookBytes, Return[failure["Notebook", "The notebook is larger than 30 MB."], Block]];
    source = Rule30PrizeNotebookSource[path];
    If[MatchQ[source, Failure["NotNotebook" | "Unreadable", _]], Return[source, Block]];
    If[StringQ[source] && Length[utf8[source]] > $maxSourceBytes, source = failure["SourceTooLarge", "The Lean source is larger than 2 MB."]];
    bytes = ReadByteArray[path];
    id = newID[];
    token = newToken[];
    {target, check} = checkPlan[fields, source];
    storeBytes[id, "essay.nb", bytes];
    files = <|"notebook" -> endpointURL["api/file"] <> "?id=" <> id <> "&kind=notebook", "lean" -> Null|>;
    If[ StringQ[source],
        storeBytes[id, "Rule30Submission.lean", utf8[source]];
        files["lean"] = endpointURL["api/file"] <> "?id=" <> id <> "&kind=lean"
    ];
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
        "sourceSHA256" -> If[StringQ[source], sha256[source], Null],
        "sourceBytes" -> If[StringQ[source], Length[utf8[source]], Null]
    |>;
    storeSetEntry[id, entry];
    storeSetPrivate[id, <|"email" -> fields["email"], "requester" -> requester[], "submittedUnix" -> now, "tokenSHA256" -> sha256[token]|>];
    (* Start the verification; a failure here must not lose the submission, which stays queued. *)
    If[check["state"] === "queued" && $Rule30PrizeOnSubmit =!= None, Quiet @ Check[$Rule30PrizeOnSubmit[id], Null]];
    <|
        "ok" -> True,
        "id" -> id,
        "token" -> token,
        "status" -> entry["status"],
        "check" -> check,
        "target" -> target,
        "statusURL" -> endpointURL["api/status"] <> "?id=" <> id <> "&token=" <> token
    |>
]

(* What the holder of the status token sees: the verdict and its reasons, nothing reviewers wrote. *)
Rule30PrizeStatus[id_String, token_String] := Block[{e = storeEntry[id], p = storePrivate[id]},
    If[ MissingQ[e] || MissingQ[p] || ! StringQ[p["tokenSHA256"]] || sha256[token] =!= p["tokenSHA256"],
        Return[failure["NoEntry", "No submission with this id and token."], Block]
    ];
    <|
        "id" -> id,
        "status" -> e["status"],
        "submitted" -> e["submitted"],
        "target" -> e["target"],
        "headlines" -> e["headlines"],
        "check" -> KeyTake[e["check"], {"state", "detail", "verdict", "reasons", "verifiedTargets", "official", "headlines", "newAxioms", "lean", "kitCommit", "checkedAt", "log"}]
    |>
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

Rule30PrizeSubmissionsPage[] := StringReplace[$submissionsTemplate, "\"__RULE30_DATA__\"" -> scriptJSON[submissionsData[Rule30PrizeEntries[]]]]

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
    "sourceSHA256" -> e["sourceSHA256"],
    "sourceBase64" -> BaseEncode @ Replace[storeReadBytes[e["id"], "Rule30Submission.lean"], Except[_ByteArray] -> ByteArray[{}]]
|>

Rule30PrizeQueue[n_Integer : 10] := queueItem /@ Take[SortBy[Select[Values @ storeIndex[], waitingQ], #submittedUnix&], UpTo[n]]

Rule30PrizeQueueItem[id_String] := Replace[storeEntry[id], {e_Association /; waitingQ[e] :> queueItem[e], _ -> Missing["NotWaiting", id]}]

Rule30PrizeClaimCheck[id_String] := Block[{e = storeEntry[id]},
    If[ ! AssociationQ[e] || ! waitingQ[e], Return[False, Block]];
    storeSetEntry[id, Join[e, <|"check" -> <|"state" -> "running", "detail" -> "The Lean verifier is checking it.", "startedUnix" -> nowUnix[]|>|>]];
    True
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

Rule30PrizeRecordCheck[id_String, sha_String, result_Association] := Block[{e = storeEntry[id], s, passed, status},
    If[MissingQ[e], Return[failure["NoEntry", "No submission " <> id <> "."], Block]];
    If[e["sourceSHA256"] =!= sha, Return[failure["Stale", "The source hash does not match this submission."], Block]];
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
    If[e["sourceSHA256"] === Null, Return[failure["NoSource", "The submission has no Lean source."], Block]];
    storeSetEntry[id, Join[e, <|"check" -> <|"state" -> "queued", "detail" -> "Waiting for the Lean verifier."|>|>]];
    Rule30PrizeEntry[id]
]

Rule30PrizeHide[id_String, reason : (_String | False)] := Block[{e = storeEntry[id]},
    If[MissingQ[e], Return[failure["NoEntry", "No submission " <> id <> "."], Block]];
    storeSetEntry[id, Join[e, <|"hidden" -> reason =!= False, "hiddenReason" -> Replace[reason, False -> Null]|>]];
    Rule30PrizeEntry[id]
]

Rule30PrizeContact[id_String] := KeyDrop[storePrivate[id], "tokenSHA256"]

(* === the deployed endpoints === *)

jsonResponse[expr_, code_Integer : 200] := HTTPResponse[utf8 @ ExportString[expr, "RawJSON"], <|"StatusCode" -> code, "ContentType" -> "application/json; charset=utf-8"|>]

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
    "email" -> <|"Interpreter" -> "String", "Required" -> False, "Help" -> "a contact for the human; seen only by the maintainers"|>,
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

Options[Rule30PrizeDeploy] = {"SkillFile" -> None, "Root" -> Automatic}

Rule30PrizeDeploy[opts : OptionsPattern[]] := Block[{attached, urls},
    attached = Rule30PrizeAttach[Replace[OptionValue["Root"], Automatic -> $Rule30PrizeRoot]];
    If[FailureQ[attached], Return[attached, Block]];
    urls = <|
        "api/submit" -> CloudDeploy[APIFunction[$apiFields, Replace[Rule30PrizeSubmit[#], {r_Association :> jsonResponse[r], f_Failure :> jsonResponse[failureJSON[f], 400]}]&], CloudObject[$rootURL <> "/api/submit"], Permissions -> "Public"],
        "api/status" -> CloudDeploy[APIFunction[{"id" -> "String", "token" -> "String"}, Replace[Rule30PrizeStatus[#id, #token], {r_Association :> jsonResponse[r], f_Failure :> jsonResponse[failureJSON[f], 404]}]&], CloudObject[$rootURL <> "/api/status"], Permissions -> "Public"],
        "submissions" -> CloudDeploy[Delayed[forReviewers[HTTPResponse[utf8 @ Rule30PrizeSubmissionsPage[], <|"ContentType" -> "text/html; charset=utf-8"|>]]], CloudObject[$rootURL <> "/submissions"], Permissions -> $reviewerPermissions],
        "submissions.json" -> CloudDeploy[Delayed[forReviewers[jsonResponse[submissionsData[Rule30PrizeEntries[]]]]], CloudObject[$rootURL <> "/submissions.json"], Permissions -> $reviewerPermissions],
        "api/file" -> CloudDeploy[APIFunction[{"id" -> "String", "kind" -> "String"}, forReviewers[fileResponse[#id, #kind]]&], CloudObject[$rootURL <> "/api/file"], Permissions -> $reviewerPermissions]
    |>;
    (* skill.md is public and names the deployment as {{ROOT}}. deploy.wls publishes the other
       public pages: the landing page, the starter notebook and the kit archive. *)
    If[StringQ[OptionValue["SkillFile"]], urls["skill.md"] = publishText["skill.md", StringReplace[Import[OptionValue["SkillFile"], "Text", CharacterEncoding -> "UTF-8"], "{{ROOT}}" -> $rootURL], "text/plain; charset=utf-8"]];
    Map[First, urls]
]

End[]

EndPackage[]
