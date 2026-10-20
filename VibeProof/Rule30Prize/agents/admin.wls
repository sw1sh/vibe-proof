#!/usr/bin/env wolframscript
(* ::Package:: *)

(* admin.wls - administer the submissions deployed under ROOT. Run it as the owner:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute admin.wls COMMAND [ID ...] [-root ROOT] [-note TEXT]

   Commands:
   - list                         the entries of the submissions page, best first (hidden ones are left out)
   - show ID                      one entry
   - contact ID                   its private contact details
   - status ID STATUS [-note T]   set its status: "Lean Unverified", "Lean Verified", "Human Verified" or "Prize Claimed"
   - requeue ID                   send it back to the Lean verifier; verifier/verify.wls then checks it
   - verify ID                    check a waiting submission in the cloud, as the submission API does
                                  for a new one, and follow it until it has a result
   - view ID ...                  deploy a view of each notebook for reviewers, without the parts
                                  that run code (new submissions get one automatically)
   - hide ID ... [-note REASON]   hide submissions from the page
   - unhide ID                    show a hidden submission again
   - undeploy -root ROOT          delete a test deployment, whose ROOT starts with Rule30PrizeTest: its
                                  objects and its three cloud expressions

   -root defaults to Rule30Prize. *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "cloud", "Rule30PrizeSite.wl"}]]

Get[FileNameJoin[{DirectoryName[$InputFileName], "verifier", "Rule30PrizeVerifier.wl"}]]

(* Under run-as.wls the command line starts with the account: take what follows this script. *)
args = Replace[$ScriptCommandLine, {{___, s_String /; StringEndsQ[s, "admin.wls"], rest___} :> {rest}, l_List :> Rest[l]}]

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

(* The arguments that are neither options nor their values. *)
words = Block[{a = args, out = {}},
    While[a =!= {}, If[StringStartsQ[First[a], "-"], a = Drop[a, UpTo[2]], AppendTo[out, First[a]]; a = Rest[a]]];
    out
]

root = option["root", "Rule30Prize"]

note = option["note", ""]

show[r_] := (
    Print[If[FailureQ[r], "failed: " <> r["Message"], Replace[Quiet @ ExportString[r, "RawJSON"], Except[_String] :> ToString[r, InputForm]]]];
    ! FailureQ[r]
)

entryLine[e_Association] := StringRiffle[
    {e["id"], e["status"], Lookup[Replace[e["check"], Except[_Association] -> <||>], "state", "-"], "problem " <> ToString[e["problem"]], e["claim"], StringTake[ToString[e["title"]], UpTo[60]]},
    "  "
]

(* The cloud task the submission API starts, then its progress every 20 s, for up to 40 minutes. *)
verifyInCloud[id_String] := Block[{e = Rule30PrizeEntry[id], seen = None, now, deadline = AbsoluteTime[] + 2400},
    If[FailureQ[e], Return[show[e], Block]];
    If[ MissingQ[Rule30PrizeQueueItem[id]], Print["not waiting for the verifier (", e["check"]["state"], ", or hidden): requeue or unhide it first"]; Return[False, Block]];
    Rule30PrizeCloudAccess[First[CloudObject[root]]];
    CloudSubmit[Rule30PrizeVerifyID[id]];
    While[ AbsoluteTime[] < deadline,
        Pause[20];
        e = Rule30PrizeEntry[id];
        now = {e["check"]["state"], e["check"]["detail"]};
        If[now =!= seen, seen = now; Print[DateString["Time"], "  ", StringRiffle[now, ": "]]];
        If[ ! MemberQ[{"queued", "running"}, First[now]], Break[]]
    ];
    show[e]
]

undeploy[r_String] := If[ ! StringStartsQ[r, "Rule30PrizeTest"],
    Print["undeploy deletes only test deployments, whose root starts with Rule30PrizeTest"]; False,
    Print["deleting ", r, ": ", Quiet @ DeleteDirectory[CloudObject[r], DeleteContents -> True]];
    Scan[Print[r <> "/" <> # <> ": ", Quiet @ DeleteCloudExpression[CloudExpression[r <> "/" <> #]]]&, {"index", "private", "rate"}];
    True
]

Print["as ", $WolframID, " on ", root]

If[ words =!= {"undeploy"},
    With[{attached = Rule30PrizeAttach[root]}, If[FailureQ[attached], Print[attached["Message"]]; Exit[1]]]
]

ok = Replace[words, {
    {"list"} :> (Scan[Print @* entryLine, Rule30PrizeEntries[]]; True),
    {"show", id_} :> show[Rule30PrizeEntry[id]],
    {"contact", id_} :> show[Rule30PrizeContact[id]],
    {"status", id_, status_} :> show[Rule30PrizeSetStatus[id, status, note]],
    {"requeue", id_} :> show[Rule30PrizeRequeue[id]],
    {"verify", id_} :> verifyInCloud[id],
    {"view", ids__} :> And @@ Map[show[Rule30PrizeDeployView[#]]&, {ids}],
    {"hide", ids__} :> And @@ Map[show[Rule30PrizeHide[#, If[note === "", "hidden by a maintainer", note]]]&, {ids}],
    {"unhide", id_} :> show[Rule30PrizeHide[id, False]],
    {"undeploy"} :> undeploy[root],
    _ :> (Print["unknown command: ", StringRiffle[words, " "], "; the comment at the top of admin.wls lists the commands"]; False)
}]

Exit[If[TrueQ[ok], 0, 1]]
