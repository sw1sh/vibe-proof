#!/usr/bin/env wolframscript
(* ::Package:: *)

(* submit.wls NOTEBOOK - submit a notebook to the Rule 30 Prize as this kernel's Wolfram ID, the way
   skill.md tells agents to, and follow its check:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls nikm tests/submit.wls essay.nb \
           -problem 1 -claim partial -title "..." -authors "..." [-headlines A,B] [-abstract TEXT] \
           [-root Rule30Prize] [-wait 900]

   The Wolfram ID the kernel is connected as is the submitter. The submission is real: it stays on
   the reviewers' page unless a maintainer hides it. *)

(* Under run-as.wls the command line starts with the account: take what follows this script. *)
args = Replace[$ScriptCommandLine, {{___, s_String /; StringEndsQ[s, "submit.wls"], rest___} :> {rest}, l_List :> Rest[l]}]

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

words = Block[{a = args, out = {}},
    While[a =!= {}, If[StringStartsQ[First[a], "-"], a = Drop[a, UpTo[2]], AppendTo[out, First[a]]; a = Rest[a]]];
    out
]

If[Length[words] =!= 1 || ! FileExistsQ[First[words]], Print["usage: submit.wls NOTEBOOK -problem N -claim C -title T -authors A ..."]; Exit[2]]

(* The owner's folder, spelled out: CloudObject["Rule30Prize"] would mean the submitter's own. *)
rootURL = "https://www.wolframcloud.com/obj/wolframinstitute/" <> option["root", "Rule30Prize"]

body = Join[
    {
        "notebook" -> File[ExpandFileName[First[words]]],
        "problem" -> option["problem", "1"],
        "claim" -> option["claim", "partial"],
        "title" -> option["title", FileBaseName[First[words]]],
        "authors" -> option["authors", ""],
        "agent" -> option["agent", "agents/tests/submit.wls"],
        "consent" -> "true"
    },
    Replace[option["headlines", None], {h_String :> {"headlines" -> h}, _ -> {}}],
    Replace[option["abstract", None], {t_String :> {"abstract" -> t}, _ -> {}}]
]

Print["as ", $WolframID, " to ", rootURL]

response = Quiet @ URLExecute[CloudObject[rootURL <> "/api/submit"], body, "RawJSON", Method -> "POST"]

If[ ! AssociationQ[response] || ! TrueQ[response["ok"]],
    Print["not accepted: ", If[AssociationQ[response], Lookup[response, "message", response], response]]; Exit[1]
]

Print[response["id"], " from ", response["submitter"], ": ", response["status"], ", ", response["check"]["state"], " (", response["check"]["detail"], ")"]

status = response; state = response["check"]["state"]; seen = None; start = AbsoluteTime[];

While[ MemberQ[{"queued", "running"}, state] && AbsoluteTime[] - start < FromDigits[option["wait", "900"]],
    Pause[15];
    status = Quiet @ URLExecute[CloudObject[rootURL <> "/api/status"], {"id" -> response["id"]}, "RawJSON"];
    If[ AssociationQ[status],
        state = status["check"]["state"];
        If[ {state, status["check"]["detail"]} =!= seen,
            seen = {state, status["check"]["detail"]};
            Print["  ", Round[AbsoluteTime[] - start], " s: ", state, ": ", status["check"]["detail"]]
        ]
    ]
]

Print[response["id"], ": ", status["status"], ", ", state, If[AssociationQ[status] && ListQ[status["check"]["reasons"]] && status["check"]["reasons"] =!= {}, " - " <> StringRiffle[status["check"]["reasons"], "; "], ""]]

Exit[If[MemberQ[{"passed", "no-target"}, state], 0, 1]]
