#!/usr/bin/env wolframscript
(* ::Package:: *)

(* live.wls - check a deployment end to end. Run it as the owner after deploy.wls:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute tests/live.wls [-root Rule30Prize] [-submit true] [-wait 600]

   - The public pages answer anonymous requests: ROOT/ (the landing page), skill.md and HowToStart.nb.
   - The reviewers' page answers this account and sends anonymous requests to the login page.
   - With -submit true (the default), it submits the kit's template as a partial result through the
     public API, waits up to -wait seconds for the verifier to report Lean Verified, and then hides
     the submission. That starts one verification on Prime Intellect: two sandboxes, about a
     minute and a half. *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "..", "cloud", "Rule30PrizeSite.wl"}]]

(* Under run-as.wls the command line starts with the account: take what follows this script. *)
args = Replace[$ScriptCommandLine, {{___, s_String /; StringEndsQ[s, "live.wls"], rest___} :> {rest}, l_List :> Rest[l]}]

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

root = option["root", "Rule30Prize"]

rootURL = First @ CloudObject[root]

kit = FileNameJoin[{DirectoryName[$InputFileName], "..", "..", "kit"}]

failures = 0

check[label_String, ok_, detail_ : ""] := (
    Print[If[TrueQ[ok], "ok    ", failures++; "FAIL  "], label, If[detail === "", "", ": " <> ToString[detail]]];
    TrueQ[ok]
)

(* A request without this kernel's cloud credentials, as an agent makes it. *)
anonymous[url_String, follow_ : True] := URLRead[HTTPRequest[url], {"StatusCode", "Body"}, FollowRedirects -> follow, Authentication -> None]

Print["as ", $WolframID, " on ", rootURL]

Block[{r},
    r = anonymous[rootURL <> "/"];
    check["the landing page", r["StatusCode"] === 200 && StringContainsQ[r["Body"], "skill.md"], r["StatusCode"]];
    r = anonymous[rootURL <> "/skill.md"];
    check["skill.md", r["StatusCode"] === 200 && StringContainsQ[r["Body"], rootURL <> "/api/submit"] && StringContainsQ[r["Body"], "https://github.com/WolframInstitute/Rule30PrizeKit"], r["StatusCode"]];
    r = anonymous[rootURL <> "/HowToStart.nb"];
    check["HowToStart.nb", r["StatusCode"] === 200, r["StatusCode"]];
    r = anonymous[rootURL <> "/submissions", False];
    check["the submissions page sends anonymous requests to log in", MatchQ[r["StatusCode"], 301 | 302 | 303 | 401 | 403], r["StatusCode"]];
    r = URLRead[CloudObject[rootURL <> "/submissions"], {"StatusCode", "Body"}];
    check["the submissions page answers " <> ToString[$WolframID], r["StatusCode"] === 200, r["StatusCode"]]
]

If[ option["submit", "true"] === "true",
    Block[{src, file, response, id, status = None, state = None, start = AbsoluteTime[], hidden},
        src = Import[FileNameJoin[{kit, "Rule30Submission.lean"}], "Text", CharacterEncoding -> "UTF-8"];
        file = FileNameJoin[{$TemporaryDirectory, "rule30prize-live-" <> CreateUUID[] <> ".nb"}];
        Export[file, Notebook[{
            Cell["Live test of the deployment", "Title"],
            Cell["The kit's template, submitted by agents/tests/live.wls.", "Text"],
            With[{s = src}, Cell[BoxData[MakeBoxes[rule30Submission = LeanImportString[s, "ProjectDir" -> $Rule30PrizeKit], StandardForm]], "Input"]]
        }], "NB"];
        response = Quiet @ URLExecute[
            HTTPRequest[rootURL <> "/api/submit", <|"Method" -> "POST", "Body" -> {
                "notebook" -> File[file], "problem" -> "1", "claim" -> "partial",
                "title" -> "Live test of the deployment", "authors" -> "The Rule 30 Prize maintainers",
                "agent" -> "agents/tests/live.wls", "headlines" -> "Rule30Submission.no_period_one", "consent" -> "true"
            }|>],
            "RawJSON"
        ];
        DeleteFile[file];
        If[ ! check["the submission is accepted", AssociationQ[response] && TrueQ[response["ok"]], If[AssociationQ[response], Lookup[response, "error", ""], response]],
            Exit[1]
        ];
        id = response["id"];
        Print["      ", id];
        While[AbsoluteTime[] - start < FromDigits[option["wait", "600"]] && ! MemberQ[{"passed", "failed"}, state],
            Pause[15];
            status = Quiet @ URLExecute[response["statusURL"], "RawJSON"];
            If[ AssociationQ[status] && status["check"]["state"] =!= state,
                state = status["check"]["state"];
                Print["      ", Round[AbsoluteTime[] - start], " s: ", state]
            ]
        ];
        check["the verifier passes it", state === "passed" && status["status"] === "Lean Verified",
            If[AssociationQ[status], {status["status"], state, Lookup[status["check"], "reasons", {}]}, status]];
        hidden = With[{attached = Rule30PrizeAttach[root]}, If[FailureQ[attached], attached, Rule30PrizeHide[id, "live test (agents/tests/live.wls)"]]];
        check["the test submission is hidden", AssociationQ[hidden],
            If[FailureQ[hidden], hidden["Message"] <> " Hide " <> id <> " as the owner: admin.wls hide " <> id, ""]]
    ]
]

Print[If[failures === 0, "all checks passed", ToString[failures] <> " checks failed"]]

Exit[If[failures === 0, 0, 1]]
