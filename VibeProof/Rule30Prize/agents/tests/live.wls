#!/usr/bin/env wolframscript
(* ::Package:: *)

(* live.wls - check a deployment end to end. Run it as the owner after deploy.wls:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute tests/live.wls [-root Rule30Prize] [-submit true] [-fakes false] [-wait 600]

   - The public pages answer anonymous requests: ROOT/ (the landing page), skill.md and HowToStart.nb.
   - The reviewers' page answers this account and sends anonymous requests to the login page.
   - With -submit true (the default), it submits the kit's template as a partial result, the way
     skill.md tells agents to, and expects Lean Verified.
   - With -fakes true, it then sends what a cheating agent might: four fake proofs of Problem 1,
     each caught at a different stage (the build, the kernel replay, the statement and the
     axioms). Each must come back failed, Lean Unverified, for the expected reason.

   It sends one submission at a time, waits up to -wait seconds for the verifier and hides the
   submission again. Each one starts a verification on Prime Intellect (two sandboxes, about a
   minute), and the API takes at most 5 submissions an hour from one address: -fakes true with
   -submit true uses all 5. *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "..", "cloud", "Rule30PrizeSite.wl"}]]

(* Under run-as.wls the command line starts with the account: take what follows this script. *)
args = Replace[$ScriptCommandLine, {{___, s_String /; StringEndsQ[s, "live.wls"], rest___} :> {rest}, l_List :> Rest[l]}]

option[name_String, default_] := Replace[SequenceCases[args, {"-" <> name, v_} :> v], {{v_, ___} :> v, {} -> default}]

root = option["root", "Rule30Prize"]

rootURL = First @ CloudObject[root]

kit = FileNameJoin[{DirectoryName[$InputFileName], "..", "..", "kit"}]

(* The template agents start from, and the kit's tests. *)
template = Import[FileNameJoin[{kit, "Rule30Submission.lean"}], "Text", CharacterEncoding -> "UTF-8"]

kitTest[name_String] := Import[FileNameJoin[{kit, "tests", name <> ".lean"}], "Text", CharacterEncoding -> "UTF-8"]

failures = 0

check[label_String, ok_, detail_ : ""] := (
    Print[If[TrueQ[ok], "ok    ", failures++; "FAIL  "], label, If[detail === "", "", ": " <> ToString[detail]]];
    TrueQ[ok]
)

(* A request without this kernel's cloud credentials, as an agent makes it. *)
anonymous[url_String, follow_ : True] := URLRead[HTTPRequest[url], {"StatusCode", "Body"}, FollowRedirects -> follow, Authentication -> None]

(* Submit a notebook whose rule30Submission cell holds source, as skill.md shows agents, wait for
   the verifier, hide the submission and give its status, or a string saying what went wrong. *)
submission[title_String, source_String, fields_List] := Block[{file, response, status = None, state = None, start = AbsoluteTime[]},
    file = FileNameJoin[{$TemporaryDirectory, "rule30prize-live-" <> CreateUUID[] <> ".nb"}];
    Export[file, Notebook[{
        Cell[title, "Title"],
        Cell["Submitted by agents/tests/live.wls.", "Text"],
        With[{s = source}, Cell[BoxData[MakeBoxes[rule30Submission = LeanImportString[s, "ProjectDir" -> $Rule30PrizeKit], StandardForm]], "Input"]]
    }], "NB"];
    response = Quiet @ URLExecute[
        HTTPRequest[rootURL <> "/api/submit", <|"Method" -> "POST", "Body" -> Join[
            {"notebook" -> File[file], "problem" -> "1", "title" -> "Live test: " <> title, "authors" -> "The Rule 30 Prize maintainers",
             "agent" -> "agents/tests/live.wls", "consent" -> "true"},
            fields
        ]|>],
        "RawJSON"
    ];
    DeleteFile[file];
    If[ ! AssociationQ[response] || ! TrueQ[response["ok"]],
        Return["not accepted: " <> If[AssociationQ[response], ToString[Lookup[response, "message", response]], ToString[response]], Block]
    ];
    Print["      ", title, ": ", response["id"]];
    While[AbsoluteTime[] - start < FromDigits[option["wait", "600"]] && ! MemberQ[{"passed", "failed", "error", "no-source", "no-target"}, state],
        Pause[15];
        status = Quiet @ URLExecute[response["statusURL"], "RawJSON"];
        If[ AssociationQ[status] && status["check"]["state"] =!= state,
            state = status["check"]["state"];
            Print["      ", Round[AbsoluteTime[] - start], " s: ", state]
        ]
    ];
    If[ FailureQ[Rule30PrizeHide[response["id"], "live test (agents/tests/live.wls)"]],
        Print["      could not hide ", response["id"], ": run admin.wls hide ", response["id"], " as the owner"]
    ];
    If[AssociationQ[status], status, "no status from the verifier"]
]

(* Whether the verifier failed the submission, as opposed to the infrastructure, with reason among
   the reasons it gives and the problems it found in the theorems. *)
rejectedFor[status_Association, reason_String] := status["check"]["state"] === "failed" && status["status"] === "Lean Unverified" &&
    StringContainsQ[ToString[Lookup[status["check"], {"reasons", "official", "headlines"}], InputForm], reason]

rejectedFor[___] := False

(* The fake proofs: each claims Problem 1 and must fail for its reason. *)
fakes = {
    {"a proof that does not compile", "import Rule30PrizeKit\n\nnamespace Rule30Submission\n\nopen Ruliology.CellularAutomata.Rule30Prize\n\ntheorem problem1 : Problem1 := by decide\n\nend Rule30Submission\n",
        "the Lean source does not compile"},
    {"a theorem added without the kernel", kitTest["T05SkipKernel"], "kernel replay failed"},
    {"a Problem1 of its own", kitTest["T07Redefine"], "does not import Ruliology.CellularAutomata.Rule30Prize"},
    {"sorry", kitTest["T02Sorry"], "uses non-standard axioms: [sorryAx]"}
}

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

If[ (option["submit", "true"] === "true" || option["fakes", "false"] === "true") && FailureQ[Rule30PrizeAttach[root]],
    Print["connect as the owner of ", root, ", so that the test submissions can be hidden again"]; Exit[1]
]

genuine = If[ option["submit", "true"] === "true",
    With[{status = submission["the kit's template", template, {"claim" -> "partial", "headlines" -> "Rule30Submission.no_period_one"}]},
        check["the verifier passes the kit's template", AssociationQ[status] && status["check"]["state"] === "passed" && status["status"] === "Lean Verified",
            If[AssociationQ[status], {status["status"], status["check"]["state"], status["check"]["reasons"]}, status]]
    ],
    True
]

If[ option["fakes", "false"] === "true",
    If[ ! genuine, Print["skipping the fake proofs: the template did not verify"],
        Scan[
            Function[fake, With[{status = submission[fake[[1]], fake[[2]], {"claim" -> "proof"}]},
                check["a fake proof is rejected, " <> fake[[1]], rejectedFor[status, fake[[3]]],
                    If[AssociationQ[status], {status["status"], status["check"]["state"], status["check"]["reasons"]}, status]]
            ]],
            fakes
        ]
    ]
]

Print[If[failures === 0, "all checks passed", ToString[failures] <> " checks failed"]]

Exit[If[failures === 0, 0, 1]]
