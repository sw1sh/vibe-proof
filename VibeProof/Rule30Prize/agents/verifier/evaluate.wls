#!/usr/bin/env wolframscript
(* ::Package:: *)

(* evaluate.wls NOTEBOOK OUT - evaluate a submitted notebook as its reader would, and save the Lean
   source of the environment its rule30Submission holds.

   The verifier runs this in the build sandbox, with a license that expires within the hour. Every
   input cell of NOTEBOOK is evaluated in this kernel, in order and without a front end, with the kit
   at RULE30PRIZE_KIT. Then OUT gets
   - result.json: whether rule30Submission is a LeanEnvironment, and what it is if not;
   - Rule30Submission.lean: the source LeanImportString made that environment from.

   A LeanEnvironment holds only handles into this kernel's Lean session, not its source, so this
   records the source of every environment LeanImportString returns. Whatever the notebook does to
   that record only changes which source the verifier then builds and checks, in a sandbox of its
   own. *)

(* Absolute paths: the front end resolves relative ones against its own folder. *)
{notebook, out} = ExpandFileName /@ Take[$ScriptCommandLine, -2];

Quiet @ CreateDirectory[out];

writeResult[result_Association] := Export[FileNameJoin[{out, "result.json"}], result, "RawJSON"];

Needs["Wolfram`LeanLink`"];

If[ ! MemberQ[$Packages, "Wolfram`LeanLink`"], writeResult[<|"ok" -> False, "message" -> "LeanLink did not load in the verifier."|>]; Exit[1]];

(* The source of each environment LeanImportString made, and what LeanLink said the last time. *)
Rule30Evaluate`sources = <||>;

Rule30Evaluate`said = {};

Rule30Evaluate`record[data_Association, args_List] := With[{env = data["Result"]},
    If[ Head[env] === Wolfram`LeanLink`LeanEnvironment && MatchQ[args, {_String, ___}],
        AssociateTo[Rule30Evaluate`sources, env -> First[args]]
    ];
    Rule30Evaluate`said = Replace[data["MessagesText"], Except[_List] -> {}];
    env
]

(* Ahead of LeanLink's own definition, which it calls. *)
Unprotect[Wolfram`LeanLink`LeanImportString];
DownValues[Wolfram`LeanLink`LeanImportString] = Prepend[
    DownValues[Wolfram`LeanLink`LeanImportString],
    HoldPattern[Wolfram`LeanLink`LeanImportString[args___]] :>
        Block[{Rule30Evaluate`inside = True}, Rule30Evaluate`record[EvaluationData[Wolfram`LeanLink`LeanImportString[args]], {args}]] /; ! TrueQ[Rule30Evaluate`inside]
];
Protect[Wolfram`LeanLink`LeanImportString];

(* The statements of an input cell, split as the front end splits them: at the cell's top-level line
   breaks, keeping lines together while they parse only as one expression. The kernel alone would
   read "a = 3;" and "b = a + 1" on two lines as a product. *)
statements[BoxData[b_]] := statements[b]

statements[RowBox[items_List]] /; MemberQ[items, "\n"] := Block[{out = {}, acc = {}},
    Scan[
        Function[line,
            acc = If[acc === {}, line, Join[acc, {"\n"}, line]];
            If[ ! FailureQ[Quiet @ ToExpression[RowBox[acc], StandardForm, HoldComplete]], AppendTo[out, RowBox[acc]]; acc = {}]
        ],
        DeleteCases[SplitBy[items, # === "\n"&], {"\n" ..}]
    ];
    If[acc =!= {}, AppendTo[out, RowBox[acc]]];
    out
]

statements[b_] := {b}

evaluateCell[s_String] := ToExpression[s, InputForm]

(* Not quieted: LeanLink's messages are what an agent needs when its source fails, and they go to the log. *)
evaluateCell[c_] := Scan[ToExpression[#, StandardForm]&, statements[c]]

Scan[evaluateCell, Cases[Import[notebook, "NB"], Cell[c_, "Input" | "Code", ___] :> c, Infinity]];

(* rule30Submission in whatever context the notebook used, if it has a value. *)
values = DeleteDuplicates @ Map[ToExpression, Select[Names["*`rule30Submission"], ToExpression[#, InputForm, Function[x, OwnValues[x] =!= {}, HoldAll]]&]];

env = SelectFirst[values, Head[#] === Wolfram`LeanLink`LeanEnvironment &, Missing[]];

source = If[MissingQ[env], Missing[], Lookup[Rule30Evaluate`sources, Key[env], Missing[]]];

describe[v_] := StringTake[If[MatchQ[v, _Failure], ToString[v["Message"]], ToString[Short[v, 3]]], UpTo[500]];

lastSaid[] := If[Rule30Evaluate`said === {}, "", " LeanImportString said: " <> StringTake[StringRiffle[Rule30Evaluate`said, "\n"], UpTo[3000]]];

writeResult @ Which[
    ! MissingQ[env] && StringQ[source],
        With[{file = FileNameJoin[{out, "Rule30Submission.lean"}]}, BinaryWrite[file, StringToByteArray[source, "UTF-8"]]; Close[file]];
        <|"ok" -> True, "message" -> "rule30Submission is a LeanEnvironment made by LeanImportString."|>,
    ! MissingQ[env], <|"ok" -> False, "message" -> "rule30Submission was not made by LeanImportString while the notebook was evaluated."|>,
    values === {}, <|"ok" -> False, "message" -> "The notebook does not set rule30Submission."|>,
    True, <|"ok" -> False, "message" -> "rule30Submission is " <> describe[First[values]] <> ", not a LeanEnvironment." <> lastSaid[]|>
];

Exit[0]
