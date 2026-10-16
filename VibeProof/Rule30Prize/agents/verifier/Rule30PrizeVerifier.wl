(* ::Package:: *)

(* Rule30PrizeVerifier.wl - the Lean verifier of the Rule 30 Prize submissions.

   Run it in the owner's kernel, after Rule30PrizeSite.wl:

       Get["../cloud/Rule30PrizeSite.wl"]; Get["Rule30PrizeVerifier.wl"]
       Rule30PrizeAttach[]
       Rule30PrizeVerify[]                                     (* Prime Intellect sandboxes *)
       Rule30PrizeVerify["Method" -> "Local", "Kit" -> kit]    (* this machine: trusted inputs only *)

   Each queued submission builds in a fresh Prime Intellect microVM sandbox, started from the
   verifier image: wolframinstitute/wolfram:15.0-lean with the Rule 30 Prize kit prebuilt
   (Dockerfile, built by build_image.sh into the team's registry). Only the
   compiled .olean comes out of it. A second fresh sandbox runs the kit's Check.lean on that file: the
   kernel replay, the statement and the axioms. No submitted code runs where the checker runs. Neither
   sandbox holds a credential, and Lean needs no Wolfram license, so they need none either. The
   owner's kernel records each result with the submission. *)

BeginPackage["Rule30PrizeVerifier`", {"Rule30PrizeSite`"}]

$Rule30PrizeVerifierImage::usage = "$Rule30PrizeVerifierImage is the Docker image of the verifier's sandboxes."

Rule30PrizeCheckSource::usage = "Rule30PrizeCheckSource[source, item] builds the Lean source of a submission and checks it, and gives the checker's result as an association."

Rule30PrizeVerify::usage = "Rule30PrizeVerify[] checks the submissions waiting for the Lean verifier and records the results with the submissions."

Begin["`Private`"]

(* Built by build_image.sh into the team's Prime Intellect registry, as a VM sandbox image. *)
$Rule30PrizeVerifierImage = "prime/team-cmb8oulik003ooa6q4tnipf18/rule30-verifier:1"

$verifierDirectory = DirectoryName[$InputFileName]

(* Paths inside the verifier image; Dockerfile writes /opt/rule30/env.sh. *)
$imageKit = "/opt/rule30/VibeProof/Rule30Prize/kit"

$imageEnv = "/opt/rule30/env.sh"

$officialTargets = {"Rule30Submission.problem1", "Rule30Submission.not_problem1", "Rule30Submission.problem2", "Rule30Submission.not_problem2"}

$namePattern = RegularExpression["Rule30Submission(\\.[A-Za-z_][A-Za-z0-9_'!?]*)+"]

$logLimit = 4000

failure[tag_String, msg_String] := Failure[tag, <|"MessageTemplate" -> msg|>]

failed[verdict_String, reason_String, log_ : Null] := <|"verdict" -> verdict, "reasons" -> {reason}, "log" -> log|>

lastChars[s_String] := StringTake[s, -Min[$logLimit, StringLength[s]]]

lastChars[_] := ""

(* The checker's command-line arguments for a queue item, checked again here: they reach a shell. *)
checkerArguments[item_Association] := Block[{target = item["target"], headlines = Replace[item["headlines"], Except[_List] -> {}]},
    Which[
        target =!= Null && ! MemberQ[$officialTargets, target], failure["Target", "unknown target"],
        Length[headlines] > 20 || ! AllTrue[headlines, StringQ[#] && StringMatchQ[#, $namePattern]&], failure["Headlines", "malformed headline names"],
        True, Join[{"--claim", If[StringQ[target], StringDelete[target, "Rule30Submission."], "partial"]}, Catenate @ Map[{"--headline", #}&, headlines]]
    ]
]

(* The checker prints one JSON object, last. *)
checkerResult[out_String] := Replace[Quiet @ ImportString[Last[StringSplit[out, "\n"], ""], "RawJSON"], Except[_Association] -> $Failed]

checkerResult[_] := $Failed

(* === on this machine (Method -> "Local") === *)

(* Run a command with a timeout in seconds. The output is drained while it runs, so a chatty
   process cannot fill the pipe and stall; exit code 124 means it timed out. *)
runCommand[cmd_List, dir_String, env_Association, timeout_ ? NumericQ] := Block[{proc, out = "", err = "", deadline, chunk},
    proc = StartProcess[cmd, ProcessDirectory -> dir, ProcessEnvironment -> env];
    If[ ! MatchQ[proc, _ProcessObject], Return[<|"ExitCode" -> 127, "StandardOutput" -> "", "StandardError" -> "cannot start " <> First[cmd]|>, Block]];
    (* No input: anything that asks for some gets end of file instead of waiting forever. *)
    Quiet @ Close[ProcessConnection[proc, "StandardInput"]];
    deadline = AbsoluteTime[] + timeout;
    While[ ProcessStatus[proc] === "Running" && AbsoluteTime[] < deadline,
        chunk = ReadString[ProcessConnection[proc, "StandardOutput"], EndOfBuffer];
        If[StringQ[chunk], out = out <> chunk];
        chunk = ReadString[ProcessConnection[proc, "StandardError"], EndOfBuffer];
        If[StringQ[chunk], err = err <> chunk];
        Pause[0.1]
    ];
    If[ ProcessStatus[proc] === "Running",
        KillProcess[proc];
        Return[<|"ExitCode" -> 124, "StandardOutput" -> out, "StandardError" -> err <> "\ntimed out after " <> ToString[timeout] <> " s"|>, Block]
    ];
    chunk = ReadString[ProcessConnection[proc, "StandardOutput"]];
    If[StringQ[chunk], out = out <> chunk];
    chunk = ReadString[ProcessConnection[proc, "StandardError"]];
    If[StringQ[chunk], err = err <> chunk];
    <|"ExitCode" -> ProcessInformation[proc, "ExitCode"], "StandardOutput" -> out, "StandardError" -> err|>
]

lakeValue[kit_String, var_String] := Replace[RunProcess[{"lake", "env", "printenv", var}, ProcessDirectory -> kit], {r_Association /; r["ExitCode"] === 0 :> StringTrim[r["StandardOutput"]], _ -> $Failed}]

localKit[kit_String] := localKit[kit] = Block[{path = ExpandFileName[kit], leanPath, sysroot, lean},
    leanPath = lakeValue[path, "LEAN_PATH"];
    sysroot = lakeValue[path, "LEAN_SYSROOT"];
    If[ ! StringQ[leanPath] || ! StringQ[sysroot], Return[failure["Kit", "lake env failed in " <> path <> "; run setup.sh in the kit first"], Block]];
    lean = FileNameJoin[{sysroot, "bin", "lean"}];
    <|
        "Path" -> path,
        "LeanPath" -> leanPath,
        "Sysroot" -> sysroot,
        "Lean" -> lean,
        "Version" -> Replace[RunProcess[{lean, "--short-version"}], {r_Association :> StringTrim[r["StandardOutput"]], _ -> Null}],
        "Commit" -> Replace[RunProcess[{"git", "rev-parse", "HEAD"}, ProcessDirectory -> path], {r_Association /; r["ExitCode"] === 0 :> StringTrim[r["StandardOutput"]], _ -> Null}]
    |>
]

checkLocal[source_ByteArray, cargs_List, kitPath_String, timeouts_List] := Block[{kit = localKit[kitPath], work, file, env, build, log, check, result},
    If[FailureQ[kit], Return[failed["error", kit["Message"]], Block]];
    work = CreateDirectory[];
    file = FileNameJoin[{work, "Rule30Submission.lean"}];
    BinaryWrite[file, source];
    Close[file];
    (* The work folder first: the kit's own build holds the template's Rule30Submission.olean. *)
    (* LEAN_SYSROOT too: without it the checker's findSysroot runs `lean --print-prefix` through elan. *)
    env = <|"PATH" -> Environment["PATH"], "HOME" -> $HomeDirectory, "LEAN_SYSROOT" -> kit["Sysroot"], "LEAN_PATH" -> work <> ":" <> kit["LeanPath"]|>;
    build = runCommand[{kit["Lean"], "-R", work, "-o", FileNameJoin[{work, "Rule30Submission.olean"}], file}, work, env, First[timeouts]];
    log = lastChars[build["StandardOutput"] <> build["StandardError"]];
    result = If[ build["ExitCode"] =!= 0,
        failed["fail", If[build["ExitCode"] === 124, "the build timed out", "the Lean source does not compile"], log],
        check = runCommand[Join[{kit["Lean"], "--run", FileNameJoin[{kit["Path"], "Check.lean"}], "Rule30Submission"}, cargs], work, env, Last[timeouts]];
        Replace[checkerResult[check["StandardOutput"]], {
            r_Association :> Append[r, "log" -> log],
            _ :> failed["error", "the checker gave no result (exit " <> ToString[check["ExitCode"]] <> ")", lastChars[log <> "\n" <> check["StandardError"]]]
        }]
    ];
    Quiet @ DeleteDirectory[work, DeleteContents -> True];
    Join[result, <|"lean" -> kit["Version"], "kitCommit" -> kit["Commit"], "verifier" -> "local"|>]
]

(* === in Prime Intellect sandboxes (Method -> "PrimeIntellect") === *)

shellQuote[s_String] := "'" <> StringReplace[s, "'" -> "'\\''"] <> "'"

(* A command run in the image, with the kit's environment. *)
imageCommand[cmd_String] := "bash -c " <> shellQuote[". " <> $imageEnv <> " && " <> cmd]

newSandbox[so_, name_String, opts_Association] := ServiceExecute[so, "CreateSandbox", {
    "Name" -> name,
    "Image" -> opts["Image"],
    "CPUCores" -> opts["CPUCores"],
    "MemoryGB" -> opts["MemoryGB"],
    "DiskGB" -> opts["DiskGB"],
    "VM" -> opts["VM"],
    "TimeoutMinutes" -> opts["TimeoutMinutes"],
    "Labels" -> {"rule30prize-verifier"}
}]

(* Run body (a function of the sandbox id) in a fresh sandbox, and always delete the sandbox. *)
withSandbox[so_, name_String, opts_Association, body_] := Block[{box = newSandbox[so, name, opts], sid},
    If[ ! AssociationQ[box] || ! StringQ[box["id"]], Return[failed["error", "could not start a Prime Intellect sandbox"], Block]];
    sid = box["id"];
    WithCleanup[body[sid], Quiet @ ServiceExecute[so, "DeleteSandbox", {"SandboxID" -> sid}]]
]

execute[so_, sid_String, cmd_String, timeout_] := ServiceExecute[so, "SandboxExecute", {"SandboxID" -> sid, "Command" -> imageCommand[cmd], "Timeout" -> timeout}]

upload[so_, sid_String, path_String, bytes_ByteArray] := Block[{tmp = CreateFile[]},
    BinaryWrite[tmp, bytes];
    Close[tmp];
    WithCleanup[ServiceExecute[so, "SandboxUpload", {"SandboxID" -> sid, "Path" -> path, "Content" -> File[tmp]}], Quiet @ DeleteFile[tmp]]
]

download[so_, sid_String, path_String] := Replace[ServiceExecute[so, "SandboxDownload", {"SandboxID" -> sid, "Path" -> path}], {b_ByteArray :> b, l_List :> ByteArray[l], s_String :> StringToByteArray[s, "ISO8859-1"], _ -> $Failed}]

(* Build in one sandbox. The build runs as a background job, polled until it ends. *)
buildRemote[so_, source_ByteArray, opts_Association] := withSandbox[so, "rule30-build", opts, Function[sid,
    Block[{job, deadline, status = "running", exit, log, files},
        execute[so, sid, "mkdir -p /work", 120];
        upload[so, sid, "/work/Rule30Submission.lean", source];
        job = ServiceExecute[so, "SandboxStartBackgroundJob", {"SandboxID" -> sid, "Command" -> imageCommand[
            "cd /work && timeout -k 30 " <> ToString[opts["BuildTimeout"]] <> " $RULE30_LEAN -R /work -o /work/Rule30Submission.olean /work/Rule30Submission.lean > /work/build.log 2>&1; echo $? > /work/build.exit"
        ]}];
        If[ ! AssociationQ[job] || ! StringQ[job["JobID"]], Return[failed["error", "could not start the build"], Block]];
        deadline = AbsoluteTime[] + opts["BuildTimeout"] + 120;
        While[ status === "running" && AbsoluteTime[] < deadline,
            Pause[5];
            status = ToLowerCase @ Replace[ServiceExecute[so, "SandboxJobStatus", {"SandboxID" -> sid, "JobID" -> job["JobID"]}], {a_Association :> ToString[a["Status"]], _ -> "running"}]
        ];
        exit = StringTrim @ Replace[ServiceExecute[so, "SandboxReadFile", {"SandboxID" -> sid, "Path" -> "/work/build.exit"}], Except[_String] -> ""];
        log = lastChars @ Replace[ServiceExecute[so, "SandboxReadFile", {"SandboxID" -> sid, "Path" -> "/work/build.log"}], Except[_String] -> ""];
        Which[
            exit === "", failed["fail", "the build did not finish", log],
            exit === "124", failed["fail", "the build timed out", log],
            exit =!= "0", failed["fail", "the Lean source does not compile", log],
            True,
                files = Select[StringSplit @ Replace[execute[so, sid, "cd /work && ls Rule30Submission.olean*", 120], {a_Association :> a["StandardOutput"], _ -> ""}], StringMatchQ[#, "Rule30Submission.olean" ~~ ("" | ".server" | ".private")]&];
                <|"log" -> log, "oleans" -> AssociationMap[download[so, sid, "/work/" <> #]&, files]|>
        ]
    ]
]]

(* Check in a second, fresh sandbox, which receives only the compiled module. *)
checkRemote[so_, oleans_Association, cargs_List, opts_Association] := withSandbox[so, "rule30-check", opts, Function[sid,
    Block[{out},
        execute[so, sid, "mkdir -p /work", 120];
        KeyValueMap[upload[so, sid, "/work/" <> #1, #2]&, oleans];
        out = execute[so, sid,
            "$RULE30_LEAN --short-version; cat /opt/rule30/commit; cd /work && timeout -k 30 " <> ToString[opts["CheckTimeout"]] <> " $RULE30_LEAN --run " <> $imageKit <> "/Check.lean Rule30Submission " <> StringRiffle[shellQuote /@ cargs, " "],
            opts["CheckTimeout"] + 60
        ];
        If[ ! AssociationQ[out], Return[failed["error", "the check sandbox did not answer"], Block]];
        Replace[checkerResult[out["StandardOutput"]], {
            r_Association :> Join[r, <|"lean" -> First[StringSplit[out["StandardOutput"], "\n"], Null], "kitCommit" -> Replace[StringSplit[out["StandardOutput"], "\n"], {{_, c_, ___} :> c, _ -> Null}]|>],
            _ :> failed["error", "the checker gave no result", lastChars[out["StandardError"]]]
        }]
    ]
]]

checkRemote[so_, Except[_Association], ___] := failed["error", "no compiled module came out of the build"]

checkPrime[source_ByteArray, cargs_List, opts_Association] := Block[{so = ServiceConnect["PrimeIntellect"], built, result},
    If[ ! MatchQ[so, _ServiceObject], Return[failed["error", "no Prime Intellect connection (ServiceConnect[\"PrimeIntellect\"])"], Block]];
    built = buildRemote[so, source, opts];
    result = If[ KeyExistsQ[built, "oleans"] && AllTrue[Values[built["oleans"]], ByteArrayQ],
        Append[checkRemote[so, built["oleans"], cargs, opts], "log" -> built["log"]],
        built
    ];
    Append[result, "verifier" -> "Prime Intellect sandboxes, image " <> opts["Image"]]
]

(* === entry points === *)

Options[Rule30PrizeCheckSource] = {
    "Method" -> "PrimeIntellect",
    "Kit" -> Automatic,
    "Image" :> $Rule30PrizeVerifierImage,
    "CPUCores" -> 4,
    "MemoryGB" -> 16,
    "DiskGB" -> 40,
    "VM" -> True,
    "TimeoutMinutes" -> 45,
    "BuildTimeout" -> 900,
    "CheckTimeout" -> 600
}

Rule30PrizeCheckSource[source_String, item_Association, opts : OptionsPattern[]] := Rule30PrizeCheckSource[StringToByteArray[source, "UTF-8"], item, opts]

Rule30PrizeCheckSource[source_ByteArray, item_Association, opts : OptionsPattern[]] := Block[{cargs = checkerArguments[item]},
    Which[
        FailureQ[cargs], failed["error", cargs["Message"]],
        OptionValue["Method"] === "Local", checkLocal[source, cargs, Replace[OptionValue["Kit"], Automatic :> FileNameJoin[{$verifierDirectory, "..", "..", "kit"}]], {OptionValue["BuildTimeout"], OptionValue["CheckTimeout"]}],
        True, checkPrime[source, cargs, Association @ Map[# -> OptionValue[#]&, {"Image", "CPUCores", "MemoryGB", "DiskGB", "VM", "TimeoutMinutes", "BuildTimeout", "CheckTimeout"}]]
    ]
]

Options[Rule30PrizeVerify] = Join[{"MaxItems" -> 5}, Options[Rule30PrizeCheckSource]]

Rule30PrizeVerify[opts : OptionsPattern[]] := Map[
    Function[item,
        Block[{source = Quiet @ BaseDecode[item["sourceBase64"]], result},
            result = If[ ! ByteArrayQ[source] || Hash[source, "SHA256", "HexString"] =!= item["sourceSHA256"],
                failed["error", "the stored source does not match its SHA-256"],
                Rule30PrizeCheckSource[source, item, FilterRules[{opts}, Options[Rule30PrizeCheckSource]]]
            ];
            <|"id" -> item["id"], "verdict" -> result["verdict"], "reasons" -> result["reasons"], "recorded" -> Rule30PrizeRecordCheck[item["id"], item["sourceSHA256"], result]|>
        ]
    ],
    Rule30PrizeQueue[OptionValue["MaxItems"]]
]

End[]

EndPackage[]
