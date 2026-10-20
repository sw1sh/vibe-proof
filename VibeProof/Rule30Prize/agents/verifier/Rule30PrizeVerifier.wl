(* ::Package:: *)

(* Rule30PrizeVerifier.wl - the Lean verifier of the Rule 30 Prize submissions.

   Run it in the owner's kernel, after Rule30PrizeSite.wl:

       Get["../cloud/Rule30PrizeSite.wl"]; Get["Rule30PrizeVerifier.wl"]
       Rule30PrizeAttach[]
       Rule30PrizeVerify[]                                     (* Prime Intellect sandboxes *)
       Rule30PrizeVerify["Method" -> "Local", "Kit" -> kit]    (* this machine: trusted inputs only *)

   A submission is a notebook. Its check runs in two fresh Prime Intellect microVM sandboxes, started
   from the verifier image: wolframinstitute/wolfram:15.0-lean with LeanLink 1.0.14 and the Rule 30
   Prize kit (WolframInstitute/Rule30PrizeKit) prebuilt; Dockerfile, built by build_image.sh into the
   team's registry.
   - The first evaluates the notebook with evaluate.wls and reads the LeanEnvironment its
     rule30Submission holds. It runs under a Wolfram license entitlement minted for this check alone:
     one kernel, an hour at most, deleted as soon as the evaluation ends. Submitted code runs there
     and can read that entitlement while it lasts. Then it builds the Lean source behind that
     environment as the module Rule30Submission; only the compiled .olean and the source come out.
   - The second receives only the .olean and runs the kit's Check.lean on it: the kernel replay, the
     statement and the axioms. No submitted code runs where the checker runs, and it holds nothing.
   The owner's kernel records each result, and the source, with the submission. *)

BeginPackage["Rule30PrizeVerifier`", {"Rule30PrizeSite`"}]

$Rule30PrizeVerifierImage::usage = "$Rule30PrizeVerifierImage is the Docker image of the verifier's sandboxes."

Rule30PrizeCheckNotebook::usage = "Rule30PrizeCheckNotebook[notebook, item] evaluates a submitted notebook, builds the Lean source behind its rule30Submission and checks it, and gives the checker's result, with the source, as an association."

Rule30PrizeVerify::usage = "Rule30PrizeVerify[] checks the submissions waiting for the Lean verifier and records the results with the submissions."

Rule30PrizeVerifyID::usage = "Rule30PrizeVerifyID[id] checks one waiting submission and records the result. The submission API starts it in the cloud for each new submission."

Rule30PrizeCloudAccess::usage = "Rule30PrizeCloudAccess[rootURL] points verifications that run in the cloud at the Prime Intellect key and paclet stored under rootURL/private, and the team of the prime CLI here."

$Rule30PrizePrimeAccess::usage = "$Rule30PrizePrimeAccess gives the cloud objects holding the Prime Intellect key and the PrimeIntellect paclet, for verifications that run in the cloud, or None."

Begin["`Private`"]

(* Built by build_image.sh into the team's Prime Intellect registry, as a VM sandbox image. *)
$Rule30PrizeVerifierImage = "prime/team-cmb8oulik003ooa6q4tnipf18/rule30-verifier:3"

$verifierDirectory = DirectoryName[$InputFileName]

(* The script that evaluates a notebook in the build sandbox, read when this package loads: the
   deployed submission API carries it into the cloud, where this folder does not exist. *)
$evaluateScript = ReadByteArray[FileNameJoin[{$verifierDirectory, "evaluate.wls"}]]

(* For verifications that run in the cloud, which has neither the prime CLI nor the PrimeIntellect
   paclet: private cloud objects with the key and the paclet archive (store_prime_key.wls puts them
   there, deploy.wls sets this). *)
$Rule30PrizePrimeAccess = None

Rule30PrizeCloudAccess[rootURL_String] := ($Rule30PrizePrimeAccess = <|
    "Key" -> rootURL <> "/private/prime-key",
    "Paclet" -> rootURL <> "/private/PrimeIntellect.paclet",
    "TeamID" -> teamID[]
|>)

(* The verifier image's environment, which the Dockerfile writes: RULE30_KIT (the kit), RULE30_LEAN,
   LEAN_SYSROOT and LEAN_PATH (with /work first). *)
$imageEnv = "/opt/rule30/env.sh"

$officialTargets = {"Rule30Submission.problem1", "Rule30Submission.not_problem1", "Rule30Submission.problem2", "Rule30Submission.not_problem2"}

$namePattern = RegularExpression["Rule30Submission(\\.[A-Za-z_][A-Za-z0-9_'!?]*)+"]

$logLimit = 4000

(* Told what the check is doing; verifyItem records it with the submission. *)
$progress = Function[detail, Null]

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

(* A process the kernel of the sandbox killed for want of memory. *)
outOfMemoryQ[exit_, log_String] := MatchQ[exit, 137 | "137"] || StringContainsQ[log, "Killed"]

(* What evaluate.wls left: None when it found the source, or the failure to report. The notebook is
   blamed only on evidence: its own rule30Submission, or a published limit it exceeded. Anything else
   is the verifier's error. *)
evaluationFailure[exit_, result_, log_String] := Which[
    MatchQ[exit, 124 | "124"], failed["fail", "evaluating the notebook took longer than its limit", lastChars[log]],
    outOfMemoryQ[exit, log], failed["fail", "evaluating the notebook ran out of the sandbox's memory", lastChars[log]],
    MatchQ[exit, "" | Null], failed["error", "the evaluation of the notebook did not finish", lastChars[log]],
    AssociationQ[result] && ! TrueQ[result["ok"]], failed["fail", Replace[result["message"], Except[_String] -> "the notebook has no rule30Submission"], lastChars[log]],
    ! AssociationQ[result], failed["error", "the verifier could not evaluate the notebook", lastChars[log]],
    True, None
]

checkLocal[notebook_ByteArray, cargs_List, kitPath_String, timeouts_Association] := Block[{kit = localKit[kitPath], work, nb, out, evaluation, stop, source, file, env, build, log, check, result},
    If[FailureQ[kit], Return[failed["error", kit["Message"]], Block]];
    work = CreateDirectory[];
    nb = FileNameJoin[{work, "submission.nb"}];
    BinaryWrite[nb, notebook];
    Close[nb];
    (* The notebook runs with this machine's license and its whole environment: trusted inputs only. *)
    out = FileNameJoin[{work, "out"}];
    evaluation = runCommand[{"wolframscript", "-f", FileNameJoin[{$verifierDirectory, "evaluate.wls"}], nb, out}, work,
        Join[Association[GetEnvironment[]], <|"RULE30PRIZE_KIT" -> kit["Path"]|>], timeouts["Evaluate"]];
    stop = evaluationFailure[evaluation["ExitCode"], Quiet @ Import[FileNameJoin[{out, "result.json"}], "RawJSON"], evaluation["StandardOutput"] <> evaluation["StandardError"]];
    If[ stop =!= None,
        Quiet @ DeleteDirectory[work, DeleteContents -> True];
        Return[Join[stop, <|"lean" -> kit["Version"], "kitCommit" -> kit["Commit"], "verifier" -> "local"|>], Block]
    ];
    source = ReadByteArray[FileNameJoin[{out, "Rule30Submission.lean"}]];
    file = FileNameJoin[{work, "Rule30Submission.lean"}];
    BinaryWrite[file, source];
    Close[file];
    (* The work folder first: the kit's own build holds the template's Rule30Submission.olean. *)
    (* LEAN_SYSROOT too: without it the checker's findSysroot runs `lean --print-prefix` through elan. *)
    env = <|"PATH" -> Environment["PATH"], "HOME" -> $HomeDirectory, "LEAN_SYSROOT" -> kit["Sysroot"], "LEAN_PATH" -> work <> ":" <> kit["LeanPath"]|>;
    build = runCommand[{kit["Lean"], "-R", work, "-o", FileNameJoin[{work, "Rule30Submission.olean"}], file}, work, env, timeouts["Build"]];
    log = lastChars[build["StandardOutput"] <> build["StandardError"]];
    result = If[ build["ExitCode"] =!= 0,
        Which[
            build["ExitCode"] === 124, failed["fail", "the build timed out", log],
            outOfMemoryQ[build["ExitCode"], log], failed["fail", "the build ran out of memory", log],
            True, failed["fail", "the Lean source does not compile", log]
        ],
        check = runCommand[Join[{kit["Lean"], "--run", FileNameJoin[{kit["Path"], "Check.lean"}], "Rule30Submission"}, cargs], work, env, timeouts["Check"]];
        Replace[checkerResult[check["StandardOutput"]], {
            r_Association :> Append[r, "log" -> log],
            _ :> failed["error", "the checker gave no result (exit " <> ToString[check["ExitCode"]] <> ")", lastChars[log <> "\n" <> check["StandardError"]]]
        }]
    ];
    Quiet @ DeleteDirectory[work, DeleteContents -> True];
    Join[result, <|"source" -> source, "lean" -> kit["Version"], "kitCommit" -> kit["Commit"], "verifier" -> "local"|>]
]

(* === in Prime Intellect sandboxes (Method -> "PrimeIntellect") === *)

(* Prime Intellect has retired container sandboxes. A VM sandbox runs commands through its gateway's
   Connect RPC service command_session.CommandSession, which the PrimeIntellect paclet does not
   speak yet; its own SandboxExecute, SandboxUpload and SandboxDownload wait for a REST readiness
   probe that never answers on a VM. So the paclet only creates, authenticates and deletes sandboxes,
   and this file talks to the gateway as the prime CLI does: Connect RPC with the JSON codec to run
   commands, REST to move files. *)

shellQuote[s_String] := "'" <> StringReplace[s, "'" -> "'\\''"] <> "'"

(* A command run with the kit's environment. *)
imageCommand[cmd_String] := ". " <> $imageEnv <> " && " <> cmd

(* The team whose wallet and registry the sandboxes use. The paclet reads it from the prime CLI's
   config, which the cloud does not have. *)
teamID[] := Replace[
    Lookup[Replace[Quiet @ Developer`ReadRawJSONFile[FileNameJoin[{$HomeDirectory, ".prime", "config.json"}]], Except[_Association] -> <||>], "team_id", None],
    Except[_String] :> If[AssociationQ[$Rule30PrizePrimeAccess], Lookup[$Rule30PrizePrimeAccess, "TeamID", Automatic], Automatic]
]

newSandbox[so_, name_String, opts_Association] := ServiceExecute[so, "CreateSandbox", {
    "Name" -> name,
    "TeamID" -> teamID[],
    "Image" -> opts["Image"],
    "CPUCores" -> opts["CPUCores"],
    "MemoryGB" -> opts["MemoryGB"],
    "DiskGB" -> opts["DiskGB"],
    "VM" -> True,
    "TimeoutMinutes" -> opts["TimeoutMinutes"],
    "Labels" -> {"rule30prize-verifier"}
}]

sandboxStatus[so_, sid_String] := Replace[Quiet @ ServiceExecute[so, "Sandbox", {"SandboxID" -> sid}], {a_Association :> Lookup[a, "status", "PENDING"], _ -> "PENDING"}]

awaitRunning[so_, sid_String, seconds_] := Block[{deadline = AbsoluteTime[] + seconds, status = sandboxStatus[so, sid]},
    While[ ! MemberQ[{"RUNNING", "ERROR", "TERMINATED", "TIMEOUT"}, status] && AbsoluteTime[] < deadline,
        Pause[5];
        status = sandboxStatus[so, sid]
    ];
    status === "RUNNING"
]

(* Run body (a function of the sandbox id) in a fresh sandbox once it runs, and always delete it. *)
withSandbox[so_, name_String, opts_Association, body_] := Block[{box = newSandbox[so, name, opts], sid},
    If[ ! AssociationQ[box] || ! StringQ[box["id"]], Return[failed["error", "could not start a Prime Intellect sandbox: " <> Replace[box, {f_Failure :> f["Message"], other_ :> ToString[Short[other, 1]]}]], Block]];
    sid = box["id"];
    WithCleanup[
        If[awaitRunning[so, sid, opts["StartTimeout"]], body[sid], failed["error", "the Prime Intellect sandbox did not start"]],
        Quiet @ ServiceExecute[so, "DeleteSandbox", {"SandboxID" -> sid}]
    ]
]

(* The gateway address and token of a sandbox, minted afresh for every call: tokens expire. *)
gateway[so_, sid_String] := Replace[Quiet @ ServiceExecute[so, "SandboxAuthenticate", {"SandboxID" -> sid}], {
    a_Association /; StringQ[a["Token"]] && StringQ[a["GatewayURL"]] :> <|"Base" -> StringTrim[a["GatewayURL"], "/"] <> "/" <> a["UserNS"] <> "/" <> a["JobID"], "Token" -> a["Token"]|>,
    _ -> $Failed
}]

(* A Connect message: a flag byte, a 4-byte big-endian length, the JSON. *)
connectFrame[json_Association] := With[{b = StringToByteArray[Developer`WriteRawJSONString[json, "Compact" -> True], "UTF-8"]},
    Join[ByteArray[{0}], ByteArray[IntegerDigits[Length[b], 256, 4]], b]
]

connectMessages[ba_ByteArray] := Block[{bytes = Normal[ba], i = 1, n},
    First[Last[Reap[
        While[ i + 4 <= Length[bytes],
            n = FromDigits[bytes[[i + 1 ;; i + 4]], 256];
            Sow[{bytes[[i]], Quiet @ ImportByteArray[ByteArray[bytes[[i + 5 ;; i + 4 + n]]], "RawJSON"]}];
            i += 5 + n
        ]
    ]], {}]
]

connectMessages[_] := {}

(* Run a command with bash in the sandbox and wait for it to end. Proto3 JSON omits a zero exit code. *)
gatewayExecute[so_, sid_String, cmd_String, timeout_ : 120] := Block[{gw = gateway[so, sid], resp, messages, stream},
    If[gw === $Failed, Return[<|"ExitCode" -> -1, "StandardOutput" -> "", "StandardError" -> "no gateway token"|>, Block]];
    resp = Quiet @ URLRead[HTTPRequest[gw["Base"] <> "/command_session.CommandSession/Start", <|
        "Method" -> "POST",
        "Headers" -> {"Authorization" -> "Bearer " <> gw["Token"], "Content-Type" -> "application/connect+json", "Connect-Protocol-Version" -> "1", "Connect-Timeout-Ms" -> ToString[1000 * timeout]},
        "Body" -> connectFrame[<|"command" -> <|"cmd" -> "/bin/bash", "args" -> {"-c", cmd}, "envs" -> <||>|>, "stdin" -> False|>]
    |>], TimeConstraint -> timeout + 30];
    If[ FailureQ[resp] || resp["StatusCode"] =!= 200,
        Return[<|"ExitCode" -> -1, "StandardOutput" -> "", "StandardError" -> "gateway: " <> ToString[If[FailureQ[resp], resp["Message"], resp["StatusCode"]]]|>, Block]
    ];
    messages = connectMessages[resp["BodyByteArray"]];
    stream[key_] := Replace[Cases[messages, {0, KeyValuePattern["event" -> KeyValuePattern["data" -> KeyValuePattern[key -> s_String]]]} :> BaseDecode[s]], {{} -> "", chunks_ :> ByteArrayToString[Join @@ chunks, "UTF-8"]}];
    <|
        "ExitCode" -> FirstCase[messages, {0, KeyValuePattern["event" -> KeyValuePattern["end" -> e_Association]]} :> Lookup[e, "exitCode", 0], -1],
        "StandardOutput" -> stream["stdout"],
        "StandardError" -> stream["stderr"]
    |>
]

gatewayUpload[so_, sid_String, path_String, bytes_ByteArray] := Block[{gw = gateway[so, sid], resp},
    If[gw === $Failed, Return[$Failed, Block]];
    resp = Quiet @ URLRead[HTTPRequest[URLBuild[gw["Base"] <> "/upload", {"path" -> path, "sandbox_id" -> sid}], <|
        "Method" -> "POST",
        "Headers" -> {"Authorization" -> "Bearer " <> gw["Token"]},
        "Body" -> {"file" -> <|"Content" -> bytes, "Name" -> FileNameTake[path], "MIMEType" -> "application/octet-stream"|>}
    |>], TimeConstraint -> 300];
    If[ ! FailureQ[resp] && resp["StatusCode"] === 200, path, $Failed]
]

gatewayDownload[so_, sid_String, path_String] := Block[{gw = gateway[so, sid], resp},
    If[gw === $Failed, Return[$Failed, Block]];
    resp = Quiet @ URLRead[HTTPRequest[URLBuild[gw["Base"] <> "/download", {"path" -> path, "sandbox_id" -> sid}], <|
        "Method" -> "GET",
        "Headers" -> {"Authorization" -> "Bearer " <> gw["Token"]}
    |>], TimeConstraint -> 300];
    If[ ! FailureQ[resp] && resp["StatusCode"] === 200, resp["BodyByteArray"], $Failed]
]

text[b_ByteArray] := ByteArrayToString[b, "UTF-8"]

text[_] := ""

(* Evaluate the notebook and build the Lean source behind its rule30Submission, in one sandbox. Both
   run detached, and short polls read their exit codes. The entitlement is deleted as soon as the
   evaluation ends, before the build. *)
buildRemote[so_, notebook_ByteArray, ent_, opts_Association] := withSandbox[so, "rule30-build", opts, Function[sid,
    Block[{script, deadline, state = {"", ""}, built = False, stop, source, exit, log, files},
        $progress["evaluating the notebook"];
        gatewayExecute[so, sid, "mkdir -p /work/out"];
        If[gatewayUpload[so, sid, "/work/submission.nb", notebook] === $Failed, Return[failed["error", "could not upload the notebook to the sandbox"], Block]];
        gatewayUpload[so, sid, "/work/evaluate.wls", $evaluateScript];
        script = StringRiffle[{
            ". " <> $imageEnv,
            "cd /work",
            "export RULE30PRIZE_KIT=\"$RULE30_KIT\"",
            "WOLFRAMSCRIPT_ENTITLEMENTID=" <> shellQuote[ent["EntitlementID"]] <> " timeout -k 30 " <> ToString[opts["EvaluateTimeout"]] <>
                " wolframscript -f /work/evaluate.wls /work/submission.nb /work/out > /work/evaluate.log 2>&1 < /dev/null",
            "echo $? > /work/evaluate.exit",
            "if [ -s /work/out/Rule30Submission.lean ]; then",
            "  cp /work/out/Rule30Submission.lean /work/Rule30Submission.lean",
            "  timeout -k 30 " <> ToString[opts["BuildTimeout"]] <> " \"$RULE30_LEAN\" -R /work -o /work/Rule30Submission.olean /work/Rule30Submission.lean > /work/build.log 2>&1",
            "  echo $? > /work/build.exit",
            "fi",
            "echo done > /work/done"
        }, "\n"];
        gatewayUpload[so, sid, "/work/build.sh", StringToByteArray[script, "UTF-8"]];
        gatewayExecute[so, sid, "setsid nohup bash /work/build.sh > /dev/null 2>&1 < /dev/null &"];
        deadline = AbsoluteTime[] + opts["EvaluateTimeout"] + opts["BuildTimeout"] + 180;
        (* state: the evaluation's exit code, then "done" when everything has finished. *)
        While[ Last[state] =!= "done" && AbsoluteTime[] < deadline,
            Pause[10];
            state = PadRight[StringSplit[gatewayExecute[so, sid, "printf '%s|%s' \"$(cat /work/evaluate.exit 2>/dev/null)\" \"$(cat /work/done 2>/dev/null)\""]["StandardOutput"], "|", All], 2, ""];
            If[ First[state] =!= "" && ! TrueQ[built],
                built = True;
                Quiet @ DeleteObject[ent];
                $progress["building the Lean source"]
            ]
        ];
        Quiet @ DeleteObject[ent];
        stop = evaluationFailure[First[state],
            Quiet @ ImportString[text @ gatewayDownload[so, sid, "/work/out/result.json"], "RawJSON"],
            text @ gatewayDownload[so, sid, "/work/evaluate.log"]];
        If[stop =!= None, Return[stop, Block]];
        source = gatewayDownload[so, sid, "/work/Rule30Submission.lean"];
        exit = StringTrim @ gatewayExecute[so, sid, "cat /work/build.exit 2>/dev/null"]["StandardOutput"];
        log = lastChars @ text @ gatewayDownload[so, sid, "/work/build.log"];
        Append[
            Which[
                exit === "", failed["error", "the build did not finish", log],
                exit === "124", failed["fail", "the build timed out", log],
                outOfMemoryQ[exit, log], failed["fail", "the build ran out of the sandbox's memory", log],
                exit =!= "0", failed["fail", "the Lean source does not compile", log],
                True,
                    files = Select[StringSplit @ gatewayExecute[so, sid, "cd /work && ls Rule30Submission.olean*"]["StandardOutput"], StringMatchQ[#, "Rule30Submission.olean" ~~ ("" | ".server" | ".private")]&];
                    <|"log" -> log, "oleans" -> AssociationMap[gatewayDownload[so, sid, "/work/" <> #]&, files]|>
            ],
            "source" -> source
        ]
    ]
]]

(* Check in a second, fresh sandbox, which receives only the compiled module. *)
checkRemote[so_, oleans_Association, cargs_List, opts_Association] := withSandbox[so, "rule30-check", opts, Function[sid,
    Block[{out},
        gatewayExecute[so, sid, "mkdir -p /work"];
        KeyValueMap[gatewayUpload[so, sid, "/work/" <> #1, #2]&, oleans];
        out = gatewayExecute[so, sid,
            imageCommand["\"$RULE30_LEAN\" --short-version; cat /opt/rule30/commit; cd /work && timeout -k 30 " <> ToString[opts["CheckTimeout"]] <> " \"$RULE30_LEAN\" --run \"$RULE30_KIT\"/Check.lean Rule30Submission " <> StringRiffle[shellQuote /@ cargs, " "]],
            opts["CheckTimeout"] + 60
        ];
        Replace[checkerResult[out["StandardOutput"]], {
            r_Association :> Join[r, <|"lean" -> First[StringSplit[out["StandardOutput"], "\n"], Null], "kitCommit" -> Replace[StringSplit[out["StandardOutput"], "\n"], {{_, c_, ___} :> c, _ -> Null}]|>],
            _ :> failed["error", "the checker gave no result (exit " <> ToString[out["ExitCode"]] <> ")", lastChars[out["StandardError"]]]
        }]
    ]
]]

checkRemote[so_, Except[_Association], ___] := failed["error", "no compiled module came out of the build"]

(* The prime CLI's key where there is one, as the PrimeIntellect paclet's own tests connect; in the
   cloud, the key and the paclet from $Rule30PrizePrimeAccess. *)
primeKey[] := Replace[
    Lookup[Replace[Quiet @ Developer`ReadRawJSONFile[FileNameJoin[{$HomeDirectory, ".prime", "config.json"}]], Except[_Association] -> <||>], "api_key", None],
    Except[_String] :> If[AssociationQ[$Rule30PrizePrimeAccess], Replace[Quiet @ CloudGet[CloudObject[$Rule30PrizePrimeAccess["Key"]]], Except[_String] -> None], None]
]

installPrimePaclet[] := If[ PacletFind["WolframInstitute/PrimeIntellect"] === {} && AssociationQ[$Rule30PrizePrimeAccess],
    Block[{file = FileNameJoin[{$TemporaryDirectory, "PrimeIntellect.paclet"}]},
        Quiet @ CopyFile[CloudObject[$Rule30PrizePrimeAccess["Paclet"]], file, OverwriteTarget -> True];
        Quiet @ PacletInstall[file, ForceVersionInstall -> True]
    ]
]

primeConnection[] := Block[{key = primeKey[]},
    installPrimePaclet[];
    If[StringQ[key], ServiceConnect["PrimeIntellect", Authentication -> key], ServiceConnect["PrimeIntellect"]]
]

(* A Wolfram license for evaluating one notebook: one kernel, for an hour at most. Minting needs the
   owner's cloud connection. *)
mintEntitlement[] := Quiet @ CreateLicenseEntitlement[<|"StandardKernelLimit" -> 1, "ParallelKernelLimit" -> 0,
    "LicenseExpiration" -> Quantity[1, "Hours"], "EntitlementExpiration" -> Quantity[1, "Hours"]|>]

checkPrime[notebook_ByteArray, cargs_List, opts_Association] := Block[{so = primeConnection[], ent, built, result},
    If[ ! MatchQ[so, _ServiceObject], Return[failed["error", "no Prime Intellect connection: no prime CLI key here, and no key in $Rule30PrizePrimeAccess"], Block]];
    ent = mintEntitlement[];
    If[ ! MatchQ[ent, _LicenseEntitlementObject], Return[failed["error", "could not mint a Wolfram license entitlement to evaluate the notebook"], Block]];
    $progress["starting a sandbox"];
    built = buildRemote[so, notebook, ent, opts];
    Quiet @ DeleteObject[ent];
    result = If[ KeyExistsQ[built, "oleans"] && AllTrue[Values[built["oleans"]], ByteArrayQ],
        $progress["checking the compiled module in a second sandbox"];
        Join[checkRemote[so, built["oleans"], cargs, opts], KeyTake[built, {"log", "source"}]],
        built
    ];
    Append[result, "verifier" -> "Prime Intellect sandboxes, image " <> opts["Image"]]
]

(* === entry points === *)

Options[Rule30PrizeCheckNotebook] = {
    "Method" -> "PrimeIntellect",
    "Kit" -> Automatic,
    "Image" :> $Rule30PrizeVerifierImage,
    "CPUCores" -> 8,
    "MemoryGB" -> 32,
    "DiskGB" -> 40,
    "StartTimeout" -> 900,
    "TimeoutMinutes" -> 45,
    "EvaluateTimeout" -> 900,
    "BuildTimeout" -> 900,
    "CheckTimeout" -> 600
}

Rule30PrizeCheckNotebook[File[path_String], item_Association, opts : OptionsPattern[]] := Rule30PrizeCheckNotebook[ReadByteArray[path], item, opts]

Rule30PrizeCheckNotebook[notebook_ByteArray, item_Association, opts : OptionsPattern[]] := Block[{cargs = checkerArguments[item]},
    Which[
        FailureQ[cargs], failed["error", cargs["Message"]],
        OptionValue["Method"] === "Local", checkLocal[notebook, cargs, Replace[OptionValue["Kit"], Automatic :> FileNameJoin[{$verifierDirectory, "..", "..", "kit"}]],
            <|"Evaluate" -> OptionValue["EvaluateTimeout"], "Build" -> OptionValue["BuildTimeout"], "Check" -> OptionValue["CheckTimeout"]|>],
        True, checkPrime[notebook, cargs, Association @ Map[# -> OptionValue[#]&, {"Image", "CPUCores", "MemoryGB", "DiskGB", "StartTimeout", "TimeoutMinutes", "EvaluateTimeout", "BuildTimeout", "CheckTimeout"}]]
    ]
]

Options[Rule30PrizeVerify] = Join[{"MaxItems" -> 5}, Options[Rule30PrizeCheckNotebook]]

(* Check one queue item, after claiming it so that no other run checks it at the same time. *)
verifyItem[item_Association, opts___] := Block[{notebook = Quiet @ BaseDecode[item["notebookBase64"]], result},
    If[ ! Rule30PrizeClaimCheck[item["id"]], Return[<|"id" -> item["id"], "verdict" -> None, "reasons" -> {"another run is checking it"}|>, Block]];
    result = If[ ! ByteArrayQ[notebook] || Hash[notebook, "SHA256", "HexString"] =!= item["notebookSHA256"],
        failed["error", "the stored notebook does not match its SHA-256"],
        Block[{$progress = Function[detail, Rule30PrizeProgress[item["id"], detail]]},
            Rule30PrizeCheckNotebook[notebook, item, FilterRules[{opts}, Options[Rule30PrizeCheckNotebook]]]
        ]
    ];
    <|"id" -> item["id"], "verdict" -> result["verdict"], "reasons" -> result["reasons"], "recorded" -> Rule30PrizeRecordCheck[item["id"], item["notebookSHA256"], result]|>
]

Rule30PrizeVerify[opts : OptionsPattern[]] := Map[verifyItem[#, opts]&, Rule30PrizeQueue[OptionValue["MaxItems"]]]

Rule30PrizeVerifyID[id_String, opts : OptionsPattern[Rule30PrizeVerify]] := Replace[Rule30PrizeQueueItem[id], {
    item_Association :> verifyItem[item, opts],
    _ -> <|"id" -> id, "verdict" -> None, "reasons" -> {"not waiting for the verifier"}|>
}]

End[]

EndPackage[]
