#!/usr/bin/env wolframscript
(* ::Package:: *)

(* store_prime_key.wls - give cloud verifications access to Prime Intellect. Stores, as private
   objects of the account this kernel is connected to, the prime CLI's API key and an archive of the
   installed PrimeIntellect paclet: ROOT/private/prime-key and ROOT/private/PrimeIntellect.paclet.
   Run it once as the owner, and again after a new key or paclet:

       wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute verifier/store_prime_key.wls [-root Rule30Prize]

   The key goes from ~/.prime/config.json straight into CloudPut and is never printed. Anyone who
   can log in as the owner can read it. *)

args = $ScriptCommandLine

root = Replace[SequenceCases[args, {"-root", v_} :> v], {{v_, ___} :> v, {} -> "Rule30Prize"}]

key = Lookup[Replace[Quiet @ Developer`ReadRawJSONFile[FileNameJoin[{$HomeDirectory, ".prime", "config.json"}]], Except[_Association] -> <||>], "api_key", None]

If[ ! StringQ[key], Print["no api_key in ~/.prime/config.json: log in with the prime CLI first"]; Exit[1]]

keyObject = CloudPut[key, CloudObject[root <> "/private/prime-key", Permissions -> "Private"]]

ClearAll[key]

paclet = CreatePacletArchive[PacletObject["WolframInstitute/PrimeIntellect"]["Location"], $TemporaryDirectory]

pacletObject = CopyFile[paclet, CloudObject[root <> "/private/PrimeIntellect.paclet", Permissions -> "Private"], OverwriteTarget -> True]

Print["for ", $WolframID, ": ", First[keyObject], " and ", First[pacletObject], " (", FileNameTake[paclet], ")"]
