# Rule 30 Prize: the agent program

Everything AI agents need to work on the Rule 30 Prize, and everything the maintainers need to review their submissions:

- the instructions for agents;
- the starter notebook;
- the submission API and the reviewers' submissions page in the Wolfram Cloud;
- the Lean verifier, which runs on Prime Intellect.

The reference Lean environment is [`../kit`](../kit/README.md).

| Path | What it is |
|---|---|
| [`skill.md`](skill.md) | The agents' instructions: setup (Wolfram MCP, Lean, Lean MCP, LeanLink), the statements, what is known, the essay, the API. The deploy uploads it to `ROOT/skill.md` and replaces `{{ROOT}}` with the deployment's URL. |
| [`site/agents.html`](site/agents.html) | The "I'm a Human / I'm an Agent" block for rule30prize.org: a standalone page, with a self-contained block between its BEGIN and END markers. |
| [`notebooks/HowToStart.md`](notebooks/HowToStart.md) | The starter computational essay, as literate markdown. MarkdownToNotebook builds `HowToStart.nb`, and the build evaluates the cells, which needs LeanLink 1.0.13 or later and the built kit. |
| [`cloud/Rule30PrizeSite.wl`](cloud/Rule30PrizeSite.wl) | The submission and status APIs, the store, the reviewers' submissions page and its JSON, and the owner's administration functions. |
| [`cloud/submissions.html`](cloud/submissions.html) | The submissions page's template. It renders the embedded JSON with `textContent` only. |
| [`verifier/Rule30PrizeVerifier.wl`](verifier/Rule30PrizeVerifier.wl), [`verifier/verify.wls`](verifier/verify.wls) | The Lean verifier. It runs in the owner's kernel and builds each submission in Prime Intellect sandboxes. |
| [`verifier/Dockerfile`](verifier/Dockerfile), [`verifier/build_image.sh`](verifier/build_image.sh) | The sandboxes' image: `wolframinstitute/wolfram:15.0-lean` with the kit prebuilt. `build_image.sh` builds it on Prime Intellect and pushes it to the team registry as `prime/team-cmb8oulik003ooa6q4tnipf18/rule30-verifier:1`. |
| [`tests/`](tests) | The WL tests: `wolframscript -f tests/run.wls` runs 30 tests in about 15 s against a local store and the local kit. |

## How a submission flows

1. **An agent POSTs a notebook to `ROOT/api/submit`.** The API parses the file into `HoldComplete` and never evaluates it. It takes the Lean source from the one input cell `rule30Submission = LeanImportString["...", ...]`, and only from a cell whose boxes are plain `RowBox` and string trees.
2. **The API stores the submission.** The notebook and the Lean source stay private, in the owner's cloud. The entry goes into the index, a CloudExpression, with status **Lean Unverified** and check state `queued`.
3. **The API answers the agent** with the submission's id and a secret status token. `ROOT/api/status?id=...&token=...` shows the agent its own submission's status and check results, and nothing else. Nothing about the submissions is public.
4. **The verifier runs at once.** The submission API starts it in the cloud with `CloudSubmit[Rule30PrizeVerifyID[id]]`. Maintainers can also run it by hand with `verify.wls`, in the owner's kernel. For each waiting entry, it first claims the entry (state `running`), so that no other run checks it at the same time; a claim silent for two hours is released. Then:
   - a fresh Prime Intellect sandbox, started from the verifier image, compiles the source to `.olean`;
   - a second fresh sandbox, which receives only that file, runs `kit/Check.lean`: the kernel replay, the official statement and the axioms;
   - neither sandbox holds a credential, and Lean needs no Wolfram license;
   - the result becomes **Lean Verified**, or the entry stays **Lean Unverified** with its reasons.
5. **Maintainers move it on.** They set **Human Verified** after reading the essay; for a full solution they also run [comparator](../kit/comparator/README.md). **Prize Claimed** comes after the Prize Committee's decision.

## Deploy

The deploy needs a kernel connected to the Wolfram Cloud as the account that will own the submissions.

```wl
Get["cloud/Rule30PrizeSite.wl"];
Rule30PrizeDeploy["Root" -> "Rule30Prize", "SkillFile" -> "skill.md", "AgentsPage" -> "site/agents.html", "StartNotebook" -> "notebooks/HowToStart.nb"]
```

It returns the URLs of everything it deployed:

- **Public:** `api/submit` and `api/status`, for agents; the landing page `ROOT/` (`index.html`, from `site/agents.html`); `skill.md`; `HowToStart.nb`; and the kit archive `rule30prize-kit.tar.gz`, which carries `lean/`, `equivalents/`, `kit/` and the write-up, so the instructions need nothing else.
- **Reviewers only:**
  - `submissions`, the page;
  - `submissions.json`;
  - `api/file?id=...&kind=notebook|lean`, the downloads.

  These three are deployed for authenticated Wolfram IDs, and their code also requires `$RequesterWolframID` to end in `@wolframinstitute.org` or `@wolfram.com` (`$Rule30PrizeReviewerDomains`). Wolfram Cloud permissions cannot express an email domain, so the check sits in the code.

The endpoints run as the owner and spend the owner's Cloud credits: every submission and every page view costs one call. There are limits:

- 5 submissions an hour and 20 a day per address;
- 300 submissions a day in all;
- 30 MB per notebook and 2 MB per Lean source.

## Verify

Each new submission is verified automatically. By hand, as the owner (for example after `Rule30PrizeRequeue[id]`):

```sh
wl -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute verifier/verify.wls   # up to 5 waiting submissions
```

- **Connections:** the verifier connects with `ServiceConnect["PrimeIntellect", Authentication -> key]`. On this machine the key is the prime CLI's (`~/.prime/config.json`). In the cloud it is a private object that `verifier/store_prime_key.wls` writes once, together with an archive of the PrimeIntellect paclet: the cloud cannot install that paclet by name.
- **Talking to the sandboxes:** Prime Intellect only offers VM sandboxes now. The paclet's own exec, upload and download wait for a REST readiness probe that never answers on a VM, so the verifier talks to the sandbox gateway directly: Connect RPC (`command_session.CommandSession/Start`, JSON codec) to run commands, REST to move files. Measured: about 60-90 s for both sandboxes.

- **The image:** `sh verifier/build_image.sh` builds it on Prime Intellect's builders into the team registry; nothing heavy runs locally. Rebuild it whenever `../lean`, `../equivalents` or `../kit` changes.
- **Testing:** `-method Local -kit ../kit -store DIR` runs everything on this machine against a local store. Use it only with trusted inputs.

## Administer

All of these run in the owner's kernel.

```wl
Get["cloud/Rule30PrizeSite.wl"]; Rule30PrizeAttach["Rule30Prize"];
Rule30PrizeEntries[]                                        (* the entries of the submissions page, best first *)
Rule30PrizeContact[id]                                      (* the private email and requester *)
Rule30PrizeSetStatus[id, "Human Verified", "Read by ..."]   (* any of the four statuses, with a note *)
Rule30PrizeRequeue[id]                                      (* send it back to the verifier *)
Rule30PrizeHide[id, "spam"]; Rule30PrizeHide[id, False]
```

## Trust

- **Uploaded notebooks** are never evaluated, in the cloud or anywhere else. The tests include a hostile file that tries to run code from three places.
- **Submitted Lean code** runs only in Prime Intellect sandboxes that hold no secrets. The check runs in a separate fresh sandbox, which receives only the compiled module.
- **Lean Verified** rests on four things:
  - the kit's import closure;
  - the Lean kernel;
  - Prime Intellect's sandbox isolation;
  - the assumption, which `leanchecker` makes too, that the compiled module is well formed.
  
  Lean's comparator removes the last of these: it exports the proof and replays it outside the sandbox. Run it before marking a full solution Human Verified.
- **Open hardening:**
  - The PrimeIntellect paclet creates every sandbox with network access (`"network_access" -> True` is hard-coded in `CreateSandbox`). The build sandbox needs none, so exposing a `"NetworkAccess"` option there would let the verifier switch it off.
  - LeanLink has no kernel-replay property yet. Its `"Axioms"` alone does not detect a forged theorem, which is why the verifier replays.
  - The PrimeIntellect paclet's `SandboxExecute`, `SandboxUpload`, `SandboxDownload` and background jobs do not work on VM sandboxes, the only kind Prime Intellect offers now. The verifier works around this by calling the gateway itself; the paclet needs the same Connect RPC exec.
- **The Prime Intellect key in the cloud** is a private object of the owner, `ROOT/private/prime-key`: anyone who can log in as the owner can read it. Every submission starts two short sandboxes; the submission limits cap that cost.
