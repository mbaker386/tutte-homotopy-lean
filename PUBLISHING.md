# One-time publication of the approved clean snapshot

## Authorized destination and boundaries

Publish to **mbaker386/tutte-homotopy-lean** on **github.com**, with **public**
visibility and **Apache-2.0** licensing. Matthew Baker approved the name,
visibility and license. This file does not assert that the remote already exists.

Only this clean publication snapshot is authorized for the first upload.
Do not publish, copy, or import the private formalization project's Git history,
manuscript drafts, correspondence, checkpoints, chat transcripts or credentials.
Do not copy newer files from the private project or change any mathematical source,
source-snapshot hashes, version pins, specifications or replay programs.

The supplied collective citation attribution may remain for the first public
snapshot. Do not invent an individual software-author list, DOI, release date,
release number or human certification claim. Do not create a tagged publication
release in this task. Manuscript reconciliation remains separate.

## 1. Verify the local folder and snapshot

Work in a separately extracted `tutte-homotopy-lean` directory, NOT in the original
`TutteFormalization` working repository, and not inside a parent Git repository.
Show its actual absolute path. Check `git rev-parse --show-toplevel` before
initializing Git. A first-time copy should not already have Git history.
If a previous publication attempt left Git state, inspect and report it; do not
remove it, reset it, or overwrite a remote without review.

Run:

```sh
python3 scripts/check_publication_inventory.py
python3 scripts/check_source_snapshot.py
bash -n scripts/verify.sh
```

The publication inventory covers all package files except itself. Ignore generated
build products, logs, `.DS_Store`, and Git metadata, but do not upload them. The
mathematical snapshot check is separate and its original hashes must not change.

## 2. Check GitHub CLI authentication

Check `command -v gh`. If it is missing, stop and ask for installation approval;
do not install tools silently. Inspect the installed CLI help for compatibility.

Run:

```sh
gh auth status --hostname github.com
gh api --hostname github.com user --jq '.login'
```

The login must be **mbaker386**. A ChatGPT login or this chat's GitHub connection
does not establish the local CLI's authentication. Do not print or request tokens,
read credential files, use `gh auth token`, or upload credentials anywhere.

If login is needed, ask the user to complete the normal GitHub browser flow:

```sh
gh auth login --hostname github.com --git-protocol https --web --scopes workflow
```

The workflow scope is for pushing the provided GitHub Actions workflow. If an
existing login needs that scope, explain the need and ask the user to approve
`gh auth refresh --hostname github.com --scopes workflow`. Do not change accounts,
reset scopes, or alter sandbox settings yourself. Use one-time command approvals
when required for Git or network access.

Check whether the destination already exists with `gh repo view` or a read-only
repository API call. If it exists, stop and report its state rather than deleting,
force-pushing over, or changing the visibility of an existing repository. Do not
interpret a generic network/authentication failure as proof of absence.

## 3. Make NEW public history and upload

Only after the preceding checks, initialize fresh local history on branch `main`:

```sh
git init -b main
```

For this repository only, use the user identity `Matthew Baker` and the
GitHub-format no-reply address `<numeric-id>+mbaker386@users.noreply.github.com`;
obtain and confirm the numeric ID using the read-only GitHub user endpoint before applying it.
Do not change global Git configuration or expose a personal email address.

Stage precisely the file paths in `PUBLICATION_INVENTORY.json`, plus that inventory
itself. Read these from the inventory in Python and pass them as explicit arguments
to `git add`; do not stage everything in an original/private project. Inspect the
staged file list and contents. Ensure all inventoried paths are present and no
additional paths are staged. Confirm the staged file bytes match the approved
inventory, including the inventory's self-exempt status. Whitespace warnings already
present in unchanged Lean source should be reported, not fixed by modifying proofs.

Make a single new commit, for example:

```text
Publish Lean proofs of Tutte's path and homotopy theorems
```

Then create the remote and push that new commit:

```sh
gh repo create mbaker386/tutte-homotopy-lean \
  --public \
  --description "Lean 4 proofs of Tutte's path theorem and the local BJL homotopy theorem" \
  --source . --remote origin --push
```

Do not use `--add-readme`, `--license`, or `--gitignore` with this command: those
files are already part of the approved local snapshot. Do not mirror or force-push.
If creation succeeds but pushing fails, preserve the local and remote state,
report the exact error, and retry only the ordinary intended push after the error
is resolved. Do not recreate or delete the remote repository.

## 4. Check the actual remote and report

Check the returned repository metadata: correct owner/name, public visibility,
default branch `main`, and Apache-2.0 license recognition (which may be asynchronous).
If GitHub has not recognized the license yet, report that without rewriting LICENSE.
Compare the remote `main` commit with the local commit, and confirm the README,
LICENSE, both target theorem files, and workflow are present at that commit.

List GitHub Actions runs for the pushed commit. The supplied verification workflow
should be triggered by the push. Report its actual URL and state. A run that is
queued or running is not a passing result. Do not claim a fresh Lean verification
until the actual workflow or a separately recorded local run finishes successfully.

For this initial publication task, proof-code changes are NOT authorized to fix
CI. Read failure logs and report a proposed fix instead. Do not modify audit tests
or regenerate hashes to make CI pass.

Return the repository URL, full public commit hash, commit-specific source URL,
visibility, license status, workflow URL/status, and any unresolved issue.
Do not save personal authentication output into a tracked publication report.
Do not begin further formalization, publish manuscript drafts, or submit to Mathlib.

## Official command references

- https://cli.github.com/manual/gh_repo_create
- https://cli.github.com/manual/gh_auth_login
- https://cli.github.com/manual/gh_auth_refresh
- https://cli.github.com/manual/gh_repo_view
