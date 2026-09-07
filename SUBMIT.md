# How to submit this result to Palomar

The Lean proof and metadata are ready for
[Palomar intake](https://submit.palomar-registry.org/). Palomar accepts
only a public GitHub repository and a full 40-character commit SHA.

## Before you submit

1. Create a public GitHub repository for this project.
2. Push `main` to that repository.
3. Confirm the commit you will pin still contains `Challenge.lean`,
   `Solution.lean`, `comparator.json`, `formalization.yaml`, and
   `LICENSE`.
4. Record the SHA:

   ```bash
   git rev-parse HEAD
   ```

5. Confirm you are a responsible maintainer named in
   `formalization.yaml`, or that you have approval from one. The
   named maintainer is Matt Palmer.

## Submit

1. Open https://submit.palomar-registry.org/
2. Sign in with GitHub. Palomar checks write access to the repository.
3. Enter the repository as `owner/name`.
4. Paste the 40-character SHA. Do not use a branch name.
5. Select `comparator.json` as the Comparator configuration.
6. Leave the project directory blank if the Lake files are at the
   repository root.
7. Leave the Palomar ID blank. This is a first registration.

Read [llms.txt](https://submit.palomar-registry.org/llms.txt) if an
agent is submitting for you.

## What Palomar checks

Palomar rebuilds the project, compares Challenge and Solution, and
replays the exported proof with Lean's kernel and NanoDa. It then runs
an editorial model over the informal account. A green local `./scripts/verify-submit.sh` run means this machine
accepted the proof. Palomar still rebuilds everything on its own pins.
The local Comparator binary was built from the PalomarTemplate commit
on Lean 4.32.0 after `v4.33.0-rc1` failed to download. That is not the
same toolchain Palomar will use. It is not registration.

After the review you decide whether to publish the registry entry.

## If intake fails

Palomar may open a repair pull request for `formalization.yaml`. It
does not push to your default branch. Fix the commit, push, and submit
the new SHA.

Common mechanical failures:

- The repository is private.
- The SHA is a branch or a short hash.
- `LICENSE` and `project.license` disagree.
- Challenge imports something other than Mathlib, Tau Ceti, or CSLib.
- `sorry` remains in the Solution development.

## Files Palomar reads

- `lean-toolchain`
- `lakefile.toml`
- `lake-manifest.json`
- `Challenge.lean`
- `Solution.lean`
- `comparator.json`
- `formalization.yaml`
- `LICENSE`
