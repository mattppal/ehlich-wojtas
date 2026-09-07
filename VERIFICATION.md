# Verification record

Local checks run on 2026-09-07 against commit work on `main`.
Rerun the commands below to reproduce them.

## Commands

```bash
./scripts/verify.sh
./scripts/verify-submit.sh
```

`verify.sh` is the fast gate. It checks the bound numbers, `lake build`,
Palomar metadata, Challenge imports, and the absence of `sorry` in the
proof.

`verify-submit.sh` also builds and runs Comparator with NanoDa.

## Results

| Check | Result |
| --- | --- |
| `scripts/check_bound.py` | `n=2 -> 2`, `n=6 -> 160`, `n=10 -> 73728` |
| `lake build` | success. Challenge `sorry` warning only |
| `scripts/check_palomar.py` | OK. `math.CO`, `05B20`, `15B34`, `15A15` |
| `ruby scripts/validate-formalization.rb` | no TEMPLATE values |
| Challenge size | 39 lines, Mathlib imports only |
| Proof `sorry` | none in `Solution.lean` or `EhlichWojtas/` |
| Root licence | one `LICENSE`, Apache-2.0 |
| `lake-manifest.json` | public GitHub URLs, 40-character SHAs |
| Comparator | `Your solution is okay!` |
| NanoDa | `Nanoda kernel accepts the solution` |
| Lean kernel | `Lean default kernel accepts the solution` |

The Comparator run is in `.audit/run-comparator.log`.

## Pins

Taken from PalomarTemplate `scripts/verify-comparator.sh`:

| Tool | Commit |
| --- | --- |
| Comparator | `68a064109f01c08f47c8edc9f51d6a2bbffaa188` |
| lean4export | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |

lean4export at that commit uses `leanprover/lean4:v4.32.0`, which matches
this project.

The Comparator pin's own `lean-toolchain` is `v4.33.0-rc1`. Elan could
not download that toolchain (`SSL connect error` to
`releases.lean-lang.org`). The Comparator sources at the pin compiled
on `v4.32.0` and that binary accepted the proof. Palomar's server builds
its own Comparator. `scripts/verify-comparator.sh` now falls back to the
project toolchain when the pin's toolchain is missing.

## Novelty searches

See [NOVELTY.md](NOVELTY.md). GitHub code search found no Lean
formalization of the Ehlich or Wojtas bound. The one `Ehlich` hit is the
substring `presumably` in `kbuzzard/ClassFieldTheory`.
`palomar-registry.org` is not reachable from this environment.

## What this does not prove

Palomar still has to run its own verifier on a public GitHub commit.
This record does not replace that run.

No human referee reviewed the Lean proof.
