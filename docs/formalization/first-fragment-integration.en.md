# Integration review of the first algebraic fragment

[Chinese original](first-fragment-integration.md)

2026-11-15: read-only review of current configuration, source-import relations, status wording, and existing machine evidence. This added no mathematical review and did not rerun the build/full tool suite.

**Conclusion: no configuration or source-binding issue was found that would prevent continued integration of the current five supporting theorems.** The identified summary-field lookup issue received a minimal correction; the final entry point still requires refresh under the established process. Machine passes, independent mathematical review, author confirmation, and whole-paper completion remain separate.

## Pinned environment and source

- `lean-toolchain` pins Lean 4.24.0. `lakefile.toml`, the manifest, and actual project `.lake/packages/mathlib` HEAD all identify `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Actual HEADs of all 9 project packages individually match the manifest; `git status --porcelain=v1 --untracked-files=normal` is empty in each package.
- `.project-verification/dependency-setup.json` records independent Git object/worktree checkouts, no shared object storage, and no copied parent cache. `.project-verification/mathlib-cache-resume.log` actually records successful targeted unpacking of 917 cache files. These are precompiled dependencies for the current import closure, not evidence that all Mathlib was rebuilt or its entire cache is present.
- `Burnett.lean` imports `Burnett.Overview` and `Burnett.Algebra.RicciSymbol`. Overview has no reverse import, and the leaf imports only 5 Mathlib modules; no local dependency cycle was found. The targeted cache lists in CI/README match the leaf imports.
- Current leaf-source SHA256 is `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`, matching the formatting-change record, target-check receipt, and appended independent readback. A byte comparison against the retained old source found equality after trimming trailing file whitespace; no mathematical token change was observed.
- The project worktree currently contains expected changes/new files from this round. The target receipt accurately records `dirty: true`, rather than presenting the old HEAD as the current source commit.

## Responsibilities of build and declaration checks

`scripts/check_project.py` first actually runs `lake build Burnett`, then calls the original `scripts/check_paper.py` for a nonempty target inventory. The original checker was not modified in this round. It still rejects empty targets, checks that each target is a theorem from the specified local module, collects transitive axiom dependencies, and compares input snapshots before and after checking.

At the first review read, `.project-verification/result.json` and `.paper-verification/result.json` both reported `machine-check-passed`. The actual library-entry build log recorded success; the original target checker's module-build and audit exit codes were both 0. Its receipt bound the final leaf source, scope, toolchain, lakefile, manifest, and checker hashes. Key hashes matched the files when first read, and the target-receipt SHA256 stored by the outer receipt matched the inner receipt's actual bytes. Scope progress wording and wrapper summary lookup were subsequently corrected, so final closure must use a fresh receipt from the established refresh entry point. The old input fingerprint cannot be presented as evidence for new inputs. The leaf-source hash remains the `f9cfae…` value above.

Precompiled cache loads pinned dependencies; local build and declaration checks provide machine evidence for current paper modules and 5 registered declarations. They neither reverify all dependency source nor judge paper semantics or whole-paper coverage. The checker-generated `.paper-verification` is excluded from its own input snapshot. The outer receipt binds the inner receipt without the reverse self-binding; no circular evidence-hash dependency was found. The original checker also includes existing `.lean` probes under `.project-verification` in its snapshot, so later changes to those probes change its input fingerprint and prevent silent reuse of the old fingerprint.

**Corrected item:** the initially reviewed `check_project.py` used `target_result.get("input_fingerprint")`, but the original receipt stores the value at `target_result["inputs"]["input_fingerprint"]`, leaving the outer summary field null. The SHA256 binding of the complete target receipt remained valid at that time. The wrapper now reads the nested field directly, failing through the existing `KeyError` path if absent. The original checker is unchanged. The final established-entry rerun will refresh the outer receipt, and the integrator must confirm a 64-character summary equal to the original receipt's value.

## Scope, confirmation, and closure

Scope contains only 5 supporting targets. The completion count for the 17 original numbered results remains 0; `unnum:quadratic-symbol-algebra` remains `partially_formalized`. README and Overview do not claim that the main theorem or whole paper is proved. The outer `paper_formalization_verified` and `semantic_correspondence_verified` remain false. The original checker does not itself check the paper hash; the outer provenance check already performed carries that responsibility.

An appended independent readback record for the current source already exists. It reports a project-environment probe exit of 0 and type/axiom output unchanged from before formatting. This integration review does not replace that mathematical review. User/author confirmation still awaits an actual reply; the final trust policy is still undecided. Remote CI for a real new commit remains distinct from the old initialization CI.

The five scope support entries were checked as updated to local machine pass and independent project-environment recompilation pass. Author confirmation remains pending and the parent remains partial. Close review records/new-commit CI against final actual evidence. This record replaces neither the final entry-point refresh nor actual CI results. If the configuration or source changes afterward, update the relevant hashes and machine records.
