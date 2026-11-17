# Engineering integration and machine checks

[Chinese source](engineering.zh-CN.md)

The portable checker uses Python 3.10+ with its standard library and a configured Lean/Lake project. Reuse existing equivalents and project rules. Keep the current directory layout and dependency pins unless a change is needed and authorized.

## Create or connect a repository

The pinned VectorFieldMethod snapshot illustrates a root library entry, namespace directories, modules grouped by mathematical mechanism, statement documents with actual Lean types, fixed dependencies, and CI. [Reference snapshot](https://github.com/Oho1e/VectorFieldMethod/tree/29807637096adbed7ee08b31a1e3c360123b3f3d)

```text
<PaperLean>.lean                 library entry
<PaperLean>/                     definitions, lemmas, and paper results
paper/                           authorized manuscript snapshot and hashes
docs/statements/                 mathematical statements, context, and actual Lean types
docs/formalization/              scope, review, and standard snapshot
lean-toolchain                   pinned Lean toolchain
lakefile.toml / lakefile.lean     build and dependency configuration
lake-manifest.json               dependency lock
scripts/check_paper.py           target origin and transitive axiom audit
.github/workflows/               project CI
README.md                        manuscript identity, status, build, and review links
```

The checker resolves `Foo.Bar` to `<repo>/Foo/Bar.lean`. Use a subordinate project as the `--repo` root when appropriate. Adapt and test custom `srcDir` layouts. Set pins based on real compatibility. Upstream mathlib conventions, global warnings as errors, and zero placeholders in all exploratory files are optional. Keep the README accurate about coverage, progress, open interfaces, and review status.

When authorized, check owner/name, visibility, and the proposed files, then push and observe CI. Otherwise proceed locally as applicable. Include project sources, configuration, and relevant documents. Preserve the authorized manuscript distribution scope and exclude credentials, build caches, and unrelated workspace files. Follow the project's PR and human merge boundaries. [PR process](github-pr.en.md) · [PR template](../assets/repo-template/.github/pull_request_template.md)

An initialization check may precede real targets. The original target checker rejects empty target lists. Once paper targets exist, run their exact audit. Record a local machine pass as development evidence of its actual coverage.

## Integrate into an existing project

1. Merge the needed files from `assets/repo-template/` with existing configuration.
2. Copy `scripts/check_paper.py` to the corresponding project path if needed.
3. Record actual paper identity, formal results, `standard.id`, `standard.version`, the standard hash, and `scope.coverage`.
4. Run the checker with the pinned Lean and mathlib.

```powershell
python scripts/check_paper.py --repo .
```

For an existing local SDK, pass `--lake 'D:\path\to\lean-sdk\bin\lake.exe'`. The checker uses the configured project. A dependency-free project may generate its initial manifest with `lake build`. For mathlib, prepare the pinned dependencies and cache. Resolve cache problems within the existing dependency configuration.

Use UTF-8 explicitly for Windows wrappers that print Chinese or Lean Unicode. If PowerShell blocks a wrapper, use the Python entry directly. Judge verification by actual commands, exit codes, and logs.

## Manifest fields

- `standard` binds the approved interpretation and version. Record a user decision for a standard change.
- `scope.kind: paper-results` is a technical enum. `scope.coverage: formal-results-and-dependency-closure` and the standard identity specify coverage together.
- `targets` lists the final theorem declarations to find and audit. Split one manuscript claim into subtargets when needed and name each actual defining module.
- `inventory` covers the paper's formal results, necessary definitions, and dependencies. Inventory the paper directly. Reuse matching library results and group routine work under actual proof blocks.
- The checker supports dotted ASCII module and declaration names. For Unicode names, provide corresponding ASCII declarations or adapt and test the checker.
- An all-zero manuscript hash is an unconfigured placeholder and fails the checker. Use the actual source identity and hashes.

Build all implementation modules. One final entry can import them and contain a registered target, or use equivalent build evidence. Audit the actual implementation and dependencies of definitions and calculations outside all registered dependency closures.

## What the checker covers

It builds target modules, checks theorem existence and defining module, and audits transitive axioms. The standard configuration allows `propext`, `Classical.choice`, and `Quot.sound`. Generated audit inputs are ordinary Lean files, preserving the proof visibility needed by the audit.

The output under `.paper-verification/` records runtime, build, axioms, actual types, and `result.json`. The checker rejects discrepancies with a pinned release. Establish custom and nightly identities separately. Hashes cover actual bytes. Align line endings across Windows and Linux when preparing the repository.

The standalone script reports only machine criteria. Manuscript identity, complete scope, semantic correspondence, and authorization of trust policy have separate evidence. Standalone output includes `paper_hash_verified: false` and `semantic_correspondence_verified: false`. A `selected-results` manifest can support development checks.

Include actual project source files in the input snapshot, including untracked and ignored files in real source directories. Declare generated roots explicitly, such as `--generated-root .project-verification`, and keep actual source/imports outside them. The checker verifies the boundary and rejects ambiguous overlaps. Keep auxiliary probe and log hashes separately.

Version 1.3.1 was tested on Lean 4.24.0. When excluding a generated root, the checker inspects actual loaded modules and source/olean paths for targets and the extra `--entry-module`, and requires project sources in the snapshot. Custom Lake layouts with multiple source roots need separate adaptation and testing. Conservative scanning or external probe directories remain available.

Maintenance regressions cover source membership, effective source changes and untracked imported sources, changing inputs during a run, and rejection at the intended build/axiom phase. A failing target alone gives limited snapshot evidence. Readiness and protection comparisons can use offline failure samples. Apply maintenance tests to affected tooling.

Dependency lock hashes identify the intended dependencies. Reproduce completion from a clean checkout with pinned sources. Record reproducible version/source or hashes for path dependencies. Precompiled pinned libraries are part of ordinary engineering trust. Independent kernel replay is a separate check.

## CI and evidence reuse

The template pins Lean, prepares usable mathlib caches, runs the target checker, and uploads evidence including explicitly allowed hidden directories. It has read-only repository permissions. When remote CI is part of delivery, record actual runs. Local delivery uses local evidence. Public verification statements bind fixed manuscript and code versions.

Version 1.2 reran 20 checker cases on Lean 4.24.0 and added a regression requiring the expected axiom rejection stage. This is historical evidence. Version 1.3.1 maintenance evidence has its own commands, exit codes, and inputs. Separate document review, offline function cases, actual Lean checks, and remote CI. Check intended failure stages and key diagnostics. These cases cover the specific tested version and inputs.

The paper's formal results and necessary dependencies must have no undisclosed gaps. Upstream API design, global warning rules, and an upstream submission are optional.
