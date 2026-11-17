# Research behind this standard

[Chinese source](sources.zh-CN.md)

This document records the research conducted on November 14, 2026. Check current rules for the specific journal before submission. The findings describe the pages inspected and the community examples considered at that time.

## Journal guidance

The official pages inspected did not list a Lean requirement, a proof-assistant requirement, or a paragraph-level formalization coverage threshold.

- [Communications in Mathematical Physics](https://link.springer.com/journal/220/submission-guidelines)
- [Annales Henri Poincaré](https://link.springer.com/journal/23/submission-guidelines)
- [Letters in Mathematical Physics](https://link.springer.com/journal/11005/submission-guidelines)
- [Archive for Rational Mechanics and Analysis](https://link.springer.com/journal/205/submission-guidelines)
- [Journal of Mathematical Physics editorial policies](https://pubs.aip.org/aip/jmp/pages/policies)
- [Journal of Physics A](https://publishingsupport.iopscience.iop.org/journals/journal-of-physics-a-mathematical-and-theoretical/)
- [Classical and Quantum Gravity](https://publishingsupport.iopscience.iop.org/journals/classical-and-quantum-gravity/)
- [Nonlinearity](https://publishingsupport.iopscience.iop.org/journals/nonlinearity/)

Data and code availability provisions address sharing. IOP also distinguishes supplementary material from the usual scope of peer review. Attribute verification of the formalization to the evidence that actually supports it.

The specialist journal AFM calls for a formal artifact and links between informal and formal statements, with at least the main result linked to code. It values generality and library integration where appropriate. These criteria neither guarantee acceptance of a main-result artifact nor impose mathlib submission standards in every case. [AFM author instructions](https://afm.episciences.org/page/instructions-for-authors) · [Aims and scope](https://afm.episciences.org/page/aims-and-scope)

## Community checks and examples

- A versioned project, an actual build, an axiom audit, and correspondence between the claimed and proved results all matter. [Lean community: Did you prove it?](https://leanprover-community.github.io/did_you_prove_it.html)
- `formalization.yaml` is a format for reporting coverage, differences, dependencies, and review status. [Project format](https://github.com/mathlib-initiative/formalization.yaml)
- PFR records specific completed results and corollaries left outside scope. This survey read the status declaration. [PFR scope record](https://github.com/teorth/pfr/blob/master/formalization.yaml)
- Thomas Bloom, Eric Wieser, and others discussed submission experiences in 2023. These are individual accounts. [Community discussion](https://leanprover-community.github.io/archive/stream/113488-general/topic/merging.20formalization.20into.20the.20original.20paper.html)

The resulting standard covers all formal mathematical results and their necessary dependencies, with accurate objects, assumptions, conclusions, and version references. The scope is defined independently of stricter whole-text standards and narrower local standards.
