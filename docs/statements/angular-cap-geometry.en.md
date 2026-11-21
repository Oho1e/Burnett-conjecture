# Angular caps and the signed phase gap

[简体中文](angular-cap-geometry.zh-CN.md)

This delivery corresponds to lines 893–1025 of the locked manuscript.

- The cyclic low-slot weights and the comparable weight form a nonnegative partition for a triad of nonzero frequencies summing to zero. Comparable thin-cone triads satisfy a uniform projective angular bound.
- For a fixed compact family of Lorentz forms, the construction gives a finite projective null-cap cover with both signed lifts and smooth base and enlarged caps. The overlap is uniformly bounded, and the cap count is at most a constant times $\delta^{-2}$. Both kinds of caps satisfy uniform derivative bounds in the parabolically rescaled coordinates.
- For a fixed finite-dimensional field fiber and each finite real $p>1$, the base and enlarged caps have uniform individual $L^p$ bounds. For every fixed finite $p_*>3$, the cap family satisfies the field $L^3$ sum estimate with counting factor $N_\delta^{1/(3(p_*-2))}$. The constants are uniform over the compact family and the allowed cap widths.
- The absolute value of the exact signed phase $q_m(p+q)-q_m(q)$ is bounded below by $b\delta^2|p||q|$ on the low-far portion. The Lean hypotheses retain the thin-cone conditions on all three frequencies and the nonvanishing low-far weight.

The nine supporting declarations below serve the near-angle lemma and the construction of the physical far-angle correction. Those results remain open, and author confirmation is pending.

- `Burnett.Analysis.ProjectiveNullCaps.triad_cutoff_partition_nonnegative`
- `Burnett.Analysis.ProjectiveNullCaps.exists_uniform_comparable_nearNull_wedge`
- `Burnett.Analysis.ProjectiveNullCaps.exists_uniform_lowFar_signedQuadraticPhase_gap`
- `Burnett.Analysis.ProjectiveNullCaps.exists_uniform_projective_null_caps`
- `Burnett.Analysis.ProjectiveNullCaps.exists_smooth_thinCone_capMultipliers`
- `Burnett.Analysis.ProjectiveNullCaps.actual_capMultiplier_parabolic_jets`
- `Burnett.Analysis.ProjectiveNullCaps.actual_enlargedCapMultiplier_parabolic_jets`
- `Burnett.Analysis.CapFourier.exists_uniform_actual_capMultiplier_fieldLp`
- `Burnett.Analysis.CapFourier.exists_uniform_actual_capMultipliers_field_angular_L3`

[Shared source bindings](angular-cap-geometry-source-bindings.json)
