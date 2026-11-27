import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierAngularDerivatives

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Filter Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff Topology

private theorem measurable_spatial_fourier_cube (P : ℝ) : MeasurableSet (spatialFourierCube P) := by
  have eq : spatialFourierCube P =
      (WithLp.ofLp (p := 2)) ⁻¹' Icc (fun _ : Index => -P) (fun _ : Index => P) := by
    ext y
    change (∀ j : Index, -P ≤ y j ∧ y j ≤ P) ↔
      (∀ j : Index, -P ≤ y j) ∧ (∀ j : Index, y j ≤ P)
    exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩, fun h j => ⟨h.1 j, h.2 j⟩⟩
  rw [eq]
  exact measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (ι := Index)).measurable

/-- Finite-order frequency regularity of the same normalized cube
coefficient follows from the domination of its actual integrand jets. -/
theorem contDiffOn_spatial_cube_fourier_coefficient
    (P : ℝ) (k : Index → ℤ) (u : CoordinateSpace → CoordinateSpace → ℂ)
    (U : Set CoordinateSpace) (hU : IsOpen U) (H : ℕ)
    (smooth : ∀ y ∈ spatialFourierCube P, ContDiffOn ℝ ∞ (u y) U)
    (measurable : ∀ j : ℕ, j ≤ H → ∀ angle ∈ U,
      AEStronglyMeasurable (fun y => iteratedFDeriv ℝ j (u y) angle)
        ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)))
    (locallyBounded : ∀ angle ∈ U, ∃ ε : ℝ, 0 < ε ∧ ball angle ε ⊆ U ∧
      ∃ B : ℝ, ∀ j : ℕ, j ≤ H → ∀ q ∈ ball angle ε, ∀ y ∈ spatialFourierCube P,
        ‖iteratedFDeriv ℝ j (u y) q‖ ≤ B) :
    ContDiffOn ℝ (H : ℕ) (fun q => spatialCubeFourierCoefficient P k (fun y => u y q)) U := by
  let μ := (volume : Measure CoordinateSpace).restrict (spatialFourierCube P)
  haveI : IsFiniteMeasure μ := ⟨by
    change ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)) univ < ⊤
    rw [Measure.restrict_apply_univ, spatial_fourier_cube_volume]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top⟩
  let phase (y : CoordinateSpace) := Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I)
  have phaseCont : Continuous phase := by
    unfold phase spatialModePhase
    fun_prop
  have phaseMeas : AEStronglyMeasurable phase μ := phaseCont.aestronglyMeasurable
  have phaseNorm (y : CoordinateSpace) : ‖phase y‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  let b (q : CoordinateSpace) := spatialCubeFourierCoefficient P k (fun y => u y q)
  let G (j : ℕ) (q y : CoordinateSpace) := phase y • iteratedFDeriv ℝ j (u y) q
  have eqWithin (j : ℕ) (hj : j ≤ H) (q : CoordinateSpace) (hq : q ∈ U) :
      iteratedFDerivWithin ℝ j b U q = ((2 * P)^4)⁻¹ • ∫ y, G j q y ∂μ := by
    rw [iteratedFDerivWithin_of_isOpen j hU hq]
    exact iteratedFDeriv_spatial_cube_fourier_coefficient P k u U hU H smooth measurable locallyBounded j hj q hq
  have actualRegular (j : ℕ) (y : CoordinateSpace) (hy : y ∈ spatialFourierCube P)
      (q : CoordinateSpace) (hq : q ∈ U) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ j (u y)) q := by
    have hj : (j : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top j
    exact ((smooth y hy).contDiffAt (hU.mem_nhds hq)).differentiableAt_iteratedFDeriv hj
  have integrandMeas (j : ℕ) (hj : j ≤ H) (q : CoordinateSpace) (hq : q ∈ U) :
      AEStronglyMeasurable (G j q) μ := phaseMeas.smul (measurable j hj q hq)
  have integrandDom (j : ℕ) (q : CoordinateSpace)
      (B : ℝ) (bound : ∀ y ∈ spatialFourierCube P, ‖iteratedFDeriv ℝ j (u y) q‖ ≤ B) :
      ∀ᵐ y ∂μ, ‖G j q y‖ ≤ B := by
    apply (ae_restrict_mem (measurable_spatial_fourier_cube P)).mono
    intro y hy
    simpa only [G, norm_smul, phaseNorm, one_mul] using bound y hy
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn hU.uniqueDiffOn).2
  constructor
  · intro j hj
    have hCont : ContinuousOn (fun q => ((2 * P)^4)⁻¹ • ∫ y, G j q y ∂μ) U := by
      intro q hq
      obtain ⟨ε, hε, inside, B, hBound⟩ := locallyBounded q hq
      have hf : ∀ᶠ q' in 𝓝 q, AEStronglyMeasurable (G j q') μ := by
        filter_upwards [ball_mem_nhds q hε] with q' hq'
        exact integrandMeas j hj q' (inside hq')
      have hb : ∀ᶠ q' in 𝓝 q, ∀ᵐ y ∂μ, ‖G j q' y‖ ≤ B := by
        filter_upwards [ball_mem_nhds q hε] with q' hq'
        exact integrandDom j q' B (hBound j hj q' hq')
      have gc : ∀ᵐ y ∂μ, ContinuousAt (fun q' => G j q' y) q :=
        (ae_restrict_mem (measurable_spatial_fourier_cube P)).mono fun y hy =>
          (actualRegular j y hy q hq).continuousAt.const_smul (phase y)
      exact ((continuousAt_of_dominated hf hb (integrable_const B) gc).const_smul _).continuousWithinAt
    exact hCont.congr (fun q hq => eqWithin j hj q hq)
  · intro j hj
    have hj' : j ≤ H := hj.le
    have derivOn : DifferentiableOn ℝ (fun q => ((2 * P)^4)⁻¹ • ∫ y, G j q y ∂μ) U := by
      intro q hq
      obtain ⟨ε, hε, inside, B, hBound⟩ := locallyBounded q hq
      let D := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => CoordinateSpace) ℂ
      letI : NormedAddCommGroup (CoordinateSpace →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin j => CoordinateSpace) ℂ) :=
        ContinuousLinearMap.toNormedAddCommGroup
      letI : NormedSpace ℂ (CoordinateSpace →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin j => CoordinateSpace) ℂ) :=
        ContinuousLinearMap.toNormedSpace
      let g' (q' y : CoordinateSpace) := phase y • D (iteratedFDeriv ℝ (j + 1) (u y) q')
      have actual (y q' : CoordinateSpace) :
          D (iteratedFDeriv ℝ (j + 1) (u y) q') =
            fderiv ℝ (iteratedFDeriv ℝ j (u y)) q' := by
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
        exact D.apply_symm_apply _
      have hf : ∀ᶠ q' in 𝓝 q, AEStronglyMeasurable (G j q') μ := by
        filter_upwards [ball_mem_nhds q hε] with q' hq'
        exact integrandMeas j hj' q' (inside hq')
      have hInt : Integrable (G j q) μ :=
        (integrable_const B).mono' (integrandMeas j hj' q hq)
          (integrandDom j q B (hBound j hj' q (mem_ball_self hε)))
      have hDerivMeas : AEStronglyMeasurable (g' q) μ :=
        phaseMeas.smul (D.continuous.comp_aestronglyMeasurable (measurable (j + 1) hj q hq))
      have hDerivB : ∀ᵐ y ∂μ, ∀ q' ∈ ball q ε, ‖g' q' y‖ ≤ B :=
        (ae_restrict_mem (measurable_spatial_fourier_cube P)).mono fun y hy q' hq' => by
          simpa only [g', norm_smul, phaseNorm, one_mul, LinearIsometryEquiv.norm_map] using
            hBound (j + 1) hj q' hq' y hy
      have hDerivAt : ∀ᵐ y ∂μ, ∀ q' ∈ ball q ε, HasFDerivAt (fun t => G j t y) (g' q' y) q' :=
        (ae_restrict_mem (measurable_spatial_fourier_cube P)).mono fun y hy q' hq' => by
          simpa only [g', actual] using (actualRegular j y hy q' (inside hq')).hasFDerivAt.fun_const_smul (phase y)
      have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) hε
        hf hInt hDerivMeas hDerivB (integrable_const B) hDerivAt
      exact (h.fun_const_smul (((2 * P)^4)⁻¹)).differentiableAt.differentiableWithinAt
    exact derivOn.congr (fun q hq => eqWithin j hj' q hq)

end Burnett.A03
