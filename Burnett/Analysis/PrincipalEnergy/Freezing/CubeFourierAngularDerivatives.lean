import Burnett.Analysis.SpatialFreezing.FixedCubeFourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Filter Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff Topology RealInnerProductSpace

private theorem cube_measurable (P : ℝ) : MeasurableSet (spatialFourierCube P) := by
  have eq : spatialFourierCube P =
      (WithLp.ofLp (p := 2)) ⁻¹' Icc (fun _ : Index => -P) (fun _ : Index => P) := by
    ext y
    change (∀ j : Index, -P ≤ y j ∧ y j ≤ P) ↔
      (∀ j : Index, -P ≤ y j) ∧ (∀ j : Index, y j ≤ P)
    exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩, fun h j => ⟨h.1 j, h.2 j⟩⟩
  rw [eq]
  exact measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (ι := Index)).measurable

private def phaseFactor (P : ℝ) (k : Index → ℤ) (y : CoordinateSpace) : ℂ :=
  Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I)

private theorem phase_continuous (P : ℝ) (k : Index → ℤ) : Continuous (phaseFactor P k) := by
  unfold phaseFactor spatialModePhase
  fun_prop

private theorem phase_norm (P : ℝ) (k : Index → ℤ) (y : CoordinateSpace) :
    ‖phaseFactor P k y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem integrable_weighted (P : ℝ) (k : Index → ℤ) (f : CoordinateSpace → F)
    (hf : Integrable f ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P))) :
    Integrable (fun y => phaseFactor P k y • f y)
      ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)) := by
  refine hf.norm.mono' ((phase_continuous P k).aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun y => by rw [norm_smul, phase_norm, one_mul]

private theorem cube_coefficient_linear_map
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (P : ℝ) (k : Index → ℤ) (L : F →L[ℝ] G)
    (hComplex : ∀ (z : ℂ) (v : F), L (z • v) = z • L v)
    (f : CoordinateSpace → F)
    (hf : Integrable f ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P))) :
    L (spatialCubeFourierCoefficient P k f) =
      spatialCubeFourierCoefficient P k (L ∘ f) := by
  change L (((2 * P) ^ 4)⁻¹ • ∫ y in spatialFourierCube P, phaseFactor P k y • f y) =
    ((2 * P) ^ 4)⁻¹ • ∫ y in spatialFourierCube P, phaseFactor P k y • (L ∘ f) y
  rw [map_smul, ← L.integral_comp_comm (integrable_weighted P k f hf)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => hComplex (phaseFactor P k y) (f y)

omit [CompleteSpace F] in
private theorem derivative_cube_coefficient_on_ball (P : ℝ) (k : Index → ℤ)
    (u : CoordinateSpace → CoordinateSpace → F)
    (du : CoordinateSpace → CoordinateSpace → CoordinateSpace →L[ℝ] F)
    (angle : CoordinateSpace) (ε B : ℝ) (hε : 0 < ε)
    (hm : ∀ q ∈ ball angle ε, AEStronglyMeasurable (fun y => u y q)
      ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)))
    (hi : Integrable (fun y => u y angle) ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)))
    (hdm : AEStronglyMeasurable (fun y => du y angle)
      ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)))
    (hd : ∀ y ∈ spatialFourierCube P, ∀ q ∈ ball angle ε,
      HasFDerivAt (u y) (du y q) q)
    (hb : ∀ y ∈ spatialFourierCube P, ∀ q ∈ ball angle ε, ‖du y q‖ ≤ B) :
    HasFDerivAt (fun q => spatialCubeFourierCoefficient P k (fun y => u y q))
      (spatialCubeFourierCoefficient P k (fun y => du y angle)) angle := by
  let μ := (volume : Measure CoordinateSpace).restrict (spatialFourierCube P)
  haveI : IsFiniteMeasure μ := ⟨by
    change ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)) univ < ⊤
    rw [Measure.restrict_apply_univ, spatial_fourier_cube_volume]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top⟩
  let U (q y : CoordinateSpace) := phaseFactor P k y • u y q
  let DU (q y : CoordinateSpace) := phaseFactor P k y • du y q
  have hPhase : AEStronglyMeasurable (phaseFactor P k) μ := (phase_continuous P k).aestronglyMeasurable
  have hU : ∀ᶠ q in 𝓝 angle, AEStronglyMeasurable (U q) μ := by
    filter_upwards [ball_mem_nhds angle hε] with q hq
    exact hPhase.smul (hm q hq)
  have hUI : Integrable (U angle) μ := integrable_weighted P k _ hi
  have hDUM : AEStronglyMeasurable (DU angle) μ := hPhase.smul hdm
  have hBD : ∀ᵐ y ∂μ, ∀ q ∈ ball angle ε, ‖DU q y‖ ≤ B :=
    (ae_restrict_mem (cube_measurable P)).mono fun y hy q hq => by
      rw [show DU q y = phaseFactor P k y • du y q from rfl, norm_smul, phase_norm, one_mul]
      exact hb y hy q hq
  have hDeriv : ∀ᵐ y ∂μ, ∀ q ∈ ball angle ε, HasFDerivAt (fun z => U z y) (DU q y) q :=
    (ae_restrict_mem (cube_measurable P)).mono fun y hy q hq =>
      (hd y hy q hq).fun_const_smul (phaseFactor P k y)
  have hf := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) hε hU hUI hDUM hBD
    (integrable_const B) hDeriv
  exact hf.fun_const_smul (((2 * P) ^ 4)⁻¹)

/-- Each actual angular jet of the cube coefficient is the cube coefficient
of that angular jet. Local domination is required on the stated open
frequency region, with one bound on the whole cube in a frequency ball. -/
theorem iteratedFDeriv_spatial_cube_fourier_coefficient
    (P : ℝ) (k : Index → ℤ) (u : CoordinateSpace → CoordinateSpace → F)
    (U : Set CoordinateSpace) (hU : IsOpen U) (N : ℕ)
    (smooth : ∀ y ∈ spatialFourierCube P, ContDiffOn ℝ ∞ (u y) U)
    (measurable : ∀ j : ℕ, j ≤ N → ∀ angle ∈ U,
      AEStronglyMeasurable (fun y => iteratedFDeriv ℝ j (u y) angle)
        ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)))
    (locallyBounded : ∀ angle ∈ U, ∃ ε : ℝ, 0 < ε ∧ ball angle ε ⊆ U ∧
      ∃ B : ℝ, ∀ j : ℕ, j ≤ N → ∀ q ∈ ball angle ε, ∀ y ∈ spatialFourierCube P,
        ‖iteratedFDeriv ℝ j (u y) q‖ ≤ B) :
    ∀ j : ℕ, j ≤ N → ∀ angle ∈ U,
      iteratedFDeriv ℝ j (fun q => spatialCubeFourierCoefficient P k (fun y => u y q)) angle =
        spatialCubeFourierCoefficient P k (fun y => iteratedFDeriv ℝ j (u y) angle) := by
  let μ := (volume : Measure CoordinateSpace).restrict (spatialFourierCube P)
  haveI : IsFiniteMeasure μ := ⟨by
    change ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)) univ < ⊤
    rw [Measure.restrict_apply_univ, spatial_fourier_cube_volume]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top⟩
  have jetInt (j : ℕ) (hj : j ≤ N) (angle : CoordinateSpace) (hAngle : angle ∈ U) :
      Integrable (fun y => iteratedFDeriv ℝ j (u y) angle) μ := by
    obtain ⟨ε, hε, _, B, hb⟩ := locallyBounded angle hAngle
    refine (integrable_const B).mono' (measurable j hj angle hAngle) ?_
    exact (ae_restrict_mem (cube_measurable P)).mono fun y hy =>
      hb j hj angle (mem_ball_self hε) y hy
  let b : CoordinateSpace → F := fun q => spatialCubeFourierCoefficient P k (fun y => u y q)
  intro j
  induction j with
  | zero =>
    intro _ angle hAngle
    let D := continuousMultilinearCurryFin0 ℝ CoordinateSpace F
    let L := D.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let LInv := D.toContinuousLinearEquiv.toContinuousLinearMap
    have hLin (z : ℂ) (v : F) : L (z • v) = z • L v := by ext m; rfl
    have fInt : Integrable (fun y => u y angle) μ := by
      have h := LInv.integrable_comp (jetInt 0 (Nat.zero_le _) angle hAngle)
      have same : (fun y => LInv (iteratedFDeriv ℝ 0 (u y) angle)) = (fun y => u y angle) := by
        funext y
        change D (iteratedFDeriv ℝ 0 (u y) angle) = _
        rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact D.apply_symm_apply _
      rwa [same] at h
    change L (spatialCubeFourierCoefficient P k (fun y => u y angle)) =
      spatialCubeFourierCoefficient P k (L ∘ (fun y => u y angle))
    exact cube_coefficient_linear_map P k L hLin _ fInt
  | succ n ih =>
    intro hn angle hAngle
    have hn' : n ≤ N := (Nat.le_succ n).trans hn
    obtain ⟨ε, hε, inside, B, hB⟩ := locallyBounded angle hAngle
    let D := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => CoordinateSpace) F
    let jet (y q : CoordinateSpace) := iteratedFDeriv ℝ n (u y) q
    let djet (y q : CoordinateSpace) := fderiv ℝ (jet y) q
    letI : NormedAddCommGroup (CoordinateSpace →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinateSpace) F) :=
      ContinuousLinearMap.toNormedAddCommGroup
    have actual (y q : CoordinateSpace) : djet y q =
        D (iteratedFDeriv ℝ (n + 1) (u y) q) := by
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      exact (D.apply_symm_apply _).symm
    have hdMeas : AEStronglyMeasurable (fun y => djet y angle) μ := by
      simp only [actual]
      exact D.continuous.comp_aestronglyMeasurable (measurable (n + 1) hn angle hAngle)
    have hd (y : CoordinateSpace) (hy : y ∈ spatialFourierCube P) (q : CoordinateSpace)
        (hq : q ∈ ball angle ε) : HasFDerivAt (jet y) (djet y q) q := by
      have atQ := (smooth y hy).contDiffAt (hU.mem_nhds (inside hq))
      have hnInf : (n : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top n
      exact (atQ.differentiableAt_iteratedFDeriv hnInf).hasFDerivAt
    have hdBound (y : CoordinateSpace) (hy : y ∈ spatialFourierCube P) (q : CoordinateSpace)
        (hq : q ∈ ball angle ε) : ‖djet y q‖ ≤ B := by
      rw [actual, LinearIsometryEquiv.norm_map]
      exact hB (n + 1) hn q hq y hy
    have integrated := derivative_cube_coefficient_on_ball P k jet djet angle ε B hε
      (fun q hq => measurable n hn' q (inside hq)) (jetInt n hn' angle hAngle)
      hdMeas hd hdBound
    have localEq : iteratedFDeriv ℝ n b =ᶠ[𝓝 angle]
        (fun q => spatialCubeFourierCoefficient P k (fun y => jet y q)) := by
      filter_upwards [hU.mem_nhds hAngle] with q hq
      exact ih hn' q hq
    have hDInt : Integrable (fun y => djet y angle) μ := by
      refine (integrable_const B).mono' hdMeas ?_
      exact (ae_restrict_mem (cube_measurable P)).mono fun y hy =>
        hdBound y hy angle (mem_ball_self hε)
    let L := D.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hLin (z : ℂ) (v : CoordinateSpace →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinateSpace) F) :
        L (z • v) = z • L v := by ext m; rfl
    change iteratedFDeriv ℝ (n + 1) b angle = _
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      localEq.fderiv_eq, integrated.fderiv]
    change L (spatialCubeFourierCoefficient P k (fun y => djet y angle)) = _
    rw [cube_coefficient_linear_map P k L hLin (fun y => djet y angle) hDInt]
    congr 1

end Burnett.A03
