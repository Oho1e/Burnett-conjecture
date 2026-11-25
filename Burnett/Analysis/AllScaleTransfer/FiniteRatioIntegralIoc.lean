import Burnett.Analysis.AllScaleTransfer.FiniteRatioIntegral

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.Analysis.LowRatio

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

private abbrev Jet (j : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) ℂ

/-- The same fixed ratio integral may be differentiated when the hypotheses
on its integrands hold on (0,1]. The endpoint zero has zero volume. -/
theorem timeAverage_contDiffOn_and_jets_of_Ioc {D : Set Point} (hD : IsOpen D) (n : ℕ)
    (u : ℝ → Point → ℂ) (bound : ℕ → ℝ)
    (smooth : ∀ t ∈ Ioc (0 : ℝ) 1, ContDiffOn ℝ n (u t) D)
    (meas : ∀ j ≤ n, ∀ z ∈ D,
      ContinuousOn (fun t => iteratedFDeriv ℝ j (u t) z) (Ioc (0 : ℝ) 1))
    (uniform : ∀ j ≤ n, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ z ∈ D,
      ‖iteratedFDeriv ℝ j (u t) z‖ ≤ bound j) :
    ContDiffOn ℝ n (timeAverage u) D ∧
      (∀ j ≤ n, ∀ z ∈ D,
        iteratedFDeriv ℝ j (timeAverage u) z =
          ∫ t in Ioc (0 : ℝ) 1, iteratedFDeriv ℝ j (u t) z) ∧
      ∀ j ≤ n, ∀ z ∈ D, ‖iteratedFDeriv ℝ j (timeAverage u) z‖ ≤ bound j := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let p (z : Point) (j : ℕ) : Jet j := ∫ t, iteratedFDeriv ℝ j (u t) z ∂μ
  have aeTime : ∀ᵐ t ∂μ, t ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have iBound (j : ℕ) : Integrable (fun _ : ℝ => bound j) μ :=
    integrableOn_const measure_Ioc_lt_top.ne
  have iJet (j : ℕ) (hj : j ≤ n) (z : Point) (hz : z ∈ D) :
      Integrable (fun t => iteratedFDeriv ℝ j (u t) z) μ :=
    (iBound j).mono' ((meas j hj z hz).aestronglyMeasurable measurableSet_Ioc)
      (aeTime.mono fun t ht => uniform j hj t ht z hz)
  have component_cont (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (j : ℕ) (hj : j ≤ n) :
      ContinuousOn (iteratedFDeriv ℝ j (u t)) D := by
    have h := (smooth t ht).continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hD.uniqueDiffOn
    apply h.congr
    intro z hz
    exact (iteratedFDerivWithin_of_isOpen j hD hz).symm
  have cont (j : ℕ) (hj : j ≤ n) : ContinuousOn (fun z => p z j) D := by
    apply continuousOn_of_dominated (bound := fun _ : ℝ => bound j)
    · exact fun z hz => (iJet j hj z hz).aestronglyMeasurable
    · intro z hz
      exact aeTime.mono fun t ht => uniform j hj t ht z hz
    · exact iBound j
    · exact aeTime.mono fun t ht => component_cont t ht j hj
  have derivative (j : ℕ) (hj : j < n) (z : Point) (hz : z ∈ D) :
      HasFDerivAt (fun w => p w j) (p z (j + 1)).curryLeft z := by
    letI : NormedAddCommGroup (Point →L[ℝ] Jet j) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (Point →L[ℝ] Jet j) := ContinuousLinearMap.toNormedSpace
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Point) ℂ
    let L := C.toContinuousLinearEquiv.toContinuousLinearMap
    let G (w : Point) (t : ℝ) := C (iteratedFDeriv ℝ (j + 1) (u t) w)
    have hG (w : Point) (t : ℝ) :
        G w t = fderiv ℝ (iteratedFDeriv ℝ j (u t)) w := rfl
    have hs : j + 1 ≤ n := hj
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD z hz
    have near : ∀ᶠ w in 𝓝 z, w ∈ D := hD.mem_nhds hz
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
      (F := fun w t => iteratedFDeriv ℝ j (u t) w) (F' := G)
      (bound := fun _ : ℝ => bound (j + 1)) hε
      (near.mono fun w hw => (iJet j hj.le w hw).aestronglyMeasurable)
      (iJet j hj.le z hz)
      (C.continuous.comp_aestronglyMeasurable (iJet (j + 1) hs z hz).aestronglyMeasurable)
      (aeTime.mono fun t ht w hw => by
        simpa only [G, LinearIsometryEquiv.norm_map] using uniform (j + 1) hs t ht w (hball hw))
      (iBound (j + 1))
      (aeTime.mono fun t ht w hw => by
        rw [hG]
        have hLt : (j : WithTop ℕ∞) < n := by exact_mod_cast hj
        exact (((smooth t ht).contDiffAt (hD.mem_nhds (hball hw))).differentiableAt_iteratedFDeriv
          hLt).hasFDerivAt)
    have commute : (∫ t, G z t ∂μ) = (p z (j + 1)).curryLeft := by
      change (∫ t, L (iteratedFDeriv ℝ (j + 1) (u t) z) ∂μ) = _
      exact ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (Fₗ := Point →L[ℝ] Jet j) L (iJet (j + 1) hs z hz)
    rwa [commute] at h
  have zer (z : Point) (hz : z ∈ D) : (p z 0).curry0 = timeAverage u z := by
    let C := (continuousMultilinearCurryFin0 ℝ Point ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    unfold timeAverage Time
    rw [integral_Icc_eq_integral_Ioc]
    change C (∫ t, iteratedFDeriv ℝ 0 (u t) z ∂μ) = ∫ t, u t z ∂μ
    rw [← C.integral_comp_comm (iJet 0 (Nat.zero_le n) z hz)]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by simp [C, iteratedFDeriv_zero_eq_comp]
  have s : HasFTaylorSeriesUpToOn n (timeAverage u) p D := by
    refine ⟨zer, ?_, ?_⟩
    · intro j hj z hz
      have hJ : j < n := by exact_mod_cast hj
      exact (derivative j hJ z hz).hasFDerivWithinAt
    · intro j hj
      exact cont j (by exact_mod_cast hj)
  have eq (j : ℕ) (hj : j ≤ n) (z : Point) (hz : z ∈ D) :
      iteratedFDeriv ℝ j (timeAverage u) z = p z j := by
    rw [← iteratedFDerivWithin_of_isOpen j hD hz]
    exact (s.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hj) hD.uniqueDiffOn hz).symm
  refine ⟨s.contDiffOn, eq, ?_⟩
  intro j hj z hz
  rw [eq j hj z hz]
  calc
    ‖p z j‖ ≤ ∫ t, ‖iteratedFDeriv ℝ j (u t) z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _t, bound j ∂μ :=
      integral_mono_ae (iJet j hj z hz).norm (iBound j)
        (aeTime.mono fun t ht => uniform j hj t ht z hz)
    _ = bound j := by simp [μ, integral_const, measureReal_def, Real.volume_Ioc]

end Burnett.Analysis.LowRatio
