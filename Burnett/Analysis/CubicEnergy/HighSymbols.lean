import Burnett.Analysis.CubicEnergy.FrequencySplit

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit

open Filter Set Burnett.RicciSymbol
open scoped Topology ContDiff

private theorem lowWeight_contDiffAt {p : E × E} (hp : p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : E × E => lowWeight q.1 q.2) p :=
  (lowWeight_contDiffOn p hp).contDiffAt ((isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set (E × E))).mem_nhds hp)

/-- A neighborhood of the entire nonzero second-frequency axis has zero high cutoff. -/
theorem eventually_lowWeight_one {p : E × E} (hη : p.1 = 0) (hp : p ≠ 0) :
    ∀ᶠ q : E × E in 𝓝 p, lowWeight q.1 q.2 = 1 := by
  have hξ : p.2 ≠ 0 := fun h => hp (Prod.ext hη h)
  have hlt : 8 * ‖p.1‖ < ‖p.2‖ := by simpa [hη] using norm_pos_iff.mpr hξ
  have hnb := (isOpen_lt (continuous_const.mul continuous_fst.norm) continuous_snd.norm).mem_nhds hlt
  filter_upwards [hnb] with q hq
  have hqξ : q.2 ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (by positivity) hq)
  exact lowWeight_eq_one hqξ hq.le

theorem high_frequency_separation {η ξ : E} (h : 1-lowWeight η ξ ≠ 0) :
    (‖η‖+‖ξ‖)/9 ≤ ‖η‖ := by
  by_cases hx : ξ = 0
  · simp [hx]
    linarith [norm_nonneg η]
  · have ht : ¬8*‖η‖ ≤ ‖ξ‖ := fun bad => h (by rw [lowWeight_eq_one hx bad]; ring)
    linarith

private theorem high_contDiffAt (f : E × E → ℝ) (hf : ContDiff ℝ ∞ f) {p : E × E} (hp : p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : E × E => (1-lowWeight q.1 q.2)*f q / ‖q.1‖) p := by
  by_cases hη : p.1 = 0
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lowWeight_one hη hp] with q hq
    simp [hq]
  · exact ((contDiffAt_const.sub (lowWeight_contDiffAt hp)).mul hf.contDiffAt).div
      (contDiffAt_fst.norm ℝ hη) (norm_ne_zero_iff.mpr hη)

theorem productSymbol_contDiffOn (j : Index) :
    ContDiffOn ℝ ∞ (fun p : E × E => productSymbol j p.1 p.2) {p | p ≠ 0} := by
  intro p hp
  exact (high_contDiffAt (fun q => (q.1+q.2) j)
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (contDiff_fst.add contDiff_snd)) hp).contDiffWithinAt

theorem inputSymbol_contDiffOn (j : Index) :
    ContDiffOn ℝ ∞ (fun p : E × E => inputSymbol j p.1 p.2) {p | p ≠ 0} := by
  intro p hp
  exact (high_contDiffAt (fun q => q.2 j)
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp contDiff_snd) hp).contDiffWithinAt

theorem highSymbols_scale (j : Index) (t : ℝ) (ht : 0 < t) (η ξ : E) :
    productSymbol j (t • η) (t • ξ) = productSymbol j η ξ ∧
    inputSymbol j (t • η) (t • ξ) = inputSymbol j η ξ := by
  have ht0 := ht.ne'
  have hsum : (t • η + t • ξ) j = t * (η+ξ) j := by rw [← smul_add]; rfl
  have hξ : (t • ξ) j = t * ξ j := rfl
  simp only [productSymbol,inputSymbol,lowWeight_scale t ht,norm_smul,Real.norm_eq_abs,
    abs_of_pos ht,hsum,hξ]
  have cancel (a z v : ℝ) : a * (t*z) / (t*v) = a*z/v := by
    rw [show a*(t*z) = t*(a*z) by ring, mul_div_mul_left _ _ ht0]
  exact ⟨cancel _ _ _,cancel _ _ _⟩

theorem homogeneous_value_zero {b : E → ℝ}
    (hb : ∀ (t : ℝ), 0 < t → ∀ z, b (t • z) = t * b z) : b 0 = 0 := by
  have h := hb 2 (by norm_num) 0
  rw [smul_zero] at h
  linarith

theorem angularComponent_contDiffOn (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (j : Index) :
    ContDiffOn ℝ ∞ (angularComponent b j) {x | x ≠ 0} := by
  exact (hb.mul (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffOn).div
    (contDiff_norm_sq ℝ).contDiffOn (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

theorem angularComponent_scale {b : E → ℝ}
    (hb : ∀ (t : ℝ), 0 < t → ∀ z, b (t • z) = t * b z)
    (j : Index) (t : ℝ) (ht : 0 < t) (z : E) :
    angularComponent b j (t • z) = angularComponent b j z := by
  have ht0 := ht.ne'
  have hz : (t • z) j = t * z j := rfl
  simp only [angularComponent,hb t ht,hz,norm_smul,Real.norm_eq_abs,abs_of_pos ht,mul_pow]
  by_cases h : ‖z‖ = 0
  · simp [h]
  · field_simp

end Burnett.A02.FrequencySplit
