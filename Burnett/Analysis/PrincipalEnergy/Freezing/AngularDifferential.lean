import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff Interval Topology

/-- The angular differential of the degree-one symbol, extended by zero at
the single frequency where the symbol can fail to be smooth. -/
def angularDifferential (b : E → ℝ) (v ξ : E) : ℝ :=
  if ξ = 0 then 0 else fderiv ℝ b ξ v

theorem angular_differential_contDiffOn (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0}) (v : E) :
    ContDiffOn ℝ ∞ (angularDifferential b v) {ξ | ξ ≠ 0} := by
  apply ((hb.fderiv_of_isOpen isClosed_singleton.isOpen_compl (by simp)).clm_apply
    (g := fun _ => v) contDiffOn_const).congr
  intro ξ hξ
  exact if_neg hξ

theorem angular_differential_homogeneous (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (v : E) (t : ℝ) (ht : 0 < t) (ξ : E) :
    angularDifferential b v (t • ξ) = angularDifferential b v ξ := by
  by_cases hx : ξ = 0
  · simp [hx]
  let U : Set E := {x | x ≠ 0}
  have ho : IsOpen U := isClosed_singleton.isOpen_compl
  have diff (z : E) (hz : z ≠ 0) : DifferentiableAt ℝ b z :=
    ((hb.differentiableOn (by simp)) z hz).differentiableAt (ho.mem_nhds hz)
  let A : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  have htx : t • ξ ≠ 0 := smul_ne_zero ht.ne' hx
  have h₁ : HasFDerivAt (b ∘ A) ((fderiv ℝ b (t • ξ)).comp A) ξ :=
    (diff _ htx).hasFDerivAt.comp ξ A.hasFDerivAt
  have h₂ := (diff ξ hx).hasFDerivAt.const_smul t
  have he : b ∘ A = fun z => t • b z := funext (hom t ht)
  rw [he] at h₁
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (h₁.unique h₂)
  change (fderiv ℝ b (t • ξ)) (t • v) = t * (fderiv ℝ b ξ v) at hh
  rw [map_smul, smul_eq_mul] at hh
  simpa only [angularDifferential, if_neg htx, if_neg hx] using mul_left_cancel₀ ht.ne' hh

theorem angular_differential_sphere_jet (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0}) (v : E) {D : ℝ} {N : ℕ}
    (jet : ∀ n : ℕ, n ≤ N + 1 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
    ‖iteratedFDeriv ℝ n (angularDifferential b v) ξ‖ ≤ ‖v‖ * D := by
  let U : Set E := {x | x ≠ 0}
  have ho : IsOpen U := isClosed_singleton.isOpen_compl
  have hx : ξ ∈ U := ne_of_mem_sphere hξ (by norm_num)
  have eq : (angularDifferential b v) =ᶠ[𝓝 ξ] (fun x => fderiv ℝ b x v) := by
    filter_upwards [ho.mem_nhds hx] with x hx
    exact if_neg hx
  rw [(eq.iteratedFDeriv ℝ n).eq_of_nhds]
  have smooth : ContDiffOn ℝ ∞ (fderiv ℝ b) U := hb.fderiv_of_isOpen ho (by simp)
  have d := smooth.contDiffAt (ho.mem_nhds hx)
  have order : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  exact (norm_iteratedFDeriv_clm_apply_const (c := v) d order).trans
    (by rw [norm_iteratedFDeriv_fderiv]; exact mul_le_mul_of_nonneg_left (jet _ (by omega) _ hξ) (norm_nonneg _))

theorem angular_differential_bound (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (v : E) (D : ℝ) (hD : 0 ≤ D)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D)
    (ξ : E) : ‖angularDifferential b v ξ‖ ≤ ‖v‖ * D := by
  by_cases hξ : ξ = 0
  · simpa [angularDifferential, hξ] using mul_nonneg (norm_nonneg v) hD
  let u := ‖ξ‖⁻¹ • ξ
  have hu : u ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right, u] using norm_smul_inv_norm (𝕜 := ℝ) hξ
  have h := angular_differential_homogeneous b hb hom v ‖ξ‖⁻¹
    (inv_pos.mpr (norm_pos_iff.mpr hξ)) ξ
  change angularDifferential b v u = _ at h
  have du : u ≠ 0 := ne_of_mem_sphere hu (by norm_num)
  calc
    _ = ‖fderiv ℝ b u v‖ := by rw [← h, angularDifferential, if_neg du]
    _ ≤ ‖fderiv ℝ b u‖ * ‖v‖ := (fderiv ℝ b u).le_opNorm v
    _ ≤ ‖v‖ * D := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] using jet u hu

private theorem degree_one_continuous (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) :
    Continuous b := by
  have b0 := hom 2 (by norm_num) (0 : E)
  simp only [smul_zero] at b0
  have hz : b 0 = 0 := by linarith
  obtain ⟨A, hA, bound⟩ := compact_sphere_jet 0 b hb
  have growth (ξ : E) : ‖b ξ‖ ≤ A * ‖ξ‖ := by
    by_cases eq : ξ = 0
    · simp [eq, hz]
    let u := ‖ξ‖⁻¹ • ξ
    have hξ := norm_pos_iff.mpr eq
    have hu : u ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere, dist_zero_right, u] using norm_smul_inv_norm (𝕜 := ℝ) eq
    have repr : ‖ξ‖ • u = ξ := smul_inv_smul₀ hξ.ne' ξ
    rw [← repr, hom _ hξ u, norm_mul, Real.norm_of_nonneg hξ.le, norm_smul, Real.norm_of_nonneg hξ.le]
    have bu : ‖b u‖ ≤ A := by simpa only [norm_iteratedFDeriv_zero] using bound 0 le_rfl u hu
    have un : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
    rw [un, mul_one]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left bu hξ.le
  apply continuous_iff_continuousAt.mpr
  intro ξ
  by_cases eq : ξ = 0
  · subst ξ
    rw [ContinuousAt, hz]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hN : Tendsto (fun x : E => A * ‖x‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
      have h : ContinuousAt (fun x : E => A * ‖x‖) (0 : E) :=
        (continuous_const.mul continuous_norm).continuousAt
      change Tendsto _ _ (𝓝 (A * ‖(0 : E)‖)) at h
      simpa only [norm_zero, mul_zero] using h
    exact squeeze_zero (fun _ => norm_nonneg _) growth hN
  · exact hb.continuousOn.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds eq)

/-- The segment formula remains valid at arbitrarily small frequencies.
A nonconstant affine line meets the singular frequency at most once. -/
theorem angular_differential_integral_eq (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (v ξ : E) :
    (∫ t in (0 : ℝ)..1, angularDifferential b v (ξ + t • v)) = b (ξ + v) - b ξ := by
  by_cases hv : v = 0
  · subst v
    have zero (x : E) : angularDifferential b 0 x = 0 := by
      by_cases h : x = 0 <;> simp [angularDifferential, h]
    simp only [zero, intervalIntegral.integral_zero, smul_zero, add_zero, sub_self]
  let A := fun t : ℝ => ξ + t • v
  let s := A ⁻¹' {0}
  have inj : Function.Injective A := fun a c eq => smul_left_injective ℝ hv (add_left_cancel eq)
  have hs : s.Countable := (countable_singleton _).preimage inj
  have cA : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  have hc : Continuous (b ∘ A) := (degree_one_continuous b hb hom).comp cA
  have hd : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max 0 1) \ s,
      HasDerivAt (b ∘ A) (angularDifferential b v (A t)) t := by
    intro t ht
    have hz : A t ≠ 0 := ht.2
    have loc : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
    have db := (hb.differentiableOn (by simp) (A t) hz).differentiableAt (loc.mem_nhds hz)
    have dA : HasDerivAt A v t := by
      have q := ((hasDerivAt_id t).smul_const v).const_add ξ
      simpa only [id, one_smul] using q
    simpa only [angularDifferential, if_neg hz] using db.hasFDerivAt.comp_hasDerivAt t dA
  have hmeas : Measurable (angularDifferential b v ∘ A) :=
    (measurable_of_continuousOn_compl_singleton 0 (angular_differential_contDiffOn b hb v).continuousOn).comp
      cA.measurable
  obtain ⟨D, hD, jet⟩ := compact_sphere_jet 1 b hb
  have hin : IntervalIntegrable (angularDifferential b v ∘ A) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact IntegrableOn.of_bound (by simp [Real.volume_Ioc]) hmeas.aestronglyMeasurable (‖v‖ * D)
      (Eventually.of_forall fun t => angular_differential_bound b hb hom v D hD (jet 1 le_rfl) (A t))
  have result := integral_eq_of_hasDerivAt_off_countable (b ∘ A) (angularDifferential b v ∘ A) hs
    hc.continuousOn hd hin
  simpa only [Function.comp_apply, A, one_smul, zero_smul, add_zero] using result

end Burnett.A03
