import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Burnett.Analysis.LowRatio

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Interval

/-- Euclidean chart coordinates for the two signed three-sphere directions. -/
abbrev Angles := EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
abbrev Point := Angles × ℝ

abbrev Window (U : Set Angles) (a b : ℝ) : Set Point := U ×ˢ Ioo a b
abbrev Time : Set ℝ := Icc 0 1

def ratioScale (t : ℝ) : Point →L[ℝ] Point :=
  (ContinuousLinearMap.fst ℝ Angles ℝ).prod 0 +
    t • (0 : Point →L[ℝ] Angles).prod (ContinuousLinearMap.snd ℝ Angles ℝ)

@[simp] theorem ratioScale_apply (t : ℝ) (z : Point) :
    ratioScale t z = (z.1, t * z.2) := by
  simp [ratioScale]

theorem ratioScale_continuous : Continuous ratioScale := by
  unfold ratioScale
  fun_prop

theorem ratioScale_norm_le {t : ℝ} (ht : t ∈ Time) : ‖ratioScale t‖ ≤ 1 := by
  apply (ratioScale t).opNorm_le_bound zero_le_one
  intro z
  rw [ratioScale_apply, one_mul, Prod.norm_def, Prod.norm_def]
  refine max_le (le_max_left _ _) ((?_: ‖t * z.2‖ ≤ ‖z.2‖).trans (le_max_right _ _))
  rw [norm_mul, Real.norm_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

theorem ratioScale_mapsTo {U : Set Angles} {a b t : ℝ} (ha : a < 0) (hb : 0 < b)
    (ht : t ∈ Time) : MapsTo (ratioScale t) (Window U a b) (Window U a b) := by
  intro z hz
  rw [ratioScale_apply]
  refine ⟨hz.1, ?_⟩
  rcases le_total 0 z.2 with h | h
  · refine ⟨ha.trans_le (mul_nonneg ht.1 h), lt_of_le_of_lt ?_ hz.2.2⟩
    simpa using mul_le_mul_of_nonneg_right ht.2 h
  · refine ⟨lt_of_lt_of_le hz.2.1 ?_, (mul_nonpos_of_nonneg_of_nonpos ht.1 h).trans_lt hb⟩
    simpa using mul_le_mul_of_nonpos_right ht.2 h

def endpoint (M : Point → ℂ) (z : Angles) : ℂ := M (z, 0)

def numerator (M : Point → ℂ) (χ : ℝ → ℝ) (z : Point) : ℂ :=
  M z - χ z.2 • endpoint M z.1

def ratioDerivative (M : Point → ℂ) (z : Point) : ℂ :=
  fderiv ℝ M z (0, 1)

/-- The exact divided difference with the derivative value at ratio zero. -/
def remainder (M : Point → ℂ) (χ : ℝ → ℝ) (z : Point) : ℂ :=
  dslope (fun r => numerator M χ (z.1, r)) 0 z.2

theorem exact_split (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1) (z : Point) :
    M z = χ z.2 • endpoint M z.1 + z.2 • remainder M χ z := by
  have h := sub_smul_dslope (fun r => numerator M χ (z.1, r)) 0 z.2
  rw [sub_zero, ← remainder] at h
  rw [h]
  simp [numerator, endpoint, hχ]

theorem remainder_eq_quotient (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    {z : Point} (hz : z.2 ≠ 0) :
    remainder M χ z = numerator M χ z / (z.2 : ℂ) := by
  have h := exact_split M χ hχ z
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hz)).mpr
  rw [mul_comm]
  change z.2 • remainder M χ z = numerator M χ z
  rw [numerator, eq_sub_iff_add_eq, add_comm]
  exact h.symm

theorem remainder_zero (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ =ᶠ[𝓝 (0 : ℝ)] 1)
    (x : Angles) :
    remainder M χ (x, 0) = deriv (fun r => M (x, r)) 0 := by
  have h : (fun r => numerator M χ (x, r)) =ᶠ[𝓝 (0 : ℝ)]
      fun r => M (x, r) - endpoint M x := by
    filter_upwards [hχ] with r hr
    simp [numerator, hr]
  rw [remainder, dslope_same, h.deriv_eq, deriv_sub_const]

private theorem derivative_curve {F : Point → ℂ} {x : Angles} {r : ℝ}
    (hF : DifferentiableAt ℝ F (x, r)) :
    HasDerivAt (fun u => F (x, u)) (ratioDerivative F (x, r)) r := by
  have h : HasDerivAt (fun u : ℝ => (x, u)) ((0 : Angles), (1 : ℝ)) r :=
    (hasDerivAt_const r x).prodMk (hasDerivAt_id r)
  exact hF.hasFDerivAt.comp_hasDerivAt r h

theorem remainder_eq_integral {U : Set Angles} {a b : ℝ} (hU : IsOpen U)
    (ha : a < 0) (hb : 0 < b) (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    (hN : ContDiffOn ℝ 1 (numerator M χ) (Window U a b)) {z : Point} (hz : z ∈ Window U a b) :
    remainder M χ z = ∫ t in (0 : ℝ)..1, ratioDerivative (numerator M χ) (ratioScale t z) := by
  let N := numerator M χ
  let D := Window U a b
  have hD : IsOpen D := hU.prod isOpen_Ioo
  have hSlope (w : Point) (hw : w ∈ D) : DifferentiableAt ℝ N w :=
    ((hN.differentiableOn le_rfl) w hw).differentiableAt (hD.mem_nhds hw)
  by_cases hzero : z.2 = 0
  · have hz' : (z.1, (0 : ℝ)) ∈ D := ⟨hz.1, ha, hb⟩
    have hr : remainder M χ z = deriv (fun u => N (z.1, u)) 0 := by rw [remainder, hzero, dslope_same]
    rw [hr, (derivative_curve (hSlope _ hz')).deriv]
    simp [hzero, N]
  · have hC : ContinuousOn (ratioDerivative N) D :=
      ((hN.fderiv_of_isOpen hD (show (0 : WithTop ℕ∞) + 1 ≤ 1 by simp)).clm_apply
        contDiffOn_const).continuousOn
    have hSeg : ContinuousOn (fun t : ℝ => (z.1, t * z.2)) Time :=
      (continuous_const.prodMk (continuous_id.mul continuous_const)).continuousOn
    have hMaps : MapsTo (fun t : ℝ => (z.1, t * z.2)) Time D := by
      intro t ht
      simpa only [ratioScale_apply] using ratioScale_mapsTo ha hb ht hz
    have hContinuous : ContinuousOn (fun t => ratioDerivative N (z.1, t * z.2)) Time :=
      hC.comp hSeg hMaps
    have hDeriv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => N (z.1, u * z.2))
          (z.2 • ratioDerivative N (z.1, t * z.2)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (derivative_curve (hSlope _ (hMaps ht))).scomp t (hasDerivAt_mul_const z.2)
    have hInt : IntervalIntegrable (fun t : ℝ => z.2 • ratioDerivative N (z.1, t * z.2))
        volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_const.smul hContinuous
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt
    rw [intervalIntegral.integral_smul] at eq
    have eq' : z.2 • (∫ t in (0 : ℝ)..1, ratioDerivative N (ratioScale t z)) = N z := by
      simpa [N, numerator, endpoint, hχ, ratioScale_apply] using eq
    apply (smul_right_injective ℂ hzero)
    change z.2 • remainder M χ z = z.2 • ∫ t in (0 : ℝ)..1, ratioDerivative N (ratioScale t z)
    rw [eq']
    rw [remainder_eq_quotient M χ hχ hzero]
    change (z.2 : ℂ) * (numerator M χ z / (z.2 : ℂ)) = numerator M χ z
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hzero)

theorem remainder_eq_integral_on_plateau {U : Set Angles} {a b : ℝ} (hU : IsOpen U)
    (ha : a < 0) (hb : 0 < b) (M : Point → ℂ) (χ : ℝ → ℝ)
    (hχ : χ =ᶠ[𝓝 (0 : ℝ)] 1) (hM : ContDiffOn ℝ 1 M (Window U a b))
    {z : Point} (hz : z ∈ Window U a b) (hone : χ z.2 = 1) :
    remainder M χ z = ∫ t in (0 : ℝ)..1, ratioDerivative M (ratioScale t z) := by
  let D := Window U a b
  let N := numerator M (fun _ => 1)
  have hD : IsOpen D := hU.prod isOpen_Ioo
  have hN : ContDiffOn ℝ 1 N D := by
    have h := (hM.comp_continuousLinearMap (ratioScale 0)).mono
      (ratioScale_mapsTo ha hb ⟨le_rfl, zero_le_one⟩)
    change ContDiffOn ℝ 1 (fun p : Point => M p - (1 : ℝ) • M (p.1, 0)) D
    simp only [one_smul]
    simpa only [Function.comp_def, ratioScale_apply, zero_mul] using hM.sub h
  have hSame : remainder M χ z = remainder M (fun _ => 1) z := by
    have hχ0 : χ 0 = 1 := hχ.eq_of_nhds
    by_cases hzero : z.2 = 0
    · have hz' : (z.1, (0 : ℝ)) = z := Prod.ext rfl hzero.symm
      rw [← hz', remainder_zero M χ hχ, remainder_zero M (fun _ => 1) EventuallyEq.rfl]
    · rw [remainder_eq_quotient M χ hχ0 hzero, remainder_eq_quotient M (fun _ => 1) rfl hzero]
      simp [numerator, hone]
  rw [hSame, remainder_eq_integral hU ha hb M (fun _ => 1) rfl hN hz]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hw : ratioScale t z ∈ D := ratioScale_mapsTo ha hb ht hz
  let w := ratioScale t z
  have hND : DifferentiableAt ℝ N (w.1, w.2) :=
    ((hN.differentiableOn le_rfl) w hw).differentiableAt (hD.mem_nhds hw)
  have hMD : DifferentiableAt ℝ M (w.1, w.2) :=
    ((hM.differentiableOn le_rfl) w hw).differentiableAt (hD.mem_nhds hw)
  change ratioDerivative N (w.1, w.2) = ratioDerivative M (w.1, w.2)
  rw [← (derivative_curve hND).deriv, ← (derivative_curve hMD).deriv]
  simp only [N, numerator, one_smul, deriv_sub_const]

theorem remainder_tsupport_subset_numerator (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1) :
    tsupport (remainder M χ) ⊆ tsupport (numerator M χ) := by
  apply closure_minimal ?_ isClosed_closure
  intro z hz
  by_contra hn
  apply hz
  by_cases hρ : z.2 = 0
  · have h : (fun t : ℝ => numerator M χ (z.1, t)) =ᶠ[𝓝 (0 : ℝ)] 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        (show Tendsto (fun t : ℝ => (z.1, t)) (𝓝 0) (𝓝 z) from by
          simpa [← hρ] using (continuous_const.prodMk continuous_id :
            Continuous (fun t : ℝ => (z.1, t))).continuousAt.tendsto)
    rw [remainder, hρ, dslope_same, h.deriv_eq, deriv_zero]
    rfl
  · rw [remainder_eq_quotient M χ hχ hρ, image_eq_zero_of_notMem_tsupport hn, zero_div]

theorem remainder_tsupport_subset (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1) :
    tsupport (remainder M χ) ⊆ tsupport M ∪
      (Prod.snd ⁻¹' tsupport χ ∩ Prod.fst ⁻¹' tsupport (endpoint M)) := by
  refine (remainder_tsupport_subset_numerator M χ hχ).trans (closure_minimal ?_ ?_)
  · intro z hz
    by_contra h
    rcases not_or.mp h with ⟨hM, hχM⟩
    rw [mem_inter_iff, mem_preimage, mem_preimage] at hχM
    have h0 := image_eq_zero_of_notMem_tsupport hM
    apply hz
    rcases not_and_or.mp hχM with hρ | hAng
    · simp [numerator, h0, image_eq_zero_of_notMem_tsupport hρ]
    · simp [numerator, h0, image_eq_zero_of_notMem_tsupport hAng]
  · exact isClosed_closure.union ((isClosed_closure.preimage continuous_snd).inter
      (isClosed_closure.preimage continuous_fst))

end Burnett.Analysis.LowRatio
