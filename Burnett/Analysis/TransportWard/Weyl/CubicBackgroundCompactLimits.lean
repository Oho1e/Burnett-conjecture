import Burnett.Analysis.TransportWard.Weyl.CubicBackgroundDerivativeError
import Burnett.Analysis.TransportWard.Weyl.CubicBackgroundValueError
import Burnett.Analysis.TransportWard.Weyl.LocalizedPrincipalCoefficient

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate ContDiff Topology

private theorem exists_compactRealCoefficientSchwartz
    {U K : Set E} (hU : IsOpen U) (r ρ : E → ℝ)
    (hr : ContDiffOn ℝ ∞ r U) (hρ : ContDiff ℝ ∞ ρ)
    (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ) (hOne : ∀ x ∈ K, ρ x = 1) :
    ∃ q : SchwartzMap E ℂ, HasCompactSupport (q : E → ℂ) ∧ ∀ x ∈ K, q x = (r x : ℂ) := by
  have hReal : ContDiff ℝ ∞ (fun x => ρ x * r x) :=
    Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hρ hρU hr
  have hSupport : HasCompactSupport (ρ * r) := hρc.mul_right
  have hSupp : HasCompactSupport (fun x => Complex.ofReal (ρ x * r x)) :=
    hSupport.comp_left Complex.ofReal_zero
  let q := hSupp.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hReal)
  refine ⟨q, hSupp, fun x hx => ?_⟩
  change Complex.ofReal (ρ x * r x) = Complex.ofReal (r x)
  rw [hOne x hx, one_mul]

private theorem setIntegral_cubicBackgroundProduct_eq_re
    {K : Set E} (hK : MeasurableSet K) (r : E → ℝ) (q a b z : SchwartzMap E ℂ)
    (hq : ∀ x ∈ K, q x = (r x : ℂ))
    (ha : ∀ x, Complex.ofReal (a x).re = a x) (hb : ∀ x, Complex.ofReal (b x).re = b x)
    (hz : tsupport (z : E → ℂ) ⊆ K) :
    (∫ x in K, r x * (a x).re * (b x).re * (z x).re) =
      (∫ x, conj (z x) * (q x * a x * b x)).re := by
  let P := scalarSchwartzProduct (scalarSchwartzProduct q a) b
  have hz₂ := z.memLp 2 volume
  have hConj : MemLp (fun x => conj (z x)) 2 volume := hz₂.mono
    (Complex.continuous_conj.comp_aestronglyMeasurable hz₂.1)
    (.of_forall fun x => by simp)
  have hInt : Integrable (fun x => conj (z x) * (q x * a x * b x)) := by
    simpa only [P, scalarSchwartzProduct_apply] using hConj.integrable_mul (P.memLp 2 volume)
  calc
    _ = ∫ x in K, (conj (z x) * (q x * a x * b x)).re := by
      apply setIntegral_congr_fun hK
      intro x hx
      change r x * (a x).re * (b x).re * (z x).re = (conj (z x) * (q x * a x * b x)).re
      have hP : q x * a x * b x = Complex.ofReal (r x * (a x).re * (b x).re) := by
        calc
          _ = (r x : ℂ) * Complex.ofReal (a x).re * Complex.ofReal (b x).re := by
            rw [hq x hx, ha x, hb x]
          _ = _ := by simp only [Complex.ofReal_mul]
      rw [hP]
      simp only [Complex.mul_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    _ = ∫ x, (conj (z x) * (q x * a x * b x)).re := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hz hs))]
      simp
    _ = _ := integral_re hInt

/-- A compactly localized real coefficient, one small value and two L²
factors suffice for all undifferentiated-test background terms. -/
theorem tendsto_compact_cubicBackground_valuePair_zero
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (r ρ : E → ℝ)
    (hr : ContDiffOn ℝ ∞ r U) (hρ : ContDiff ℝ ∞ ρ)
    (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ) (hOne : ∀ x ∈ K, ρ x = 1)
    (a b z : ℕ → SchwartzMap E ℂ)
    (haR : ∀ n x, Complex.ofReal (a n x).re = a n x)
    (hbR : ∀ n x, Complex.ofReal (b n x).re = b n x)
    (hz : ∀ n, tsupport (z n : E → ℂ) ⊆ K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (ha : ∀ n x, ‖a n x‖ ≤ ε n)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ n, ‖(b n).toLp 2 volume‖ ≤ M)
    (hL : ∀ n, ‖(z n).toLp 2 volume‖ ≤ M) :
    Tendsto (fun n => ∫ x in K, r x * (a n x).re * (b n x).re * (z n x).re) atTop (𝓝 0) := by
  obtain ⟨q,hqs,hq⟩ := exists_compactRealCoefficientSchwartz hU r ρ hr hρ hρU hρc hOne
  let R := SchwartzMap.seminorm ℝ 0 0 q
  have hB := Burnett.V03.tendsto_cubicBackground_small_value_pair_zero q a b z R M
    (apply_nonneg _ _) hM (SchwartzMap.norm_le_seminorm ℝ q) hqs
    q.smooth' ε hε hLim ha hb hL
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp hB
  refine (show Tendsto (fun n => (∫ x, conj (z n x) * (q x * a n x * b n x)).re) atTop (𝓝 0)
    from hRe).congr' ?_
  exact .of_forall fun n =>
    (setIntegral_cubicBackgroundProduct_eq_re hK.measurableSet r q (a n) (b n) (z n)
      hq (haR n) (hbR n) (hz n)).symm

/-- Integration by parts keeps the original test derivative and uses only an
L² bound for the undifferentiated test. -/
theorem tendsto_compact_cubicBackground_derivativePair_zero
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (e : E) (r ρ : E → ℝ)
    (hr : ContDiffOn ℝ ∞ r U) (hρ : ContDiff ℝ ∞ ρ)
    (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ) (hOne : ∀ x ∈ K, ρ x = 1)
    (a b z : ℕ → SchwartzMap E ℂ)
    (haR : ∀ n x, Complex.ofReal (a n x).re = a n x)
    (hbR : ∀ n x, Complex.ofReal (b n x).re = b n x)
    (hz : ∀ n, tsupport (z n : E → ℂ) ⊆ K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (ha : ∀ n x, ‖a n x‖ ≤ ε n) (hb : ∀ n x, ‖b n x‖ ≤ ε n)
    (M : ℝ) (hM : 0 ≤ M) :
    let D := SchwartzMap.pderivCLM ℂ e
    (∀ n, ‖(a n).toLp 2 volume‖ ≤ M) →
    (∀ n, ‖(D (a n)).toLp 2 volume‖ ≤ M) →
    (∀ n, ‖(D (b n)).toLp 2 volume‖ ≤ M) →
    (∀ n, ‖(z n).toLp 2 volume‖ ≤ M) →
    Tendsto (fun n => ∫ x in K, r x * (a n x).re * (b n x).re * (D (z n) x).re) atTop (𝓝 0) := by
  intro D hLa hDa hDb hL
  obtain ⟨q,_,hq⟩ := exists_compactRealCoefficientSchwartz hU r ρ hr hρ hρU hρc hOne
  have hB := Burnett.V03.tendsto_cubicBackground_test_derivative_pair_zero e q a b z ε ε
    hε hε hLim hLim ha hb M hM hLa hDa hDb hL
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp hB
  have hSD (n : ℕ) : tsupport (D (z n) : E → ℂ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hOut
    have hzOut : x ∉ tsupport (z n : E → ℂ) := fun hx => hOut (hz n hx)
    apply hx
    change fderiv ℝ (z n : E → ℂ) x e = 0
    rw [fderiv_of_notMem_tsupport ℝ hzOut, ContinuousLinearMap.zero_apply]
  refine (show Tendsto (fun n => (∫ x, conj (D (z n) x) * (q x * a n x * b n x)).re) atTop (𝓝 0)
    from hRe).congr' ?_
  exact .of_forall fun n =>
    (setIntegral_cubicBackgroundProduct_eq_re hK.measurableSet r q (a n) (b n) (D (z n))
      hq (haR n) (hbR n) (hSD n)).symm

end Burnett.V03.Palatini
