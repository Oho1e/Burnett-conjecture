import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierConjugation
import Burnett.Analysis.Microlocal.Overlap.DyadicShellInversionLimit

/-! Strong convergence of the actual normalized Fourier conjugation error
for weakly null inputs, in any compatible pair of smooth charts. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Set Burnett.Fourier Burnett.Geometry Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.OverlapKernel
open scoped BigOperators ContDiff Manifold

/-- The genuine near and far kernels of the fixed maximal-atlas
transition admit bounds uniform over all dyadic shells. -/
theorem overlap_shellKernel_near_far_bounds
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    ∃ q a δ₀ Cnear Cfar : ℝ, 0 < q ∧ 0 < a ∧ 0 < δ₀ ∧ 0 ≤ Cnear ∧ 0 ≤ Cfar ∧
      ∀ (j : ℕ) (x : E), x ∈ K → ∀ y ∈ K,
        let s := dyadicScale j
        let R := halfDensityKernelDifference Φ w (shellKernel m hm j) x y
        (‖x - y‖ ≤ δ₀ →
          ‖R‖ ≤ Cnear * s^3 / (1+s*q*‖x - y‖)^5) ∧
        (δ₀ ≤ ‖x - y‖ →
          ‖R‖ ≤ Cfar * s^4 / (1+s*a)^7) := by
  intro Φ w
  obtain ⟨q, L, W, H, δ₀, hq, hL, hW, hH, hδ, hNear, hΦ, hLip, hInv, hw, hwLip⟩ :=
    overlapKernel_geometry_bounds c d K hK hKU hConv
  obtain ⟨a, ha, hFar⟩ := overlapFar_uniform_arguments c d K hK hKU hδ
  obtain ⟨C₀, C₁, hC₀, hC₁, hDecay⟩ := Burnett.Microlocal.OverlapKernel.shellKernel_decay_bounds m hm
  refine ⟨q/2, a, δ₀, W * H * C₀ / (q/2) + W^2 * C₁ * L / (q/2)^2,
    2*W^2*C₀, half_pos hq, ha, hδ, by positivity, by positivity, ?_⟩
  intro j x hx y hy
  let s := dyadicScale j
  have hs : 0 < s := by unfold s dyadicScale; positivity
  have hk : Differentiable ℝ (shellKernel m hm j) := fun z =>
    (shellKernel_hasFDerivAt m hm j z).differentiableAt
  refine ⟨fun hnxy => ?_, fun hfxy => ?_⟩
  · exact halfDensityKernelDifference_near_bound hConv Φ w _ hΦ hk hq hL hW hH hs hC₀ hC₁
      hLip hInv hw hwLip (fun z => (hDecay j z).1) (fun z => (hDecay j z).2)
      hx hy (hNear _ (norm_nonneg _) hnxy)
  · obtain ⟨hu, hv⟩ := hFar x hx y hy hfxy
    calc
      _ ≤ 2*W^2*(C₀*s^4/(1+s*a)^7) :=
        halfDensityKernelDifference_far_bound Φ w _ hW hs ha.le
          (fun z => (hDecay j z).1) (hw x hx) (hw y hy) hu hv
      _ = _ := by ring

private theorem far_decay_to_integrable_envelope
    {s a b r : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : b*r ≤ a) :
    s^4 / (1+s*a)^7 ≤ (s^3 / a) / (1+s*b*r)^5 := by
  let A := 1+s*a
  let D := 1+s*b*r
  have hA : 0 < A := by dsimp only [A]; positivity
  have hA1 : 1 ≤ A := le_add_of_nonneg_right (mul_nonneg hs.le ha.le)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDA : D ≤ A := by
    simpa only [A, D, mul_assoc] using add_le_add_left (mul_le_mul_of_nonneg_left h hs.le) 1
  have hProd : (s*a) * D^5 ≤ A^7 := by
    calc
      _ ≤ A * A^5 := mul_le_mul (le_add_of_nonneg_left zero_le_one)
        (pow_le_pow_left₀ hD.le hDA 5) (pow_nonneg hD.le _) hA.le
      _ = A^6 := by ring
      _ ≤ A^7 := pow_le_pow_right₀ hA1 (by norm_num)
  have hRatio : (s*a)/A^7 ≤ 1/D^5 :=
    (div_le_div_iff₀ (pow_pos hA _) (pow_pos hD _)).2 (by simpa only [one_mul] using hProd)
  change s^4/A^7 ≤ (s^3/a)/D^5
  calc
    _ = (s^3/a)*((s*a)/A^7) := by field_simp [ha.ne', hA.ne']
    _ ≤ (s^3/a)*(1/D^5) := mul_le_mul_of_nonneg_left hRatio (by positivity)
    _ = _ := by ring

/-- One integrable radial profile dominates the pair of shell kernels on
the whole compact overlap. The scale in the amplitude is (s^3). -/
theorem overlap_shellKernel_uniform_envelope
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (j : ℕ) (x : E), x ∈ K → ∀ y ∈ K,
      let s := dyadicScale j
      ‖halfDensityKernelDifference Φ w (shellKernel m hm j) x y‖ ≤
        C*s^3/(1+s*b*‖x-y‖)^5 := by
  intro Φ w
  obtain ⟨q, a, δ₀, Cnear, Cfar, hq, ha, _, hCnear, hCfar, hBounds⟩ :=
    overlap_shellKernel_near_far_bounds c d K hK hKU hConv m hm
  let R := Metric.diam K + 1
  let b := min q (a/R)
  let C := Cnear + Cfar/a
  have hR : 0 < R := by dsimp only [R]; linarith [Metric.diam_nonneg (s := K)]
  have hb : 0 < b := lt_min hq (div_pos ha hR)
  have hC : 0 ≤ C := add_nonneg hCnear (div_nonneg hCfar ha.le)
  refine ⟨b, C, hb, hC, fun j x hx y hy => ?_⟩
  let s := dyadicScale j
  let r := ‖x-y‖
  let D := 1+s*b*r
  have hs : 0 < s := by unfold s dyadicScale; positivity
  have hr : 0 ≤ r := norm_nonneg _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hrR : r ≤ R := (by
    simpa only [r, dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded hx hy
      : r ≤ Metric.diam K).trans (le_add_of_nonneg_right zero_le_one)
  have hba : b*r ≤ a := calc
    _ ≤ b*R := mul_le_mul_of_nonneg_left hrR hb.le
    _ ≤ (a/R)*R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    _ = a := div_mul_cancel₀ a hR.ne'
  have hCnearC : Cnear ≤ C := le_add_of_nonneg_right (div_nonneg hCfar ha.le)
  have hCfarC : Cfar/a ≤ C := le_add_of_nonneg_left hCnear
  obtain ⟨hNear, hFar⟩ := hBounds j x hx y hy
  change ‖halfDensityKernelDifference Φ w (shellKernel m hm j) x y‖ ≤ C*s^3/D^5
  by_cases hsmall : r ≤ δ₀
  · have hDenom : D^5 ≤ (1+s*q*r)^5 := by
      apply pow_le_pow_left₀ hD.le
      exact add_le_add_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le) hr) _
    calc
      _ ≤ Cnear*s^3/(1+s*q*r)^5 := hNear hsmall
      _ ≤ Cnear*s^3/D^5 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hD _) hDenom
      _ ≤ C*s^3/D^5 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCnearC (by positivity)) (pow_nonneg hD.le _)
  · calc
      _ ≤ Cfar*s^4/(1+s*a)^7 := hFar (le_of_lt (lt_of_not_ge hsmall))
      _ = Cfar * (s^4/(1+s*a)^7) := by ring
      _ ≤ Cfar * ((s^3/a)/D^5) :=
        mul_le_mul_of_nonneg_left (far_decay_to_integrable_envelope hs ha hb.le hr hba) hCfar
      _ = (Cfar/a)*s^3/D^5 := by ring
      _ ≤ C*s^3/D^5 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCfarC (by positivity)) (pow_nonneg hD.le _)

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Set MeasureTheory Filter Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.AngularDyadicKernel (E dyadicScale shellKernel shellKernel_hasFDerivAt)
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff Manifold InnerProduct Topology ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The localized difference of the pullback kernel and its affine approximation
on one dyadic shell. -/
def localizedOverlapShellDifference (c d : AtlasChart M) (K : Set E) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (x y : E) : ℂ :=
  (K ×ˢ K).indicator
    (fun p => halfDensityKernelDifference (overlapTransition c d) (overlapJacobianWeight c d)
      (shellKernel m hm j) p.1 p.2) (x, y)

private theorem measurable_halfDensityKernelDifference
    (Φ : E → E) (w : E → ℝ) (k : E → ℂ)
    (hΦ : Measurable Φ) (hw : Measurable w) (hk : Measurable k) :
    Measurable (uncurry (halfDensityKernelDifference Φ w k)) := by
  have hEval : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hFrozen : Measurable (fun p : E × E => fderiv ℝ Φ p.1 (p.1 - p.2)) :=
    hEval.measurable.comp (((measurable_fderiv ℝ Φ).comp measurable_fst).prodMk
      (measurable_fst.sub measurable_snd))
  have hx : Measurable (fun p : E × E => w p.1) := hw.comp measurable_fst
  have hy : Measurable (fun p : E × E => w p.2) := hw.comp measurable_snd
  have hChange : Measurable (fun p : E × E => Φ p.1 - Φ p.2) :=
    (hΦ.comp measurable_fst).sub (hΦ.comp measurable_snd)
  exact ((hx.mul hy).smul (hk.comp hChange)).sub ((hx.pow_const 2).smul (hk.comp hFrozen))

theorem measurable_localizedOverlapShellDifference
    (c d : AtlasChart M) (K : Set E) (hK : MeasurableSet K) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    Measurable (uncurry (localizedOverlapShellDifference c d K m hm j)) := by
  have hk : Continuous (shellKernel m hm j) :=
    continuous_iff_continuousAt.mpr fun x => (shellKernel_hasFDerivAt m hm j x).continuousAt
  exact (measurable_halfDensityKernelDifference _ _ _ (overlapTransition_measurable c d)
    (overlapJacobianWeight_measurable c d) hk.measurable).indicator (hK.prod hK)


/-- On a compact convex overlap window, the series of actual half-density
shell-kernel differences gives a strongly null output for every bounded
weakly null sequence with integrable input representatives. -/
theorem exists_actualOverlapShell_actions_tendsto_zero
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : ℕ → E → ℂ) (hfm : ∀ n, Measurable (f n)) (hf₁ : ∀ n, Integrable (f n))
    (hf : ∀ n, MemLp (f n) 2 volume)
    (C : ℝ) (hu : ∀ n, ‖(hf n).toLp (f n)‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((hf n).toLp (f n))) atTop (𝓝 0)) :
    ∃ U : ℕ → ℕ → ComplexL2 E,
      (∀ j n, U j n =ᵐ[volume] fun x =>
        ∫ y, localizedOverlapShellDifference c d K m hm j x y * f n y) ∧
      (∀ n, Summable (fun j => ‖U j n‖)) ∧
      Tendsto (fun n => ∑' j, U j n) atTop (𝓝 0) := by
  let R := localizedOverlapShellDifference c d K m hm
  have hKm := hK.isClosed.measurableSet
  obtain ⟨q, A, hq, hA, hEnv⟩ := overlap_shellKernel_uniform_envelope c d K hK hKU hConv m hm
  have hSupp j (x y : E) (h : x ∉ K ∨ y ∉ K) : R j x y = 0 := by
    have hxy : (x,y) ∉ K ×ˢ K := fun hp => h.elim (fun hx => hx hp.1) (fun hy => hy hp.2)
    simp only [R, localizedOverlapShellDifference, indicator_of_notMem hxy]
  have hNorm j (x y : E) : ‖R j x y‖ ≤
      A * dyadicScale j ^ 3 / (1 + dyadicScale j * q * ‖x - y‖) ^ 5 := by
    by_cases hxy : (x,y) ∈ K ×ˢ K
    · simpa only [R, localizedOverlapShellDifference, indicator_of_mem hxy] using hEnv j x hxy.1 y hxy.2
    · simp only [R, localizedOverlapShellDifference, indicator_of_notMem hxy, norm_zero]
      have hs : 0 ≤ dyadicScale j := by unfold dyadicScale; positivity
      exact div_nonneg (mul_nonneg hA (pow_nonneg hs _))
        (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hs hq.le) (norm_nonneg _))) _)
  exact Burnett.Microlocal.Overlap.exists_overlapShell_actions_tendsto_zero R
    (measurable_localizedOverlapShellDifference c d K hKm m hm) K hKm
    hK.measure_lt_top.ne hSupp A q hA hq hNorm f hfm hf₁ hf C hu hw

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open MeasureTheory Set Filter Burnett.Fourier Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E partialAngularSymbol)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped BigOperators ContDiff FourierTransform Manifold InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The difference of the two explicit finite Fourier actions, restricted to
the compact overlap window. -/
def localizedPartialAngularDifference (c d : AtlasChart M) (K : Set E)
    (hKU : K ⊆ (c.transition d).source) (m : BoundedSymbol E) (N : ℕ)
    (f : E → ℂ) (x : E) : ℂ := by
  classical
  exact if hx : x ∈ K then
    overlapJacobianWeight c d x •
        (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 (transportedHalfDensity c d K f)) ξ))
          (overlapTransition c d x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x
    else 0

/-- For each input, the finite Fourier differences have a strong L² limit
as the number of shells grows. These limits vanish on a bounded weakly null
sequence of inputs. -/
theorem exists_localizedPartialAngularDifference_limit
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : ℕ → SchwartzMap E ℂ)
    (C : ℝ) (hC : ∀ n, ‖(f n).toLp 2 volume‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ F : ℕ → ℕ → ComplexL2 E, ∃ R : ℕ → ComplexL2 E,
      (∀ n N, F n N =ᵐ[volume] localizedPartialAngularDifference c d K hKU m N (f n)) ∧
      (∀ n, Tendsto (F n) atTop (𝓝 (R n))) ∧ Tendsto R atTop (𝓝 0) := by
  let J (j n : ℕ) (x : E) :=
    ∫ y, localizedOverlapShellDifference c d K m hm j x y * f n y
  obtain ⟨U, hU, hSummable, hLimit⟩ := exists_actualOverlapShell_actions_tendsto_zero
    c d K hK hKU hConv m hm (fun n => (f n : E → ℂ))
    (fun n => (f n).continuous.measurable) (fun n => (f n).integrable)
    (fun n => (f n).memLp 2 volume) C hC hw
  let F (n N : ℕ) := ∑ j ∈ Finset.range N, U j n
  let R (n : ℕ) := ∑' j, U j n
  have hAE (n N : ℕ) : (F n N : E → ℂ) =ᵐ[volume] fun x => ∑ j ∈ Finset.range N, J j n x := by
    induction N with
    | zero => simpa only [F, Finset.sum_range_zero] using
        (Lp.coeFn_zero ℂ 2 (volume : Measure E))
    | succ N ih =>
        simp only [F, Finset.sum_range_succ]
        filter_upwards [Lp.coeFn_add (F n N) (U N n), ih, hU N n] with x hx hxSum hxTerm
        simpa only [Pi.add_apply, hxSum, hxTerm, J] using hx
  refine ⟨F, R, ?_, fun n => (hSummable n).of_norm.hasSum.tendsto_sum_nat, hLimit⟩
  intro n N
  filter_upwards [hAE n N] with x hX
  rw [hX]
  by_cases hx : x ∈ K
  · simp only [localizedPartialAngularDifference, dif_pos hx]
    exact (overlap_partialAngularFourier_difference_sum_actions c d K hK hKU hx m hm hd N
      (f n) (f n).continuous).symm
  · have jZero (j : ℕ) : J j n x = 0 := by
      have hxy (y : E) : (x,y) ∉ K ×ˢ K := fun h => hx h.1
      simp only [J, localizedOverlapShellDifference, indicator_of_notMem (hxy _), zero_mul, integral_zero]
    simp only [localizedPartialAngularDifference, dif_neg hx, jZero, Finset.sum_const_zero]

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open MeasureTheory Set Filter Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldBilinear
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.Overlap (tendsto_inverseFourier_partialAngular_comp ae_eq_of_tendsto_L2_and_pointwise)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff FourierTransform Manifold InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The difference of the actual transported and frozen Fourier actions with
one fixed infrared normalization. -/
def localizedNormalizedAngularDifference (c d : AtlasChart M) (K : Set E)
    (hKU : K ⊆ (c.transition d).source) (m : BoundedSymbol E)
    (f : E → ℂ) (x : E) : ℂ := by
  classical
  exact if hx : x ∈ K then
    overlapJacobianWeight c d x •
        (𝓕⁻ (fun ξ => normalizedAngularSymbol m ξ * (𝓕 (transportedHalfDensity c d K f)) ξ))
          (overlapTransition c d x) -
      (𝓕⁻ (fun ξ => normalizedAngularSymbol m (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x
    else 0

theorem tendsto_localizedPartialAngularDifference
    (c d : AtlasChart M) (K : Set E) (hKU : K ⊆ (c.transition d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : E → ℂ) (hf : Integrable (𝓕 (K.indicator f)))
    (hTransport : Integrable (𝓕 (transportedHalfDensity c d K f))) (x : E) :
    Tendsto (fun N => localizedPartialAngularDifference c d K hKU m N f x) atTop
      (𝓝 (localizedNormalizedAngularDifference c d K hKU m f x)) := by
  by_cases hx : x ∈ K
  · simp only [localizedPartialAngularDifference, localizedNormalizedAngularDifference, dif_pos hx]
    have hTarget := tendsto_inverseFourier_partialAngular_comp m hm id measurable_id
      (𝓕 (transportedHalfDensity c d K f)) hTransport (overlapTransition c d x)
    have hFrozen := tendsto_inverseFourier_partialAngular_comp m hm
      (frozenChartFrequency c d (hKU hx))
      (frozenChartFrequency c d (hKU hx)).continuous.measurable (𝓕 (K.indicator f)) hf x
    exact (hTarget.const_smul (overlapJacobianWeight c d x)).sub hFrozen
  · simp only [localizedPartialAngularDifference, localizedNormalizedAngularDifference, dif_neg hx]
    exact tendsto_const_nhds

/-- Removing the outer cutoff gives the actual Fourier difference in L².
The identified differences vanish strongly on bounded weakly null inputs. -/
theorem exists_localizedNormalizedAngularDifference_strongZero
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : ℕ → SchwartzMap E ℂ)
    (hf : ∀ n, Integrable (𝓕 (K.indicator (f n : E → ℂ))))
    (hTransport : ∀ n, Integrable (𝓕 (transportedHalfDensity c d K (f n))))
    (C : ℝ) (hC : ∀ n, ‖(f n).toLp 2 volume‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ R : ℕ → ComplexL2 E,
      (∀ n, R n =ᵐ[volume] localizedNormalizedAngularDifference c d K hKU m (f n)) ∧
      Tendsto R atTop (𝓝 0) := by
  obtain ⟨F, R, hEq, hOuter, hZero⟩ := exists_localizedPartialAngularDifference_limit
    c d K hK hKU hConv m hm hd f C hC hw
  refine ⟨R, fun n => ?_, hZero⟩
  exact ae_eq_of_tendsto_L2_and_pointwise (F n) (R n)
    (fun N => localizedPartialAngularDifference c d K hKU m N (f n)) _ (hEq n) (hOuter n)
    (tendsto_localizedPartialAngularDifference c d K hKU m hm (f n) (hf n) (hTransport n))

end Burnett.Microlocal.AtlasOverlapKernel
