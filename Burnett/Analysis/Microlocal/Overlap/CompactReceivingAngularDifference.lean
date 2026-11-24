import Burnett.Analysis.Microlocal.Overlap.CompactWindowKernel
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierLimit
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartHalfDensity

/-! The actual difference of the transported multiplier and its frozen
principal action is an operator-norm sum of compact shell operators. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E dyadicScale shellKernel shellKernel_hasFDerivAt)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.OverlapKernel
open scoped ContDiff ENNReal InnerProduct Topology FourierTransform

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem continuousOn_localizedOverlapShellDifference
    (c d : AtlasChart M) (K : Set E) (hKU : K ⊆ (c.transition d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    ContinuousOn (uncurry (localizedOverlapShellDifference c d K m hm j)) (K ×ˢ K) := by
  let Φ := overlapTransition c d
  let w := overlapJacobianWeight c d
  let k := shellKernel m hm j
  have hΦ : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hw : ContinuousOn w K := (overlapJacobianWeight_continuousOn c d).mono hKU
  have hD₀ : ContDiffOn ℝ 0 (fderiv ℝ Φ) (c.transition d).source :=
    (overlapTransition_contDiffOn c d).fderiv_of_isOpen (c.transition d).open_source (by simp)
  have hD : ContinuousOn (fderiv ℝ Φ) K := hD₀.continuousOn.mono hKU
  have hk : Continuous k :=
    continuous_iff_continuousAt.mpr fun x => (shellKernel_hasFDerivAt m hm j x).continuousAt
  have h₁ : MapsTo (Prod.fst : E × E → E) (K ×ˢ K) K := fun _ hp => hp.1
  have h₂ : MapsTo (Prod.snd : E × E → E) (K ×ˢ K) K := fun _ hp => hp.2
  have hL := (hΦ.comp continuous_fst.continuousOn h₁).sub
    (hΦ.comp continuous_snd.continuousOn h₂)
  have hR := (hD.comp continuous_fst.continuousOn h₁).clm_apply
    (continuous_fst.sub continuous_snd).continuousOn
  have hx := hw.comp continuous_fst.continuousOn h₁
  have hy := hw.comp continuous_snd.continuousOn h₂
  apply (((hx.mul hy).smul (hk.comp_continuousOn hL)).sub
    ((hx.pow 2).smul (hk.comp_continuousOn hR))).congr
  intro p hp
  simp only [uncurry, localizedOverlapShellDifference, indicator_of_mem hp,
    Φ, w, k, halfDensityKernelDifference, Function.comp_apply]

/-- The error for an actual smooth angular multiplier is one fixed compact
operator. Its action is identified on every Schwartz input supported in the
window, with the same chart transition and Jacobian used at every shell. -/
theorem exists_compact_localizedNormalizedAngularDifference
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) :
    ∃ R : ComplexL2 E →L[ℂ] ComplexL2 E, IsCompactOperator R ∧
      ∀ f : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ K →
        R (f.toLp 2 volume) =ᵐ[volume] localizedNormalizedAngularDifference c d K hKU m f := by
  let L := localizedOverlapShellDifference c d K m hm
  obtain ⟨q, A, hq, hA, hEnv⟩ := overlap_shellKernel_uniform_envelope c d K hK hKU hConv m hm
  have hs (j : ℕ) : 0 < dyadicScale j := by unfold dyadicScale; positivity
  have hSupp (j : ℕ) (x y : E) (h : x ∉ K ∨ y ∉ K) : L j x y = 0 := by
    have hxy : (x,y) ∉ K ×ˢ K := fun hp => h.elim (fun hx => hx hp.1) (fun hy => hy hp.2)
    simp only [L, localizedOverlapShellDifference, indicator_of_notMem hxy]
  have hNorm (j : ℕ) (x y : E) : ‖L j x y‖ ≤
      A * dyadicScale j ^ 3 / (1 + dyadicScale j * q * ‖x - y‖) ^ 5 := by
    by_cases hxy : (x,y) ∈ K ×ˢ K
    · simpa only [L, localizedOverlapShellDifference, indicator_of_mem hxy] using hEnv j x hxy.1 y hxy.2
    · simp only [L, localizedOverlapShellDifference, indicator_of_notMem hxy, norm_zero]
      have hs₀ := (hs j).le
      positivity
  choose T hT hTN hPair using fun j =>
    exists_compact_windowKernel_schur (L j) K hK
      (measurable_localizedOverlapShellDifference c d K hK.isClosed.measurableSet m hm j)
      (continuousOn_localizedOverlapShellDifference c d K hKU m hm j) (hSupp j)
      A q (dyadicScale j) hA hq (hs j) (hNorm j)
  have hSum : Summable T := (summable_overlapShell_bound A q).of_norm_bounded hTN
  let R := ∑' j, T j
  have hTSum (N : ℕ) : IsCompactOperator ⇑(∑ j ∈ Finset.range N, T j) := by
    apply Finset.sum_induction T (fun P => IsCompactOperator P)
    · intro P Q hP hQ
      exact hP.add hQ
    · exact isCompactOperator_zero
    · exact fun j _ => hT j
  have hR : IsCompactOperator R :=
    isCompactOperator_of_tendsto hSum.hasSum.tendsto_sum_nat (Eventually.of_forall hTSum)
  refine ⟨R, hR, fun f hf => ?_⟩
  have hTaken : K.indicator (f : E → ℂ) = f := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))).symm
  have hF : Integrable (𝓕 (K.indicator (f : E → ℂ))) := by
    rw [hTaken]
    exact (SchwartzMap.fourierTransformCLM ℂ f).integrable
  have hTransport : Integrable (𝓕 (transportedHalfDensity c d K f)) :=
    (SchwartzMap.fourierTransformCLM ℂ (transportedHalfDensitySchwartz c d K hK hKU f hf)).integrable
  let V (N : ℕ) := ∑ j ∈ Finset.range N, T j (f.toLp 2 volume)
  let J (j : ℕ) (x : E) := ∫ y, L j x y * f y
  have hAE (j : ℕ) : T j (f.toLp 2 volume) =ᵐ[volume] J j := by
    filter_upwards [hPair j (f.toLp 2 volume)] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp 2 volume] with y hy
    rw [hy]
  have hV (N : ℕ) : (V N : E → ℂ) =ᵐ[volume] fun x => ∑ j ∈ Finset.range N, J j x := by
    induction N with
    | zero =>
      simpa only [V, Finset.sum_range_zero] using Lp.coeFn_zero ℂ 2 (volume : Measure E)
    | succ N ih =>
      simp only [V, Finset.sum_range_succ]
      filter_upwards [Lp.coeFn_add (V N) (T N (f.toLp 2 volume)), ih, hAE N] with x hx h₁ h₂
      change ((V N + T N (f.toLp 2 volume) : ComplexL2 E) : E → ℂ) x =
        (∑ j ∈ Finset.range N, J j x) + J N x
      rw [hx, Pi.add_apply, h₁, h₂]
  have hFinite (N : ℕ) :
      (V N : E → ℂ) =ᵐ[volume] localizedPartialAngularDifference c d K hKU m N f := by
    filter_upwards [hV N] with x hx
    rw [hx]
    by_cases hX : x ∈ K
    · simp only [localizedPartialAngularDifference, dif_pos hX]
      exact (overlap_partialAngularFourier_difference_sum_actions c d K hK hKU hX m hm hd N
        f f.continuous).symm
    · simp only [J, hSupp _ x _ (Or.inl hX), zero_mul, integral_zero, Finset.sum_const_zero,
        localizedPartialAngularDifference, dif_neg hX]
  have hLimit : Tendsto V atTop (𝓝 (R (f.toLp 2 volume))) := by
    have h := (ContinuousLinearMap.apply ℂ (ComplexL2 E) (f.toLp 2 volume)).continuous.continuousAt
      |>.tendsto.comp hSum.hasSum.tendsto_sum_nat
    change Tendsto (fun N => (∑ j ∈ Finset.range N, T j) (f.toLp 2 volume)) atTop
      (𝓝 (R (f.toLp 2 volume))) at h
    simpa only [V, ContinuousLinearMap.sum_apply] using h
  exact ae_eq_of_tendsto_L2_and_pointwise V (R (f.toLp 2 volume))
    (fun N => localizedPartialAngularDifference c d K hKU m N f) _ hFinite hLimit
    (tendsto_localizedPartialAngularDifference c d K hKU m hm f hF hTransport)

end Burnett.Microlocal.AtlasOverlapKernel
