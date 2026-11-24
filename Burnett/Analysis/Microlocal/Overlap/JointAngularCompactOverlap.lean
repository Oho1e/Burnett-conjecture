import Burnett.Analysis.Microlocal.Overlap.JointAngularOverlapEnvelope
import Burnett.Analysis.Microlocal.Overlap.CompactWindowKernel
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartHalfDensity

/-! The source-chart difference for a genuine joint principal symbol is compact. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E dyadicScale shellKernel)
open Burnett.Microlocal.Overlap Burnett.Microlocal.OverlapKernel
open scoped ContDiff ENNReal FourierTransform InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private def jointOverlapShellKernel (c d : AtlasChart M) (K : Set E) (a : E → BoundedSymbol E)
    (ha : ∀ x, ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (x y : E) : ℂ :=
  localizedOverlapShellDifference c d K (a (overlapTransition c d x)) (ha (overlapTransition c d x)) j x y

private theorem jointOverlapShellKernel_regular
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (a : E → BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (hS : ∀ x, ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    Measurable (uncurry (jointOverlapShellKernel c d K a hS j)) ∧
      ContinuousOn (uncurry (jointOverlapShellKernel c d K a hS j)) (K ×ˢ K) := by
  let Φ := overlapTransition c d
  let w := overlapJacobianWeight c d
  let k (z : E × E) := shellKernel (a z.1) (hS z.1) j z.2
  have hk : Continuous k := continuous_shellKernel_family a ha hS j
  let D (p : E × E) := (fderiv ℝ Φ p.1) (p.1 - p.2)
  let R (p : E × E) := ((w p.1 * w p.2) • k (Φ p.1, Φ p.1 - Φ p.2)) -
    (w p.1)^2 • k (Φ p.1, D p)
  have hRaw : uncurry (jointOverlapShellKernel c d K a hS j) = (K ×ˢ K).indicator R := by
    funext p
    rfl
  have hΦm : Measurable Φ := overlapTransition_measurable c d
  have hwm : Measurable w := overlapJacobianWeight_measurable c d
  have hDm : Measurable D :=
    (continuous_fst.clm_apply continuous_snd :
      Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2)).measurable.comp
      (((measurable_fderiv ℝ Φ).comp measurable_fst).prodMk
        (measurable_fst.sub measurable_snd))
  have hΦ₁ : Measurable (fun z : E × E => Φ z.1) := hΦm.comp measurable_fst
  have hRm : Measurable R :=
    (((hwm.comp measurable_fst).mul (hwm.comp measurable_snd)).smul
      (hk.measurable.comp (hΦ₁.prodMk (hΦ₁.sub (hΦm.comp measurable_snd))))).sub
      (((hwm.comp measurable_fst).pow_const 2).smul (hk.measurable.comp (hΦ₁.prodMk hDm)))
  refine ⟨hRaw.symm ▸ hRm.indicator (hK.measurableSet.prod hK.measurableSet), ?_⟩
  have hΦc : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hwc : ContinuousOn w K := (overlapJacobianWeight_continuousOn c d).mono hKU
  have hcD₀ : ContDiffOn ℝ 0 (fderiv ℝ Φ) (c.transition d).source :=
    (overlapTransition_contDiffOn c d).fderiv_of_isOpen (c.transition d).open_source (by simp)
  have hF : MapsTo (Prod.fst : E × E → E) (K ×ˢ K) K := fun _ hz => hz.1
  have hG : MapsTo (Prod.snd : E × E → E) (K ×ˢ K) K := fun _ hz => hz.2
  have hDx : ContinuousOn D (K ×ˢ K) :=
    ((hcD₀.continuousOn.mono hKU).comp continuous_fst.continuousOn hF).clm_apply
      (continuous_fst.sub continuous_snd).continuousOn
  have hΦ₁' := hΦc.comp continuous_fst.continuousOn hF
  have hΦ₂' := hΦc.comp continuous_snd.continuousOn hG
  have hw₁ := hwc.comp continuous_fst.continuousOn hF
  have hw₂ := hwc.comp continuous_snd.continuousOn hG
  have hRc : ContinuousOn R (K ×ˢ K) :=
    ((hw₁.mul hw₂).smul (hk.comp_continuousOn (hΦ₁'.prodMk (hΦ₁'.sub hΦ₂')))).sub
      ((hw₁.pow 2).smul (hk.comp_continuousOn (hΦ₁'.prodMk hDx)))
  rw [hRaw]
  exact hRc.congr fun x hx => indicator_of_mem hx R

/-- The Fourier difference with the angular input frozen at the actual output position. -/
def localizedJointAngularDifference (c d : AtlasChart M) (K : Set E)
    (hKU : K ⊆ (c.transition d).source) (a : E → BoundedSymbol E) (f : E → ℂ) (x : E) : ℂ :=
  localizedNormalizedAngularDifference c d K hKU (a (overlapTransition c d x)) f x

theorem exists_compact_localizedJointAngularDifference
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (a : E → BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (hS : ∀ x, ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E))
    (hd : ∀ x, DegreeZero (a x : E → ℂ)) :
    ∃ R : ComplexL2 E →L[ℂ] ComplexL2 E, IsCompactOperator R ∧
      ∀ f : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ K →
        R (f.toLp 2 volume) =ᵐ[volume] localizedJointAngularDifference c d K hKU a f := by
  let L := jointOverlapShellKernel c d K a hS
  let Φ := overlapTransition c d
  obtain ⟨q, A, hq, hA, hEnv⟩ := jointAngular_overlapShell_uniform_envelope c d K hK hKU hConv a ha hS
  have hs (j : ℕ) : 0 < dyadicScale j := by unfold dyadicScale; positivity
  have hSupp (j : ℕ) (x y : E) (h : x ∉ K ∨ y ∉ K) : L j x y = 0 := by
    have hxy : (x, y) ∉ K ×ˢ K := fun hz => h.elim (fun hx => hx hz.1) (fun hy => hy hz.2)
    simp only [L, jointOverlapShellKernel, localizedOverlapShellDifference, indicator_of_notMem hxy]
  have hNorm (j : ℕ) (x y : E) : ‖L j x y‖ ≤
      A * dyadicScale j ^ 3 / (1 + dyadicScale j * q * ‖x - y‖) ^ 5 := by
    by_cases hxy : (x, y) ∈ K ×ˢ K
    · simpa only [L, jointOverlapShellKernel, localizedOverlapShellDifference, indicator_of_mem hxy]
        using hEnv j x hxy.1 y hxy.2
    · simp only [L, jointOverlapShellKernel, localizedOverlapShellDifference, indicator_of_notMem hxy, norm_zero]
      have hs₀ := (hs j).le
      positivity
  let chooseShell (j : ℕ) :=
    exists_compact_windowKernel_schur (L j) K hK
      (jointOverlapShellKernel_regular c d K hK hKU a ha hS j).1
      (jointOverlapShellKernel_regular c d K hK hKU a ha hS j).2
      (hSupp j) A q (dyadicScale j) hA hq (hs j) (hNorm j)
  choose T hT hTN hPair using chooseShell
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
  let P (N : ℕ) (x : E) := localizedPartialAngularDifference c d K hKU (a (Φ x)) N f x
  have hFinite (N : ℕ) : (V N : E → ℂ) =ᵐ[volume] P N := by
    filter_upwards [hV N] with x hx
    rw [hx]
    by_cases hX : x ∈ K
    · simp only [P, localizedPartialAngularDifference, dif_pos hX]
      exact (overlap_partialAngularFourier_difference_sum_actions c d K hK hKU hX (a (Φ x))
        (hS (Φ x)) (hd (Φ x)) N f f.continuous).symm
    · simp only [J, hSupp _ x _ (Or.inl hX), zero_mul, integral_zero, Finset.sum_const_zero,
        P, localizedPartialAngularDifference, dif_neg hX]
  have hLimit : Tendsto V atTop (𝓝 (R (f.toLp 2 volume))) := by
    have h := (ContinuousLinearMap.apply ℂ (ComplexL2 E) (f.toLp 2 volume)).continuous.continuousAt
      |>.tendsto.comp hSum.hasSum.tendsto_sum_nat
    change Tendsto (fun N => (∑ j ∈ Finset.range N, T j) (f.toLp 2 volume)) atTop
      (𝓝 (R (f.toLp 2 volume))) at h
    simpa only [V, ContinuousLinearMap.sum_apply] using h
  exact ae_eq_of_tendsto_L2_and_pointwise V (R (f.toLp 2 volume)) P _ hFinite hLimit
    (fun x => tendsto_localizedPartialAngularDifference c d K hKU (a (Φ x)) (hS (Φ x)) f hF hTransport x)

end Burnett.Microlocal.AtlasOverlapKernel
