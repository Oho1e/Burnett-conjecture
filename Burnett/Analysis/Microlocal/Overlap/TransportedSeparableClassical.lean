import Burnett.Analysis.Microlocal.Overlap.CompactReceivingAngularDifference
import Burnett.Analysis.Microlocal.Overlap.CompactClassicalQuantization
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartBaseModes
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartRepresentedPairing

/-! Changing charts in an actual cut angular multiplier produces a bounded
source-coordinate operator with the natural principal symbol and a compact
remainder. The transplanted pairing is an exact equality. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol radialCore_eq_zero)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.SeparablePositive (separableOperator)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- For a bounded separated multiplier in the target chart, this is its
actual source-window pairing in the same Lebesgue half-density coordinates.
The bounded source operator has the natural moving principal symbol. -/
theorem exists_classical_transportedSeparableOperator
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (a m : BoundedSymbol E) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (haS : tsupport (a : E → ℂ) ⊆ K)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ)) :
    ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      HasLocalClassicalRepresentation T (fun x ξ => movingChartAngularSymbol c d a m (x, ξ)) K ∧
      ∀ (b : BoundedSymbol E) (f v : SchwartzMap E ℂ),
        ∀ (hf : tsupport (f : E → ℂ) ⊆ K) (hv : tsupport (v : E → ℂ) ⊆ K),
        (∀ x ∈ tsupport (v : E → ℂ), a x = b (c.transition d x)) →
        let F := transportedHalfDensitySchwartz c d K hK hKU f hf
        let V := transportedHalfDensitySchwartz c d K hK hKU v hv
        inner ℂ (V.toLp 2 volume) (separableOperator b (normalizedAngularSymbol m) (F.toLp 2 volume)) =
          inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  let p (x ξ : E) := movingChartAngularSymbol c d a m (x, ξ)
  let B (x ξ : E) := a x * normalizedAngularSymbol m (receivingFrequency c d x ξ)
  let S := movingChartFixedCoreSymbol c d a m
  let I := movingChartInfraredRemainder c d a m
  let A := symbolCLM a
  have hAS (x : E) (hx : x ∉ K) : a x = 0 :=
    image_eq_zero_of_notMem_tsupport (f := (a : E → ℂ)) (fun h => hx (haS h))
  have hP (ξ : E) : tsupport (fun x => p x ξ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra h
    exact hx (by simp only [p, movingChartAngularSymbol, hAS x h, zero_mul])
  have hB (ξ : E) : tsupport (fun x => B x ξ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra h
    exact hx (by simp only [B, hAS x h, zero_mul])
  have hBs : uncurry B = S + I := by
    funext z
    by_cases hz : z.1 ∈ K
    · simpa only [B, S, I, uncurry, Pi.add_apply, chartTransitionFrequency_eq_frozen c d (hKU hz)] using
        movingChartNormalizedSymbol_eq_fixedCore_add c d a m (hKU hz) z.2
    · simp only [B, S, I, uncurry, Pi.add_apply, movingChartFixedCoreSymbol,
        movingChartInfraredRemainder, movingChartAngularSymbol, hAS _ hz, zero_mul, mul_zero, add_zero]
  have hBD : ContDiff ℝ ∞ (uncurry B) := by
    rw [hBs]
    exact (contDiff_movingChartFixedCoreSymbol c d a m ha (haS.trans hKU) hm).add
      (contDiff_movingChartInfraredRemainder c d a m K hK hKU haS ha hm)
  have hPD : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    contDiffOn_movingChartAngularSymbol c d a m ha (haS.trans hKU) hm
  have hP0 : ContDiff ℝ ∞ (fun x => p x 0) := by
    simp only [p, movingChartAngularSymbol, map_zero]
    exact ha.mul contDiff_const
  obtain ⟨ρ, _, hIS⟩ := exists_movingChartInfraredRemainder_tsupport_subset c d a m K hK hKU haS
  let ρ₀ := max 2 (ρ + 1)
  have hHigh (ξ : E) (hξ : ρ₀ ≤ ‖ξ‖) :
      (fun x => B x ξ - p x ξ) = fun _ => (0 : ℂ) := by
    funext x
    have hi : I (x, ξ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      have h := (hIS hp).2
      change dist ξ 0 ≤ ρ at h
      rw [dist_zero_right] at h
      linarith [le_max_right (2 : ℝ) (ρ + 1)]
    have hEq : B x ξ = S (x, ξ) + I (x, ξ) := congrFun hBs (x, ξ)
    rw [hEq, hi]
    simp only [S, movingChartFixedCoreSymbol,
      radialCore_eq_zero ξ ((le_max_left _ _).trans hξ), sub_zero, Complex.ofReal_one,
      one_mul, p, add_zero, sub_self]
  obtain ⟨T₀, hT₀, hRep⟩ := exists_classicalFullSymbolOperator B p K hK hB hP hBD hPD hP0
    (movingChartAngularSymbol_degreeZero c d a m hd) ρ₀ (by
      intro n
      exact ⟨0, le_rfl, fun x ξ hξ => by simp [hHigh ξ hξ]⟩)
  obtain ⟨R, hR, hAct⟩ :=
    exists_compact_localizedNormalizedAngularDifference c d K hK hKU hConv m hm hd
  refine ⟨T₀ + A.comp R, hasLocalClassicalRepresentation_add_compact T₀ (A.comp R) p K
    (hRep K hK) (hR.clm_comp A), fun b f v hf hv hPull => ?_⟩
  intro F V
  have hInd : K.indicator (f : E → ℂ) = f := by
    funext x
    by_cases h : x ∈ K
    · exact indicator_of_mem h _
    · rw [indicator_of_notMem h]
      exact (image_eq_zero_of_notMem_tsupport (fun h' => h (hf h'))).symm
  have hFrozen (x : E) (hx : x ∈ K) : firstOrderAction B f x =
      a x * (𝓕⁻ (fun ξ => normalizedAngularSymbol m (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator (f : E → ℂ))) ξ)) x := by
    rw [firstOrderAction_integrand_eq, Real.fourierIntegralInv_eq', ← integral_const_mul, hInd]
    apply integral_congr_ae
    filter_upwards with ξ
    change baseFourierPhase ξ x * (B x ξ * (𝓕 (f : E → ℂ)) ξ) =
      a x * (baseFourierPhase ξ x * (normalizedAngularSymbol m (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (f : E → ℂ)) ξ))
    simp only [B, chartTransitionFrequency_eq_frozen c d (hKU hx)]
    ring
  let err := localizedNormalizedAngularDifference c d K hKU m f
  have hActA : A (R (f.toLp 2 volume)) =ᵐ[volume] fun x => a x * err x := by
    filter_upwards [symbolL2_ae a (R (f.toLp 2 volume)), hAct f hf] with x h₁ h₂
    change symbolL2 a (R (f.toLp 2 volume)) x = _
    rw [h₁, h₂]
  have hInnerR : inner ℂ (v.toLp 2 volume) ((A.comp R) (f.toLp 2 volume)) =
      ∫ x, conj (v x) * (a x * err x) := by
    rw [ContinuousLinearMap.comp_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [v.coeFn_toLp 2 volume, hActA] with x h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply']
  have hIntR : Integrable (fun x => conj (v x) * (a x * err x)) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (v.toLp 2 volume) (A (R (f.toLp 2 volume)))).congr
    filter_upwards [v.coeFn_toLp 2 volume, hActA] with x h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply']
  have hIntB := integrable_tested_bounded_leftAction B hBD.continuous.measurable
    (a.bound * (normalizedAngularSymbol m).bound) (fun x ξ => by
      change ‖a x * normalizedAngularSymbol m (receivingFrequency c d x ξ)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (a.norm_le x) ((normalizedAngularSymbol m).norm_le _)
        (norm_nonneg _) a.bound_nonneg) f v
  change inner ℂ (V.toLp 2 volume) (separableOperator b (normalizedAngularSymbol m) (F.toLp 2 volume))
    = inner ℂ (v.toLp 2 volume) ((T₀ + A.comp R) (f.toLp 2 volume))
  rw [transportedSeparable_pairing_eq c d K hK hKU a b m f v hf hv hPull,
    ContinuousLinearMap.add_apply, inner_add_right, hT₀ v f, hInnerR, classicalLeftPairing,
    ← integral_add hIntB hIntR]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [hFrozen x hx]
    simp only [err, localizedNormalizedAngularDifference, localizedTransportedAngularAction,
      dif_pos hx, indicator_of_mem hx]
    ring
  · have hv0 : v x = 0 := image_eq_zero_of_notMem_tsupport
      (f := (v : E → ℂ)) (fun h => hx (hv h))
    simp only [hv0, map_zero, zero_mul, add_zero]

/-- An arbitrary smooth bounded target base factor has this exact
half-density transport on all Schwartz tests in a compact interior window.
The source base cutoff is constructed from the windows. -/
theorem exists_classical_transportedSeparableOperator_on_compactInterior
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (b m : BoundedSymbol E) (hb : ContDiff ℝ ∞ (b : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ)) :
    ∃ (p : E → E → ℂ) (T : ComplexL2 E →L[ℂ] ComplexL2 E),
      (∀ x ∈ L, ∀ ξ, p x ξ = b (c.transition d x) * m (receivingFrequency c d x ξ)) ∧
      HasLocalClassicalRepresentation T p L ∧
      ∀ f v : SchwartzMap E ℂ,
        ∀ (hf : tsupport (f : E → ℂ) ⊆ L) (hv : tsupport (v : E → ℂ) ⊆ L),
        let hLK' := hLK.trans interior_subset
        let F := transportedHalfDensitySchwartz c d K hK hKU f (hf.trans hLK')
        let V := transportedHalfDensitySchwartz c d K hK hKU v (hv.trans hLK')
        inner ℂ (V.toLp 2 volume) (separableOperator b (normalizedAngularSymbol m) (F.toLp 2 volume)) =
          inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  obtain ⟨a, ha, haS, _, hPull⟩ := exists_receivingBaseMode_pullback c d L K hL hLK hKU b hb
  obtain ⟨T, hRep, hTransport⟩ :=
    exists_classical_transportedSeparableOperator c d K hK hKU hConv a m ha haS hm hd
  have hLK' := hLK.trans interior_subset
  refine ⟨fun x ξ => movingChartAngularSymbol c d a m (x, ξ), T,
    fun x hx ξ => ?_, ?_, fun f v hf hv => ?_⟩
  · simp only [movingChartAngularSymbol, hPull x hx]
  · obtain ⟨R, hR, hRep⟩ := hRep
    exact ⟨R, hR, fun f v hv => hRep f v (hv.trans hLK')⟩
  · exact hTransport b f v (hf.trans hLK') (hv.trans hLK') (fun x hx => hPull x (hv hx))

end Burnett.Microlocal.AtlasOverlapKernel
