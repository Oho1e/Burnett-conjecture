import Burnett.Analysis.Microlocal.Overlap.JointAngularCompactOverlap
import Burnett.Analysis.Microlocal.Overlap.JointAngularMovingPrincipal
import Burnett.Analysis.Microlocal.Overlap.LeftActionPairingBounds

/-! Transport of the actual joint principal quantization in half-density coordinates. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 4300000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol radialCore radialCore_nonneg radialCore_le_one)
open Burnett.Microlocal.Overlap Burnett.Microlocal.OverlapKernel
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

open private firstOrderAction_mul_base from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal
open private receivingJointSymbol_contDiff from Burnett.Analysis.Microlocal.Overlap.JointAngularMovingPrincipal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem normalizedAngularSymbol_eq_jointIR (a : E → BoundedSymbol E) (x ξ : E) :
    normalizedAngularSymbol (a x) ξ = infraredAngularPrincipal (fun y ζ => a y ζ) x ξ := by
  change (1 - (radialCore ((1 : ℝ) • ξ) : ℂ)) * a x ξ = _
  rw [one_smul]
  rfl

/-- An actual bounded normalized scalar quantization of a smooth, jointly
dependent principal symbol has the natural represented source operator.
The transported Schwartz pairing is an exact identity on the fixed window. -/
theorem exists_classical_transportedJointAngularOperator
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K) (hLK : L ⊆ K)
    (χ : BoundedSymbol E) (hχ : ContDiff ℝ ∞ (χ : E → ℂ))
    (hχK : tsupport (χ : E → ℂ) ⊆ K) (hχL : ∀ x ∈ L, χ x = 1)
    (a : E → BoundedSymbol E) (S : Set E) (hS : IsCompact S)
    (hAs : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (hAz : ContDiff ℝ ∞ (fun x => a x 0))
    (hAd : ∀ x, DegreeZero (a x : E → ℂ)) :
    ∃ A T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ f v : SchwartzMap E ℂ,
        inner ℂ (v.toLp 2 volume) (A (f.toLp 2 volume)) =
          classicalLeftPairing (infraredAngularPrincipal (fun x ξ => a x ξ)) v f) ∧
      HasLocalClassicalRepresentation T (receivingJointSymbol c d χ (fun x ξ => a x ξ)) K ∧
      ∀ f v : SchwartzMap E ℂ,
        ∀ (hf : tsupport (f : E → ℂ) ⊆ K) (hv : tsupport (v : E → ℂ) ⊆ L),
          let F := transportedHalfDensitySchwartz c d K hK hKU f hf
          let V := transportedHalfDensitySchwartz c d K hK hKU v (hv.trans hLK)
          inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) =
            inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  let p (x ξ : E) := a x ξ
  let q := infraredAngularPrincipal p
  let P := receivingJointSymbol c d χ q
  let C := symbolCLM χ
  have hSlice (x : E) : ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E) :=
    ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨mem_univ _, hz⟩)
  obtain ⟨A, hA, _⟩ := exists_infraredAngularPrincipalOperator p S hS hAs ha hAz hAd
  obtain ⟨T₀, hT₀, hRep⟩ := exists_receivingJointPrincipalOperator c d K hK hKU χ hχ hχK p ha hAz hAd
  obtain ⟨R, hR, hAct⟩ := exists_compact_localizedJointAngularDifference c d K hK hKU hConv a ha hSlice hAd
  refine ⟨A, T₀ + C.comp R, fun f v => hA v f, ?_, fun f v hf hv => ?_⟩
  · exact hasLocalClassicalRepresentation_add_compact T₀ (C.comp R)
      (receivingJointSymbol c d χ p) K hRep (hR.clm_comp C)
  intro F V
  let Φ := overlapTransition c d
  let w := overlapJacobianWeight c d
  let D := firstOrderAction q (F : E → ℂ)
  let err := localizedJointAngularDifference c d K hKU a f
  have hT : inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) =
      ∫ x, conj (v x) * K.indicator (fun z => w z • D (Φ z)) x := by
    rw [hA V F, classicalLeftPairing]
    have hChange := integral_transportHalfDensity_pairing c d K hK hKU v (fun _ => 1) D
    simpa only [one_mul, V, coe_transportedHalfDensitySchwartz, D, Φ, w] using hChange
  have hInd : K.indicator (f : E → ℂ) = f := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))).symm
  have hFrozen (x : E) (hx : x ∈ K) : firstOrderAction P f x =
      χ x * (𝓕⁻ (fun ξ => normalizedAngularSymbol (a (Φ x)) (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator (f : E → ℂ))) ξ)) x := by
    change firstOrderAction (fun y ξ => χ y * q (Φ y) (receivingFrequency c d y ξ)) f x = _
    rw [hInd, firstOrderAction_mul_base χ _ f x]
    congr 1
    unfold firstOrderAction
    apply congrArg (fun z : E → ℂ => (𝓕⁻ z) x)
    funext ξ
    rw [← chartTransitionFrequency_eq_frozen c d (hKU hx), normalizedAngularSymbol_eq_jointIR]
  have hActC : C (R (f.toLp 2 volume)) =ᵐ[volume] fun x => χ x * err x := by
    filter_upwards [symbolL2_ae χ (R (f.toLp 2 volume)), hAct f hf] with x h₁ h₂
    change symbolL2 χ (R (f.toLp 2 volume)) x = _
    rw [h₁, h₂]
  have hInnerR : inner ℂ (v.toLp 2 volume) ((C.comp R) (f.toLp 2 volume)) =
      ∫ x, conj (v x) * (χ x * err x) := by
    rw [ContinuousLinearMap.comp_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [v.coeFn_toLp 2 volume, hActC] with x h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply']
  have hIntR : Integrable (fun x => conj (v x) * (χ x * err x)) :=
    integrable_testedL2_representatives v _ (v.toLp 2 volume) _ (v.coeFn_toLp 2 volume) hActC
  have hPS : ContDiff ℝ ∞ (uncurry P) :=
    receivingJointSymbol_contDiff c d χ hχ (hχK.trans hKU) _ (contDiff_uncurry_infraredAngularPrincipal ha)
  obtain ⟨B, hB, hBound⟩ := exists_uniform_baseDerivative_of_homogeneousAngular p S hS hAs ha hAz hAd 0
  have hPBound (x ξ : E) : ‖P x ξ‖ ≤ χ.bound * B := by
    let ζ := receivingFrequency c d x ξ
    have hIR : ‖(1 : ℂ) - (radialCore ζ : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ζ))]
      exact sub_le_self _ (radialCore_nonneg ζ)
    have hP : ‖p (Φ x) ζ‖ ≤ B := by simpa only [norm_iteratedFDeriv_zero] using hBound (Φ x) ζ
    change ‖χ x * (((1 : ℂ) - (radialCore ζ : ℂ)) * p (Φ x) ζ)‖ ≤ _
    simp only [norm_mul]
    exact mul_le_mul (χ.norm_le x)
      (by simpa only [one_mul] using (mul_le_mul hIR hP (norm_nonneg _) zero_le_one))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) χ.bound_nonneg
  have hIntP := integrable_tested_bounded_leftAction P hPS.continuous.measurable _ hPBound f v
  rw [hT, ContinuousLinearMap.add_apply, inner_add_right, hT₀ f v, hInnerR, classicalLeftPairing,
    ← integral_add hIntP hIntR]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport (v : E → ℂ)
  · have hxK : x ∈ K := hLK (hv hx)
    rw [hFrozen x hxK, hχL x (hv hx), indicator_of_mem hxK]
    simp only [err, localizedJointAngularDifference, localizedNormalizedAngularDifference, dif_pos hxK,
      D, firstOrderAction, q, p, F, coe_transportedHalfDensitySchwartz, Φ, w]
    simp only [normalizedAngularSymbol_eq_jointIR, one_mul]
    ring
  · simp only [image_eq_zero_of_notMem_tsupport hx, map_zero, zero_mul, add_zero]

end Burnett.Microlocal.AtlasOverlapKernel
