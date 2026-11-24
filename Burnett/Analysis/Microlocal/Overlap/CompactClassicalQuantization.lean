import Burnett.Analysis.Microlocal.Overlap.ActualClassicalFullSymbol

/-! Bounded L² quantization for compact-base classical full symbols. -/

set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E radialCore radialCore_eq_zero radialCore_nonneg radialCore_le_one)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.CompactFrequencyCutoff (smoothCutoffSymbol)
open Burnett.Microlocal.SeparablePositive
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

open private oscillatoryCutoff continuous_symbolCLM_oscillatoryCutoff
  norm_fourierMultiplier_sub_le continuous_operatorFamily_of_uniform
  from Burnett.Analysis.Microlocal.CompactFrequencyCutoff
open private baseFourierCoefficient_eventually_uniform
  from Burnett.Analysis.Microlocal.Overlap.AngularOrderMinusOneQuantization

/-- Integrating the separated base Fourier modes realizes the actual left
symbol on L². The output cutoff ensures continuity in operator norm. -/
theorem exists_bounded_compactBaseZero_leftAction (p : E → E → ℂ) (S : Set E)
    (hS : IsCompact S) (hs : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S)
    (hp : ContDiff ℝ ∞ (uncurry p))
    (hOrder : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C) :
    ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E, ∀ f v : SchwartzMap E ℂ,
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) = classicalLeftPairing p f v := by
  obtain ⟨_, _, _, _, α, hαSmooth, hαC, _, _, hα⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hS isOpen_univ (subset_univ S)
  have hSmooth (ξ : E) : ContDiff ℝ ∞ (fun x => p x ξ) := hp.comp (contDiff_id.prodMk contDiff_const)
  have hBase := compactBaseOrderOne_frequencyWeight ⟨S, hS, hs⟩ hSmooth hOrder
  obtain ⟨C, _, hI, hB⟩ := baseFourierCoefficient_dominated hBase
  let g (k : E) : ℝ := C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹
  let m := baseFourierCoefficientSymbol p hp.continuous.measurable g hB
  let a : D := ⟨α, hαSmooth, hαC⟩
  let ψ := smoothCutoffSymbol a
  let Q (k : E) := (symbolCLM (oscillatoryCutoff ψ k)).comp (fourierMultiplier (m k))
  have hFM : Continuous (fun k => fourierMultiplier (m k)) := by
    refine continuous_operatorFamily_of_uniform m fourierMultiplier norm_fourierMultiplier_sub_le ?_
    intro k ε hε
    obtain ⟨D, hD, hBounds⟩ := hOrder 0
    have hUniform (x ξ : E) : ‖p x ξ‖ ≤ D := by
      simpa only [norm_iteratedFDeriv_zero] using hBounds x ξ
    exact baseFourierCoefficient_eventually_uniform p S hS hs hp.continuous D hD hUniform k ε hε
  have hQM : Continuous Q :=
    (continuous_symbolCLM_oscillatoryCutoff ψ (hαC.comp_left Complex.ofReal_zero)).clm_comp hFM
  have hQI : Integrable Q := by
    refine (hI.const_mul ψ.bound).mono' hQM.aestronglyMeasurable (Eventually.of_forall fun k => ?_)
    have hLeft : ‖symbolCLM (oscillatoryCutoff ψ k)‖ ≤ ψ.bound :=
      ContinuousLinearMap.opNorm_le_bound _ ψ.bound_nonneg (symbolL2_norm_le (oscillatoryCutoff ψ k))
    have hRight : ‖fourierMultiplier (m k)‖ ≤ g k :=
      ContinuousLinearMap.opNorm_le_bound _ (m k).bound_nonneg (fourierMultiplier_norm_le (m k))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hLeft hRight (norm_nonneg _) ψ.bound_nonneg)
  refine ⟨∫ k, Q k, ?_⟩
  intro f v
  have hMode (k : E) : inner ℂ (f.toLp 2 volume) (Q k (v.toLp 2 volume)) =
      inner ℂ ((coeffMul a f).toLp 2 volume)
        (separableOperator (baseFourierPhaseSymbol k) (m k) (v.toLp 2 volume)) := by
    simp only [Q, ContinuousLinearMap.comp_apply, coeffMul_toLp, inner_symbolCLM_left]
    congr 1
    simp only [separableOperator, ContinuousLinearMap.comp_apply, ← symbolCLM_product]
    apply symbolL2_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [oscillatoryCutoff, productSymbol_apply, baseFourierPhaseSymbol, baseFourierPhase,
        Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ψ, conjugateSymbol_apply,
        smoothCutoffSymbol, physicalCoefficient, Complex.conj_ofReal]
      ring
  let Λ := (innerSL ℂ (f.toLp 2 volume)).comp
    (ContinuousLinearMap.apply ℂ (ComplexL2 E) (v.toLp 2 volume))
  have hSwap := (Λ.integral_comp_comm hQI).symm
  have hPair := firstOrderAction_pairing_eq_integral_separable_baseFourier p m
    (measurable_baseFourierCoefficient hp.continuous.measurable) g hI (fun _ => le_rfl)
    (baseFourierCoefficient_inverse hBase) v (coeffMul a f)
  calc
    _ = ∫ k, inner ℂ (f.toLp 2 volume) (Q k (v.toLp 2 volume)) := hSwap
    _ = ∫ x, conj (coeffMul a f x) * firstOrderAction p v x :=
      (integral_congr_ae (Eventually.of_forall hMode)).trans hPair.2.symm
    _ = classicalLeftPairing p f v := by
      unfold classicalLeftPairing
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ S
      · change conj ((α x : ℂ) * f x) * _ = _
        rw [hα x hx, Complex.ofReal_one, one_mul]
      · have hZero (ξ : E) : p x ξ = 0 := image_eq_zero_of_notMem_tsupport (f := fun z => p z ξ)
          (fun h => hx (hs ξ h))
        have hAction : firstOrderAction p v x = 0 := by
          simp only [firstOrderAction, Real.fourierIntegralInv_eq', hZero, zero_mul, smul_zero, integral_zero]
        simp only [hAction, mul_zero]

private theorem infraredAngularPrincipal_baseDerivative_le (a : E → E → ℂ) (n : ℕ) (x ξ : E)
    (ha : ContDiff ℝ ∞ (fun y => a y ξ)) :
    ‖iteratedFDeriv ℝ n (fun y => infraredAngularPrincipal a y ξ) x‖ ≤
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ := by
  let θ : ℂ := 1 - (radialCore ξ : ℂ)
  have hθ : ‖θ‖ ≤ 1 := by
    change ‖(1 : ℂ) - (radialCore ξ : ℂ)‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ξ))]
    exact sub_le_self _ (radialCore_nonneg ξ)
  have hN : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hA : ContDiffAt ℝ n (fun y => a y ξ) x := ha.contDiffAt.of_le hN
  have he : (fun y => infraredAngularPrincipal a y ξ) = θ • (fun y => a y ξ) := rfl
  rw [he, iteratedFDeriv_const_smul_apply hA, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hθ

private theorem classicalFullSymbol_uniform_baseDerivative {b a : E → E → ℂ} {S : Set E} (hS : IsCompact S)
    (ha : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S) (hbDiff : ContDiff ℝ ∞ (uncurry b))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (haZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (hDecay : OrderMinusOneBounds (classicalFullRemainder b a)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, ‖iteratedFDeriv ℝ n (fun y => b y ξ) x‖ ≤ C := by
  let p := infraredAngularPrincipal a
  let q := classicalFullRemainder b a
  have hp : ContDiff ℝ ∞ (uncurry p) := contDiff_uncurry_infraredAngularPrincipal haDiff
  have hq : ContDiff ℝ ∞ (uncurry q) := hbDiff.sub hp
  obtain ⟨C, hC, hBA⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS ha haDiff haZero hDegree n
  obtain ⟨D, hD, hBQ⟩ := hDecay n
  refine ⟨C + D, add_nonneg hC hD, fun x ξ => ?_⟩
  let P (x : E) := p x ξ
  let Q (x : E) := q x ξ
  have hf (W : E × E → ℂ) (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (fun y : E => W (y, ξ)) :=
    hW.comp (contDiff_id.prodMk contDiff_const)
  have hN : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hpa : ContDiffAt ℝ n P x := ((hf _ hp).contDiffAt (x := x)).of_le hN
  have hqa : ContDiffAt ℝ n Q x := ((hf _ hq).contDiffAt (x := x)).of_le hN
  have hAξ : ContDiff ℝ ∞ (fun y => a y ξ) := contDiff_baseAngularSection a haDiff haZero ξ
  have hP : ‖iteratedFDeriv ℝ n P x‖ ≤ C :=
    (infraredAngularPrincipal_baseDerivative_le a n x ξ hAξ).trans (hBA x ξ)
  have hQ : ‖iteratedFDeriv ℝ n Q x‖ ≤ D :=
    (le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg ξ))).trans (hBQ x ξ)
  have hEq : (fun y => b y ξ) = P + Q := by
    funext y
    change b y ξ = p y ξ + (b y ξ - p y ξ)
    ring
  rw [hEq, iteratedFDeriv_add_apply hpa hqa]
  exact (norm_add_le _ _).trans (add_le_add hP hQ)

/-- The compact-base classical symbol itself supplies a bounded operator
and the local representation on each compact right window. -/
theorem exists_classicalFullSymbolOperator (b a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hb : ∀ ξ, tsupport (fun x => b x ξ) ⊆ S)
    (ha : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hbDiff : ContDiff ℝ ∞ (uncurry b))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (haZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (R : ℝ) (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C) :
    ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ f v : SchwartzMap E ℂ, inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) =
        classicalLeftPairing b f v) ∧
      ∀ L : Set E, IsCompact L → HasLocalClassicalRepresentation T a L := by
  have hDecay := orderMinusOneBounds_classicalFullRemainder hS hb ha hbDiff haDiff R hLarge
  have hOrder := classicalFullSymbol_uniform_baseDerivative hS ha hbDiff haDiff haZero hDegree hDecay
  obtain ⟨T, hAct⟩ := exists_bounded_compactBaseZero_leftAction b S hS hb hbDiff hOrder
  refine ⟨T, hAct, fun L hL => ?_⟩
  exact hasLocalClassicalRepresentation_of_fullSymbolPairing T b a S L hS hL
    hb ha hbDiff haDiff haZero hDegree R hLarge (fun f v _ => hAct f v)

/-- A known compact smoothing contribution can be retained in the same operator. -/
theorem hasLocalClassicalRepresentation_add_compact
    (T S : ComplexL2 E →L[ℂ] ComplexL2 E) (a : E → E → ℂ) (L : Set E)
    (hT : HasLocalClassicalRepresentation T a L) (hS : IsCompactOperator S) :
    HasLocalClassicalRepresentation (T + S) a L := by
  obtain ⟨R, hR, hRep⟩ := hT
  refine ⟨R + S, hR.add hS, fun f v hv => ?_⟩
  simp only [ContinuousLinearMap.add_apply, inner_add_right, hRep f v hv, add_assoc]

/-- Every smooth compact-base degree-zero principal symbol has a bounded
realization with the paper's fixed infrared regularization. -/
theorem exists_infraredAngularPrincipalOperator (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (ha : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (haZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x)) :
    ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ f v : SchwartzMap E ℂ, inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) =
        classicalLeftPairing (infraredAngularPrincipal a) f v) ∧
      ∀ L : Set E, IsCompact L → HasLocalClassicalRepresentation T a L := by
  have hSupp (ξ : E) : tsupport (fun x => infraredAngularPrincipal a x ξ) ⊆ S :=
    tsupport_mul_subset_right.trans (ha ξ)
  refine exists_classicalFullSymbolOperator _ a S hS hSupp ha
    (contDiff_uncurry_infraredAngularPrincipal haDiff) haDiff haZero hDegree 2 ?_
  intro n
  refine ⟨0, le_rfl, fun x ξ hξ => ?_⟩
  have hEq : (fun y => infraredAngularPrincipal a y ξ - a y ξ) = fun _ => (0 : ℂ) := by
    funext y
    simp [infraredAngularPrincipal, radialCore_eq_zero ξ hξ]
  simp [hEq]

end Burnett.Microlocal.Overlap
