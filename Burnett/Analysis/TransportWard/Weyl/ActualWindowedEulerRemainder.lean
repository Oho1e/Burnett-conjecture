import Burnett.Analysis.TransportWard.Weyl.PointwiseVacuum
import Burnett.Analysis.TransportWard.Weyl.ActualRemainderLimit
import Burnett.Analysis.TransportWard.Weyl.EulerLowerPairLimit
import Burnett.Analysis.TransportWard.Weyl.EulerRemainderPairing
import Burnett.Analysis.TransportWard.Weyl.EulerAffineRegularity
import Burnett.Analysis.TransportWard.Weyl.ActualWeylCompactMatrixTest

set_option autoImplicit false
set_option maxHeartbeats 5800000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V03

open Filter Set MeasureTheory Function Burnett.A03 Burnett.Fourier
open Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.SymmetricEnergy (coordinateDirection coordinateH1)
open Palatini
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix.Norms.Elementwise

open private coordinateH1_le_compactMatrixCoordinateH1 from Burnett.Analysis.PrincipalEnergy.Energy.CompactFourierNorms

/-- The actual Euler Taylor remainder paired with the actual Weyl output
tends to zero on the chart window. Both uses of the cutoff are exact on
the test support. -/
theorem tendsto_actualWindowedWeylEulerRemainder_of_chartBounds
    {ι : Type*} [Fintype ι]
    (θ : Space → ℝ) (β : Space → Space → ℂ) (R : ℝ)
    (ha : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hA : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hΘβ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) (hReal : ∀ x ξ, conj (β x ξ) = β x ξ)
    (S : ι → Mat) {U : Set Space} (hU : IsOpen U)
    (g : Space → ι → ℝ) (h : ℕ → Space → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ∀ n, ContDiffOn ℝ ∞ (h n) U)
    (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ)
    (hPlateau : ∀ x ∈ tsupport θ, ρ =ᶠ[𝓝 x] fun _ => 1)
    {K : Set Mat} (hK : IsCompact K) (hKdet : K ⊆ nonsingularMetricDomain)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (W P D P₁ D₁ P₂ F : ℝ) (hW : 0 ≤ W) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hP₁ : 0 ≤ P₁) (hD₁ : 0 ≤ D₁) (hP₂ : 0 ≤ P₂) (hF : 0 ≤ F)
    (hρ₀ : ∀ x, ‖ρ x‖ ≤ W) (hρ₁ : ∀ x, ‖fderiv ℝ ρ x‖ ≤ W) :
    let G (x : Space) := assembleMetricComponents S (g x)
    let H (n : ℕ) (x : Space) := assembleMetricComponents S (h n x)
    let f (n : ℕ) := chartMetricCutoffTest hU (h n) (hh n) ρ hρ hρU hρc
    let p := windowedWeylLeftSymbol θ β R ha
    (∀ n x, x ∈ U → ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (G x) (H n x) t ∈ K) →
    (∀ n x, x ∈ U → ‖H n x‖ ≤ ε n) →
    (∀ x ∈ U, ‖fderiv ℝ G x‖ ≤ P) →
    (∀ n x, x ∈ U → ‖fderiv ℝ (H n) x‖ ≤ D) →
    (∀ x ∈ tsupport θ, ∀ q, ‖coordinateMetricFirstJet g x q‖ ≤ P₁) →
    (∀ n x, x ∈ tsupport θ → ∀ q, ‖coordinateMetricFirstJet (h n) x q‖ ≤ D₁) →
    (∀ x ∈ tsupport θ, ∀ b q, ‖coordinateMetricSecondJet g x b q‖ ≤ P₂) →
    (∀ n, compactMatrixCoordinateH1 (f n) ≤ F) →
    Tendsto (fun n => 2 * (∫ x in U, ∑ i, conj (firstOrderAction p ((f n).val i) x) *
      (quadraticPathRemainder (fun t => coordinateDensityEuler S (fun y => g y + t • h n y) x i) : ℂ)).im)
        atTop (𝓝 0) := by
  intro G H f p hSeg hSmall hG₁ hH₁ hp hdp hq hF₁
  let V := tsupport θ
  have hV : IsCompact V := hθc
  have hVU : V ⊆ U := fun x hx => hρU (subset_tsupport ρ (by
    change ρ x ≠ 0
    rw [(hPlateau x hx).self_of_nhds]
    exact one_ne_zero))
  have hG : ContDiffOn ℝ ∞ G U := (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hH (n : ℕ) : ContDiffOn ℝ ∞ (H n) U := (assembleMetricComponents S).contDiff.comp_contDiffOn (hh n)
  have hND (n : ℕ) (x : Space) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    hKdet (hSeg n x hx t ht)
  have hGdet (x : Space) (hx : x ∈ U) : (G x).det ≠ 0 := by
    simpa only [fieldSegment, zero_smul, add_zero] using hND 0 x hx 0 (by simp)
  have hGHdet (n : ℕ) (x : Space) (hx : x ∈ U) : (G x + H n x).det ≠ 0 := by
    simpa only [fieldSegment, one_smul] using hND n x hx 1 (by simp)
  let A (n : ℕ) := chartMetricRemainderCoefficient S ρ G (H n)
  have hSmoothA (n : ℕ) (b d : Fin 4) (i j : ι) : ContDiff ℝ ∞ (A n b d i j) :=
    chartMetricRemainderCoefficient_smooth S hU hρ hρU hG (hH n) (hND n) b d i j
  let P₀ (n : ℕ) (i : ι) := compactFinitePrincipalField (A n) (f n) i
  let M₀ (n : ℕ) (i : ι) (x : Space) := (coordinateEulerLowerRemainder S g (h n) i x : ℂ)
  let R₀ (n : ℕ) (i : ι) (x : Space) :=
    (quadraticPathRemainder (fun t => coordinateDensityEuler S (fun y => g y + t • h n y) x i) : ℂ)
  have hDec (n : ℕ) (i : ι) (x : Space) (hx : x ∈ V) : R₀ n i x = P₀ n i x + M₀ n i x :=
    coordinateEulerRemainder_eq_compactPrincipal_add_lower S hU g (h n) hg (hh n) ρ hρ hρU hρc ρ
      (hVU hx) (hPlateau x hx) (hPlateau x hx).self_of_nhds i (hND n x (hVU hx))
  have hPc (n : ℕ) (i : ι) : Continuous (P₀ n i) := by
    unfold P₀ compactFinitePrincipalField
    exact continuous_finset_sum _ (fun b _ => continuous_finset_sum _ (fun d _ =>
      continuous_finset_sum _ (fun j _ => (hSmoothA n b d i j).continuous.mul (SchwartzMap.continuous _))))
  have hRc (n : ℕ) (i : ι) : ContinuousOn (R₀ n i) U := by
    have hOne := contDiffOn_coordinateDensityEuler S (fun y => g y + h n y) hU (hg.add (hh n))
      (fun x hx => by simpa only [map_add] using hGHdet n x hx) i
    have hZero := contDiffOn_coordinateDensityEuler S g hU hg hGdet i
    have hT := coordinateDensityEuler_affine_variations_contDiffOn S hU g (h n) hg (hh n) hGdet
    have hLin := (continuous_apply i).comp_continuousOn hT.1.continuousOn
    have hQuad := (continuous_apply i).comp_continuousOn hT.2.continuousOn
    exact Complex.continuous_ofReal.comp_continuousOn (by
      simpa only [R₀, quadraticPathRemainder, one_smul, zero_smul, add_zero] using
        (((hOne.continuousOn.sub hZero.continuousOn).sub hLin).sub
          ((continuousOn_const (c := (1 / 2 : ℝ))).mul hQuad)))
  have hMc (n : ℕ) (i : ι) : ContinuousOn (M₀ n i) V := by
    apply ((hRc n i).mono hVU |>.sub (hPc n i).continuousOn).congr
    intro x hx
    change M₀ n i x = R₀ n i x - P₀ n i x
    rw [hDec n i x hx, add_sub_cancel_left]
  have hLeft := windowedWeyl_leftSymbol_scaled_order_one θ β R ha hA hΘβ hβ
  have hDerivative (b : Fin 4) := hLeft.baseDirection (coordinateDirection b)
  have hProper := windowedWeyl_leftSymbol_proper θ β R ha hθc
    hLeft.firstBaseFrequency.frequency hLeft.smooth.continuous
  have hSym := windowedWeyl_leftAction_formallySymmetric θ β R ha hθ hθc
    (hβ.smooth.of_le (by simp)) hβ.firstBaseFrequency.frequency hReal
  let L (n : ℕ) (i : ι) := firstOrderAction p ((f n).val i)
  have hPmain := tendsto_chartMetricRemainderPrincipal_of_leftAction hLeft.firstBaseFrequency hLeft.smooth
    hLeft.pureBase (fun b => (hDerivative b).firstBaseFrequency) (fun b => (hDerivative b).pureBase)
    hProper hSym (fun v => firstOrderAction p v) (fun _ _ => rfl) S hU hρ hρU hK hKdet G H hG hH hSeg ε hε hεlim
    W P D F hW hP hD hρ₀ hρ₁ hSmall hG₁ hH₁ f hF₁
  obtain ⟨C, hC, hBnd⟩ := exists_firstOrderAction_global_h1_bound_of_properSupport
    hLeft.firstBaseFrequency hLeft.smooth hLeft.pureBase hProper
  choose hMem hB using fun n i => hBnd ((f n).val i) ((f n).property i)
  have hB₀ (n : ℕ) (i : ι) : ‖(hMem n i).toLp (L n i)‖ ≤ C * F :=
    (hB n i).trans (mul_le_mul_of_nonneg_left
      ((coordinateH1_le_compactMatrixCoordinateH1 (f n) i).trans (hF₁ n)) hC)
  have hLower := tendsto_metricEulerJetLowerRemainder_window_pair S hK hKdet hV G H
    (coordinateMetricFirstJet g) (fun n => coordinateMetricFirstJet (h n)) (coordinateMetricSecondJet g)
    (fun n x hx => hSeg n x (hVU hx)) ε hε (fun n x hx => hSmall n x (hVU hx)) hεlim
    P₁ D₁ P₂ hP₁ hD₁ hP₂ hp hdp hq L hMem (C * F) (mul_nonneg hC hF) hB₀
    (fun n i => (hMc n i).aestronglyMeasurable hV.measurableSet)
  have hLowerIm : Tendsto (fun n => 2 * (∑ i, ∫ x in V, conj (L n i x) * M₀ n i x).im)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Complex.zero_im, mul_zero] using
      (((Complex.continuous_im.tendsto 0).comp hLower).const_mul (2 : ℝ))
  obtain ⟨B, hExact, hSupp, _⟩ := exists_windowedWeylSchwartz_selfAdjoint θ β R ha hA hΘβ hθ hθc hβ hReal
  have hBc (n : ℕ) (i : ι) : Continuous (fun x => conj (L n i x)) := by
    have he : L n i = (B ((f n).val i) : Space → ℂ) := (funext (hExact ((f n).val i))).symm
    rw [he]
    exact Complex.continuous_conj.comp (B ((f n).val i)).continuous
  have hBz (n : ℕ) (i : ι) (x : Space) (hx : x ∉ V) : L n i x = 0 := by
    change firstOrderAction p ((f n).val i) x = 0
    rw [← hExact ((f n).val i) x]
    exact image_eq_zero_of_notMem_tsupport (fun hy => hx (hSupp _ hy))
  have hIntP (n : ℕ) (i : ι) : Integrable (fun x => conj (L n i x) * P₀ n i x) volume := by
    have hSupport : HasCompactSupport (fun x => conj (L n i x)) := by
      apply hV.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ hV.isClosed
      intro x hx
      by_contra hOut
      exact hx (by simp only [hBz n i x hOut, map_zero])
    exact ((hBc n i).mul (hPc n i)).integrable_of_hasCompactSupport hSupport.mul_right
  have hIntM (n : ℕ) (i : ι) : IntegrableOn (fun x => conj (L n i x) * M₀ n i x) V volume :=
    ((hBc n i).continuousOn.mul (hMc n i)).integrableOn_compact hV
  have hSum (n : ℕ) : (∫ x in U, ∑ i, conj (L n i x) * R₀ n i x) =
      (∑ i, ∫ x, conj (L n i x) * P₀ n i x) + (∑ i, ∫ x in V, conj (L n i x) * M₀ n i x) := by
    calc
      _ = ∫ x in V, ∑ i, conj (L n i x) * R₀ n i x := by
        rw [← integral_indicator hU.measurableSet, ← integral_indicator hV.measurableSet]
        apply integral_congr_ae
        exact .of_forall fun x => by
          by_cases hx : x ∈ V
          · rw [indicator_of_mem hx, indicator_of_mem (hVU hx)]
          · rw [indicator_of_notMem hx]
            by_cases hu : x ∈ U
            · simp only [indicator_of_mem hu, hBz n _ x hx, map_zero, zero_mul, Finset.sum_const_zero]
            · rw [indicator_of_notMem hu]
      _ = ∫ x in V, ∑ i, (conj (L n i x) * P₀ n i x + conj (L n i x) * M₀ n i x) :=
        setIntegral_congr_fun hV.measurableSet fun x hx => Finset.sum_congr rfl fun i _ => by
          rw [hDec n i x hx, mul_add]
      _ = ∑ i, ∫ x in V, conj (L n i x) * P₀ n i x + conj (L n i x) * M₀ n i x := by
        exact integral_finset_sum Finset.univ (fun i _ => (hIntP n i).integrableOn.add (hIntM n i))
      _ = _ := by
        have hSplit (i : ι) : (∫ x in V, conj (L n i x) * P₀ n i x + conj (L n i x) * M₀ n i x) =
            (∫ x in V, conj (L n i x) * P₀ n i x) + ∫ x in V, conj (L n i x) * M₀ n i x :=
          integral_add (hIntP n i).integrableOn (hIntM n i)
        simp only [hSplit, Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          simp only [hBz n i x hx, map_zero, zero_mul])
  have hFinal : Tendsto (fun n => 2 * (∑ i, ∫ x, conj (L n i x) * P₀ n i x).im +
      2 * (∑ i, ∫ x in V, conj (L n i x) * M₀ n i x).im) atTop (𝓝 0) := by
    simpa only [add_zero] using hPmain.add hLowerIm
  change Tendsto (fun n => 2 * (∫ x in U, ∑ i, conj (L n i x) * R₀ n i x).im) atTop (𝓝 0)
  exact hFinal.congr (fun n => by rw [hSum, Complex.add_im, mul_add])

end Burnett.V03
