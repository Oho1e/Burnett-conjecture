import Burnett.Analysis.TransportPatches.ActualThinScreenCombination
import Burnett.Analysis.FrozenTransport.FourierSchwartzTransportInputs

set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 7500000
noncomputable section

namespace Burnett.C02

open MeasureTheory Filter Metric Set Matrix Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E tau)
open Burnett.A07 (coordinateDerivative)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile_degreeZero weighted_iteratedFDeriv_le_of_unitSphere)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix principalGaugeProjectionMatrix gaugeProjectionInfrared
  gaugeProjectionInfrared_one gaugeProjectionSymbol gaugeProjectionSymbol_even gaugeProjectionSymbol_scale
  gaugeProjectionSymbol_contDiffOn projectionFullSchwartz)
open scoped BigOperators ComplexConjugate ContDiff Matrix Topology

open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols

private theorem homogeneousEnd_hasTemperateGrowth {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiffOn ℝ ∞ g {ξ | ξ ≠ 0})
    (hdeg : ∀ a : ℝ, a ≠ 0 → ∀ ξ, g (a • ξ) = g ξ)
    (R : ℝ) (hR : 1 ≤ R) (hEq : ∀ ξ, R ≤ ‖ξ‖ → f ξ = g ξ) : f.HasTemperateGrowth := by
  refine ⟨hf, fun n => ?_⟩
  have hn : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  let U : Set E := {ξ | ξ ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hCont : ContinuousOn (iteratedFDeriv ℝ n g) U :=
    (hg.continuousOn_iteratedFDerivWithin hn hU.uniqueDiffOn).congr
      (fun ξ hξ => (iteratedFDerivWithin_of_isOpen n hU hξ).symm)
  have hSphere : sphere (0 : E) 1 ⊆ U := by
    intro ξ hξ hZero
    simpa only [hZero, norm_zero, zero_ne_one] using mem_sphere_zero_iff_norm.mp hξ
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hCont.mono hSphere)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) (R + 1)).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv hn).continuousOn
  refine ⟨0, max B C, fun ξ => ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hξ : ‖ξ‖ ≤ R + 1
  · exact (hB ξ (mem_closedBall_zero_iff.mpr hξ)).trans (le_max_left _ _)
  · have hFar : R < ‖ξ‖ := (lt_add_of_pos_right _ zero_lt_one).trans (lt_of_not_ge hξ)
    have hNear : ∀ᶠ y in 𝓝 ξ, R < ‖y‖ :=
      (continuous_norm.tendsto ξ).eventually (Ioi_mem_nhds hFar)
    have hSame : f =ᶠ[𝓝 ξ] g := hNear.mono fun y hy => hEq y hy.le
    rw [(hSame.iteratedFDeriv ℝ n).eq_of_nhds]
    have hOne := hR.trans hFar.le
    have hNZ : ξ ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hOne)
    calc
      _ ≤ ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n g ξ‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hOne)
      _ ≤ C := weighted_iteratedFDeriv_le_of_unitSphere hg hdeg
        (fun y hy => hC y (mem_sphere_zero_iff_norm.mpr hy)) hNZ
      _ ≤ _ := le_max_right _ _

private def projectedAngularEntry (S : RealOrderedAngularMatrix) (k i : OrderedPair) (ξ : E) : ℝ :=
    ∑ j : OrderedPair, S.matrix ξ k j * gaugeProjectionSymbol j.1 j.2 i.1 i.2 ξ

private theorem projectedAngularEntry_cast (S : RealOrderedAngularMatrix) (k i : OrderedPair) (ξ : E) :
    S.afterOriginalProjection.principal ξ k i = (projectedAngularEntry S k i ξ : ℂ) := by
  simp only [RealOrderedAngularMatrix.afterOriginalProjection, Matrix.mul_apply, RealOrderedAngularMatrix.complex,
    principalGaugeProjectionMatrix, projectedAngularEntry, Complex.ofReal_sum, Complex.ofReal_mul]

private theorem afterOriginalProjection_full_cast (S : RealOrderedAngularMatrix) (k i : OrderedPair) (ξ : E) :
    S.afterOriginalProjection.full k i ξ =
      ((gaugeProjectionInfrared ‖tau • ξ‖ * projectedAngularEntry S k i ξ : ℝ) : ℂ) := by
  rw [S.afterOriginalProjection_full, projectedAngularEntry_cast, Complex.ofReal_mul]

theorem RealOrderedAngularMatrix.afterOriginalProjection_full_hasTemperateGrowth (S : RealOrderedAngularMatrix)
    (hEven : ∀ ξ, S.matrix (-ξ) = S.matrix ξ) (k i : OrderedPair) :
    Function.HasTemperateGrowth (S.afterOriginalProjection.full k i : E → ℂ) := by
  let T := S.afterOriginalProjection
  let f := fun ξ : E => (T.full k i ξ).re
  let g := projectedAngularEntry S k i
  have hf : ContDiff ℝ ∞ f := Complex.reCLM.contDiff.comp (T.full_smooth k i)
  have hg : ContDiffOn ℝ ∞ g {ξ | ξ ≠ 0} := by
    apply ContDiffOn.sum
    intro j _
    exact (S.smooth k j).mul (gaugeProjectionSymbol_contDiffOn _ _ _ _)
  have hPos (a : ℝ) (ha : 0 < a) (ξ : E) : g (a • ξ) = g ξ := by
    simp only [g, projectedAngularEntry, S.degree a ha ξ, gaugeProjectionSymbol_scale _ _ _ _ a ha]
  have hEvenG (ξ : E) : g (-ξ) = g ξ := by
    simp only [g, projectedAngularEntry, hEven, gaugeProjectionSymbol_even]
  have hDeg (a : ℝ) (ha : a ≠ 0) (ξ : E) : g (a • ξ) = g ξ := by
    rcases lt_or_gt_of_ne ha with h | h
    · rw [show a • ξ = -((-a) • ξ) by simp, hEvenG]
      exact hPos (-a) (neg_pos.mpr h) ξ
    · exact hPos a h ξ
  let R := max 1 (2 / tau)
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hHigh (ξ : E) (hξ : R ≤ ‖ξ‖) : f ξ = g ξ := by
    have hCut : (2 : ℝ) ≤ ‖tau • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg hτ.le, mul_comm]
      exact (div_le_iff₀ hτ).mp ((le_max_right _ _).trans hξ)
    simp only [f, T, afterOriginalProjection_full_cast, Complex.ofReal_re, gaugeProjectionInfrared_one hCut,
      one_mul, g]
  have hTemp := homogeneousEnd_hasTemperateGrowth hf hg hDeg R (le_max_left _ _) hHigh
  have hCast : (T.full k i : E → ℂ) = Complex.ofRealLI ∘ f := by
    funext ξ
    change S.afterOriginalProjection.full k i ξ = ((S.afterOriginalProjection.full k i ξ).re : ℂ)
    rw [afterOriginalProjection_full_cast, Complex.ofReal_re]
  rw [show S.afterOriginalProjection = T from rfl, hCast]
  refine ⟨Complex.ofRealCLM.contDiff.comp hf, fun n => ?_⟩
  obtain ⟨d, C, hC⟩ := hTemp.2 n
  refine ⟨d, C, fun ξ => ?_⟩
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
  exact hC ξ

theorem RealOrderedAngularMatrix.afterOriginalProjection_full_conj_neg (S : RealOrderedAngularMatrix)
    (hEven : ∀ ξ, S.matrix (-ξ) = S.matrix ξ) (k i : OrderedPair) (ξ : E) :
    conj (S.afterOriginalProjection.full k i ξ) = S.afterOriginalProjection.full k i (-ξ) := by
  simp only [afterOriginalProjection_full_cast, Complex.conj_ofReal, smul_neg, norm_neg, projectedAngularEntry,
    hEven, gaugeProjectionSymbol_even]

theorem thinScreenAngular_even (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ) (ξ : E) :
    (thinScreenAngular m wi wo hm hη i o).matrix (-ξ) = (thinScreenAngular m wi wo hm hη i o).matrix ξ := by
  have hC := thinConeProfile_degreeZero m η i o (-1) (neg_ne_zero.mpr one_ne_zero) ξ
  rw [neg_one_smul] at hC
  have hW : (wideScreenAngular wi wo m hm).matrix (-ξ) = (wideScreenAngular wi wo m hm).matrix ξ := by
    ext k j
    exact congrFun (congrFun (globalAngularScreenSymbol_even wi wo m (orderedBasis j) (fun t => ξ t)) k.1) k.2
  simp only [thinScreenAngular, hC, hW]

/-- The actual thin-screen output of the original source, as a Schwartz
field on all of coordinate space, for the complete physical cubic energy. -/
def actualThinSchwartzField (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) : OrderedPair → SchwartzMap E ℂ :=
  (actualThinScreenMultiplier m wi wo hm hη i o).schwartzOutput
    ((thinScreenAngular m wi wo hm hη i o).afterOriginalProjection_full_hasTemperateGrowth
      (thinScreenAngular_even m wi wo hm hη i o)) z

theorem actualThinSchwartzField_toLp (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (k : OrderedPair) :
    (actualThinSchwartzField m wi wo hm hη i o z k).toLp 2 volume =
      (actualThinScreenMultiplier m wi wo hm hη i o).output (fun j => (z j.1 j.2).toLp 2 volume) k :=
  ClassicalMatrixMultiplier.schwartzOutput_toLp _ _ _ _

theorem actualThinSchwartzField_coordinateDerivative (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (d : Index) (k : OrderedPair) :
    (coordinateDerivative d (actualThinSchwartzField m wi wo hm hη i o z k)).toLp 2 volume =
      multiplierCoordinateDerivative (actualThinScreenMultiplier m wi wo hm hη i o) z d k :=
  ClassicalMatrixMultiplier.schwartzOutput_coordinateDerivative _ _ _ _ _

theorem actualThinSchwartzField_real (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) (k : OrderedPair) (x : E) :
    conj (actualThinSchwartzField m wi wo hm hη i o z k x) = actualThinSchwartzField m wi wo hm hη i o z k x :=
  ClassicalMatrixMultiplier.schwartzOutput_real _ _
    ((thinScreenAngular m wi wo hm hη i o).afterOriginalProjection_full_conj_neg
      (thinScreenAngular_even m wi wo hm hη i o)) _ hz _ _

/-- Pointwise reality of the same P01 Schwartz projection used by C03. -/
theorem projectionFullSchwartz_real_of_source (z : ProjectionSchwartzMatrix)
    (hz : ∀ a b x, conj (z a b x) = z a b x) (k : OrderedPair) (x : E) :
    conj (projectionFullSchwartz z k.1 k.2 x) = projectionFullSchwartz z k.1 k.2 x := by
  let S := RealOrderedAngularMatrix.identity
  let hTemp := S.afterOriginalProjection_full_hasTemperateGrowth (fun _ => rfl)
  let u := S.afterOriginalProjection.schwartzOutput hTemp z k
  have hEq := S.afterOriginalProjection.schwartzOutput_toLp hTemp z k
  change u.toLp 2 volume =
    originalProjectedMatrixMultiplier.output (fun j => (z j.1 j.2).toLp 2 volume) k at hEq
  rw [originalProjectedMatrixMultiplier_output_eq_schwartz] at hEq
  let v := projectionFullSchwartz z k.1 k.2
  have hu := u.coeFn_toLp 2 volume
  rw [hEq] at hu
  have hPoint : (u : E → ℂ) = (v : E → ℂ) :=
    Measure.eq_of_ae_eq (hu.symm.trans (v.coeFn_toLp 2 volume)) u.continuous v.continuous
  have hReal := S.afterOriginalProjection.schwartzOutput_real hTemp
    (S.afterOriginalProjection_full_conj_neg (fun _ => rfl)) z hz k x
  change conj ((u : E → ℂ) x) = (u : E → ℂ) x at hReal
  simpa only [hPoint] using hReal

end Burnett.C02
