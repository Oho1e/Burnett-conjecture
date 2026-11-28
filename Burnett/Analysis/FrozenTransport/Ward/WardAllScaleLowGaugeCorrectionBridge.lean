import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 18000000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (quadratic lowSlotWeight)
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix projectionFullSchwartz
  projectionFullSchwartz_radianFourier regularizedComplexGaugeProjection gaugeProjectionInfrared
  gaugeProjectionInfrared_zero gaugeProjectionInfrared_one)
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector)
open Burnett.V08 (lowGaugeHighMatrix lowGaugeHighDifference lowGaugeTransportCoefficient frozenWavePhase
  originalLowGaugePotential signedCyclicPhase)
open scoped Matrix ComplexConjugate

open private radianFourier_real_reflection from Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection
open private raisedWardScreenEntry from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

private abbrev GaugeRealMatrix := Matrix OrderedPair OrderedPair ℝ

private theorem wardGaugeCompressed_mulVec (C : GaugeRealMatrix) (S : E → GaugeRealMatrix)
    (p q : E) (U V : OrderedPair → ℂ) :
    (∑ i, ∑ j, (lowGaugeHighMatrix C S p q i j : ℂ) * U j * V i) =
      ((S (p+q)).map Complex.ofReal *ᵥ V) ⬝ᵥ
        (C.map Complex.ofReal *ᵥ ((S q).map Complex.ofReal *ᵥ U)) := by
  let R := (S (p+q)).map Complex.ofReal
  let M := C.map Complex.ofReal
  let P := (S q).map Complex.ofReal
  have hMap : (lowGaugeHighMatrix C S p q).map Complex.ofReal = Rᵀ * M * P := by
    unfold lowGaugeHighMatrix
    rw [show Complex.ofReal = ⇑Complex.ofRealHom from rfl,
      Matrix.map_mul (f := Complex.ofRealHom), Matrix.map_mul (f := Complex.ofRealHom), Matrix.transpose_map]
    rfl
  calc
    _ = V ⬝ᵥ ((lowGaugeHighMatrix C S p q).map Complex.ofReal *ᵥ U) := by
      simp only [dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [hMap, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, Matrix.transpose_transpose]

private def wardGaugeProjectionSpectrum (z : ProjectionSchwartzMatrix) (ξ : E) (j : OrderedPair) : ℂ :=
  radianFourier (projectionFullSchwartz z j.1 j.2) ξ

private theorem wardGaugeProjectionSpectrum_nestedInfrared (z : ProjectionSchwartzMatrix) (ξ : E) (j : OrderedPair) :
    (gaugeProjectionInfrared (2 * ‖ξ‖) : ℂ) * wardGaugeProjectionSpectrum z ξ j =
      wardGaugeProjectionSpectrum z ξ j := by
  by_cases hξ : ‖ξ‖ ≤ 1
  · unfold wardGaugeProjectionSpectrum
    rw [projectionFullSchwartz_radianFourier]
    simp only [regularizedComplexGaugeProjection, gaugeProjectionInfrared_zero hξ, Complex.ofReal_zero,
      zero_smul, Matrix.zero_apply, mul_zero]
  · rw [gaugeProjectionInfrared_one (show 2 ≤ 2 * ‖ξ‖ by linarith [lt_of_not_ge hξ]), Complex.ofReal_one, one_mul]

private theorem wardProjectedThin_eq_mulVec (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (ξ : E) (j : OrderedPair) :
    (((thinScreenAngular m wi wo hm hη i o).matrix ξ).map Complex.ofReal *ᵥ
        wardGaugeProjectionSpectrum z ξ) j =
      wardActualThinSpectrum m wi wo hm hη i o z ξ j.1 j.2 := by
  exact (wardActualThinSpectrum_eq_sum m wi wo hm hη i o z ξ j).symm

private theorem wardFrozenWavePhase_eq (m : Tensor2) (ξ : E) :
    frozenWavePhase m ξ = quadratic m ξ := (quadratic_eq_symbolNorm m ξ).symm

private theorem wardQuadratic_even (m : Tensor2) (ξ : E) : quadratic m (-ξ) = quadratic m ξ := by
  simp only [quadratic_eq_symbolNorm, symbolNorm, PiLp.neg_apply, mul_neg, neg_mul, neg_neg]

private def wardQuarterTraceReversal (m : Tensor2) (i j : OrderedPair) : ℝ :=
  (m i.1 j.1 * m i.2 j.2 - m i.1 i.2 * m j.1 j.2 / 2) / 4

private theorem wardQuarterTraceReversal_action (m : Tensor2) (H : ComplexComponents) (i : OrderedPair) :
    (∑ j : OrderedPair, (wardQuarterTraceReversal m i j : ℂ) * H j.1 j.2) =
      physicalCoefficient m H i.1 i.2 := by
  simp only [physicalCoefficient, raiseBoth, complexRaiseSecond, complexMetricTrace,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [wardQuarterTraceReversal, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

private theorem wardGaugeHighPair_eq_screenPair
    (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix)
    (hz : ∀ a b x, conj (z a b x) = z a b x) (p q : E)
    (ht : complexMetricTrace m (wardActualThinSpectrum m wi wo hm hη i o z q) = 0) :
    let S := (thinScreenAngular m wi wo hm hη i o).matrix
    let U := wardGaugeProjectionSpectrum z
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    (∑ I, ∑ J, (lowGaugeHighMatrix (wardQuarterTraceReversal m) S p q I J : ℂ) *
      U q J * conj (U (q+p) I)) =
      frozenWardScreenPair m (H q) (H (-(p+q))) := by
  intro S U H
  let r := -(p+q)
  have hU (I : OrderedPair) : conj (U (q+p) I) = U r I := by
    rw [add_comm q p]
    exact (radianFourier_real_reflection _
      (projectionFullSchwartz_real_of_source z hz I) (p+q)).symm
  simp only [hU]
  rw [wardGaugeCompressed_mulVec]
  have hS : S (p+q) = S r := (thinScreenAngular_even m wi wo hm hη i o (p+q)).symm
  rw [hS]
  unfold dotProduct
  rw [wardFrozenScreenPair_eq_raised]
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun k : OrderedPair => (1 / 4 : ℂ) *
    (H r k.1 k.2 * raisedWardScreenEntry m (H q) k.1 k.2))]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (Matrix.map (S r) Complex.ofReal *ᵥ U r) j = H r j.1 j.2 from
    wardProjectedThin_eq_mulVec m wi wo hm hη i o z r j]
  have hCol : (Matrix.map (wardQuarterTraceReversal m) Complex.ofReal *ᵥ
       (Matrix.map (S q) Complex.ofReal *ᵥ U q)) j =
      physicalCoefficient m (H q) j.1 j.2 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    change (∑ k : OrderedPair, (wardQuarterTraceReversal m j k : ℂ) *
      (Matrix.map (S q) Complex.ofReal *ᵥ U q) k) = _
    simp_rw [show ∀ k : OrderedPair, (Matrix.map (S q) Complex.ofReal *ᵥ U q) k = H q k.1 k.2 from
      wardProjectedThin_eq_mulVec m wi wo hm hη i o z q]
    exact wardQuarterTraceReversal_action m (H q) j
  rw [hCol, physicalCoefficient, ht, mul_zero, zero_div, sub_zero, wardRaiseBoth_eq_orderedEntry]
  ring

/-- The low gauge Ward correction, including the original cyclic factor
minus i/3, is the ordered projected-patch numerator. Both nested high
infrared windows are retained on their own original Fourier inputs. -/
theorem wardActualLowGaugeTransport_eq_orderedNumerator (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) (p q : E)
    (ht : complexMetricTrace (inverseMatrix G)
      (wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z q) = 0) :
    let m := inverseMatrix G
    let r := -(p+q)
    let w := metricDensity G
    let S := (thinScreenAngular m wi wo hm hη i o).matrix
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let L := lowSlotWeight ϑ κ p q r
    let α := signedCyclicPhase a p q
    (-Complex.I / 3) * ((L : ℂ) * (α : ℂ) *
      (-(w : ℂ) * ((quadratic m r : ℂ) - (quadratic m q : ℂ)) *
        raisedWardGaugeDot m (originalLowGaugePotential z p) (q-r) * frozenWardScreenPair m (H q) (H r))) =
      ∑ I : OrderedPair, ∑ J : OrderedPair,
        ((L * gaugeProjectionInfrared (2 * ‖q‖) * gaugeProjectionInfrared (2 * ‖p+q‖) : ℝ) : ℂ) *
        lowGaugeTransportCoefficient m w a (originalLowGaugePotential z) (wardQuarterTraceReversal m) S p q I J *
        radianFourier (projectionFullSchwartz z J.1 J.2) q *
        conj (radianFourier (projectionFullSchwartz z I.1 I.2) (q+p)) := by
  intro m r w S H L α
  let U := wardGaugeProjectionSpectrum z
  let M := lowGaugeHighMatrix (wardQuarterTraceReversal m) S p q
  let v := originalLowGaugePotential z p
  let D := (quadratic m r : ℂ) - (quadratic m q : ℂ)
  let V := raisedWardGaugeDot m v (q-r)
  have hV : lowGaugeHighDifference m v p q = V := by
    unfold V r raisedWardGaugeDot lowGaugeHighDifference
    rw [sub_neg_eq_add]
  have hD : ((frozenWavePhase m (p+q) - frozenWavePhase m q : ℝ) : ℂ) = D := by
    simp only [D, r, Complex.ofReal_sub, wardFrozenWavePhase_eq, wardQuadratic_even]
  have hIR (I J : OrderedPair) :
      ((gaugeProjectionInfrared (2 * ‖q‖) * gaugeProjectionInfrared (2 * ‖p+q‖) : ℝ) : ℂ) *
        (U q J * conj (U (q+p) I)) = U q J * conj (U (q+p) I) := by
    have ha : (gaugeProjectionInfrared (2 * ‖q‖) : ℂ) * U q J = U q J :=
      wardGaugeProjectionSpectrum_nestedInfrared z q J
    have hb : (gaugeProjectionInfrared (2 * ‖p+q‖) : ℂ) * conj (U (q+p) I) = conj (U (q+p) I) := by
      have hv := congrArg conj (wardGaugeProjectionSpectrum_nestedInfrared z (q+p) I)
      have hnorm : ‖q+p‖ = ‖p+q‖ := congrArg norm (add_comm q p)
      simpa only [map_mul, Complex.conj_ofReal, hnorm] using hv
    rw [Complex.ofReal_mul, mul_mul_mul_comm, ha, hb]
  have hOne (I J : OrderedPair) :
      ((L * gaugeProjectionInfrared (2 * ‖q‖) * gaugeProjectionInfrared (2 * ‖p+q‖) : ℝ) : ℂ) *
        lowGaugeTransportCoefficient m w a (originalLowGaugePotential z) (wardQuarterTraceReversal m) S p q I J *
        U q J * conj (U (q+p) I) =
      (Complex.I / 3 * (L : ℂ) * (α : ℂ) * (w : ℂ) * D * V) *
        ((M I J : ℂ) * U q J * conj (U (q+p) I)) := by
    have hCoeff : lowGaugeTransportCoefficient m w a (originalLowGaugePotential z) (wardQuarterTraceReversal m)
        S p q I J = Complex.I * ((w / 3 : ℝ) : ℂ) * (α : ℂ) * D * V * (M I J : ℂ) := by
      unfold lowGaugeTransportCoefficient
      change Complex.I * ((w / 3 : ℝ) : ℂ) * (α : ℂ) *
        ((frozenWavePhase m (p+q) - frozenWavePhase m q : ℝ) : ℂ) *
        lowGaugeHighDifference m v p q * (M I J : ℂ) = _
      rw [hD, hV]
    rw [hCoeff]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
    have h := hIR I J
    rw [Complex.ofReal_mul] at h
    linear_combination (Complex.I / 3 * (L : ℂ) * (α : ℂ) * (w : ℂ) * D * V * (M I J : ℂ)) * h
  change _ = ∑ I, ∑ J, _ * _ * U q J * conj (U (q+p) I)
  simp only [hOne, ← Finset.mul_sum]
  rw [wardGaugeHighPair_eq_screenPair m wi wo hm hη i o z hz p q ht]
  change (-Complex.I / 3) * ((L : ℂ) * (α : ℂ) * (-(w : ℂ) * D * V * frozenWardScreenPair m (H q) (H r))) = _
  ring

end Burnett.C02
