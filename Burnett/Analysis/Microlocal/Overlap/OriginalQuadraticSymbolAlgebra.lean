import Burnett.Algebra.PhysicalQuotient
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingPhysicalCovariance
import Burnett.Analysis.Microlocal.Overlap.FactoredPhysicalJetDensity
import Burnett.Analysis.Microlocal.RicciDensityNullMoment

/-! The full pointwise quadratic algebra of the paper in an actual metric fiber. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.F06

open Burnett.RicciSymbol
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.PhysicalDensity
open Burnett.Microlocal.RawCovariance (rawJetProductCoefficient)
open scoped BigOperators ComplexConjugate ComplexOrder Matrix MatrixOrder

private theorem swap_raised_covector_pairing
    (G : Tensor2) (hG : IsSymmetricTensor G) (u v : Covector) :
    (∑ a, u a * raiseCovector G v a) = ∑ a, raiseCovector G u a * v a := by
  simp only [raiseCovector, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hG b a]
  ring

/-- The two connection products of a pure gauge tensor have the same
individual value, with the precise contraction of the gauge covector. -/
theorem pureGauge_two_connection_products
    (G : Tensor2) (hG : IsSymmetricTensor G) (ξ v : Covector) (b c : Index) :
    let C := connectionSymbol G ξ (pureGauge ξ v)
    let value := ξ b * ξ c * (∑ a, raiseCovector G ξ a * v a) ^ 2
    (∑ a, ∑ e, C a c e * C e b a) = value ∧
      (∑ a, ∑ e, C a a e * C e b c) = value := by
  dsimp only
  rw [← swap_raised_covector_pairing G hG ξ v]
  constructor <;>
    simp only [connectionSymbol_pureGauge, pow_two, Finset.mul_sum, Finset.sum_mul] <;>
    apply Finset.sum_congr rfl <;> intro a _ <;>
    apply Finset.sum_congr rfl <;> intro e _ <;> ring

/-- The real cross pairing with a gauge tensor before imposing the null
constraint. The indices on the contracted covector and frequency are raised
with the same inverse metric. -/
theorem physicalPairing_pureGauge_cross_formula
    (G : Tensor2) (hG : IsSymmetricTensor G) (ξ : Covector)
    (k : Tensor2) (hk : IsSymmetricTensor k) (v : Covector) :
    physicalPairing G k (pureGauge ξ v) =
      2 * (∑ a, raiseCovector G (contracted G ξ k) a * v a) -
      metricTrace G k * (∑ a, raiseCovector G ξ a * v a) := by
  rw [physicalPairing, tensorPairing_pureGauge G k ξ v hk, metricTrace_pureGauge G ξ v hG,
    swap_raised_covector_pairing G hG (contracted G ξ k) v,
    swap_raised_covector_pairing G hG ξ v]
  ring

/-- The normalized frame from the metric and frequency alone serves both
the real screen representative and the complete complex gauge quotient. -/
structure QuadraticNullScreen (G : Tensor2) (ξ : Covector) : Prop where
  normalized_screen :
    ∃ e : LorentzFrame G, TensorFrame.covector e.components ξ = NullScreen.nullCovector ∧
      (∀ k : Tensor2, IsSymmetricTensor k → (∀ i j, ricciSymbol G ξ k i j = 0) →
        let l := TensorFrame.tensor e.components k
        (l 0 0 + 2 * l 0 1 + l 1 1 = 0 ∧
          l 0 2 + l 1 2 = 0 ∧ l 0 3 + l 1 3 = 0 ∧ l 2 2 + l 3 3 = 0) ∧
        l = pureGauge NullScreen.nullCovector (NullScreen.gaugeVector l) +
          NullScreen.screenTensor (l 2 2) (l 2 3) ∧
        physicalPairing G k k = 2 * ((l 2 2) ^ 2 + (l 2 3) ^ 2)) ∧
      ∃ screen : ComplexTensor2 →ₗ[ℂ] ℂ × ℂ,
        (∀ k, screen k = NullNormalForm.screenCoordinates e.components k) ∧
        (∀ k l : ComplexTensor2, IsSymmetricComplexTensor k → IsSymmetricComplexTensor l →
          (∀ i j, complexRicciSymbol G ξ k i j = 0) →
          (∀ i j, complexRicciSymbol G ξ l i j = 0) →
          ((∃ v : ComplexCovector, k = l + complexPureGauge ξ v) ↔ screen k = screen l)) ∧
        (∀ u : ℂ × ℂ, ∃ k : ComplexTensor2, IsSymmetricComplexTensor k ∧
          (∀ i j, complexRicciSymbol G ξ k i j = 0) ∧ screen k = u) ∧
        ∀ k l : ComplexTensor2, IsSymmetricComplexTensor k → IsSymmetricComplexTensor l →
          (∀ i j, complexRicciSymbol G ξ k i j = 0) →
          (∀ i j, complexRicciSymbol G ξ l i j = 0) →
          hermitianPhysicalPairing G k l =
            2 * ((screen k).1 * conj (screen l).1 + (screen k).2 * conj (screen l).2)

/-- The complete real and Hermitian identities, gauge cancellation and
two-component physical form at the point. The covariance fields retain the
actual ordered jet contraction and the quarter normalization. -/
structure QuadraticSymbolAlgebra (G : Tensor2) (ξ : Covector) : Prop where
  trace :
    ∀ k : Tensor2, IsSymmetricTensor k → ∀ e : Index,
      (∑ a, connectionSymbol G ξ k a a e) = ξ e * metricTrace G k / 2
  first_connection_product :
    ∀ k : Tensor2, IsSymmetricTensor k → ∀ b c : Index,
      4 * (∑ a, ∑ e, connectionSymbol G ξ k a c e * connectionSymbol G ξ k e b a) =
        ξ b * ξ c * tensorPairing G k k +
        2 * contracted G ξ k b * contracted G ξ k c - 2 * symbolNorm G ξ * tensorSquare G k b c
  second_connection_product :
    ∀ k : Tensor2, IsSymmetricTensor k → ∀ b c : Index,
      4 * (∑ a, ∑ e, connectionSymbol G ξ k a a e * connectionSymbol G ξ k e b c) =
        metricTrace G k * (ξ b * contracted G ξ k c + ξ c * contracted G ξ k b -
          symbolNorm G ξ * k b c)
  expansion :
    ∀ k : Tensor2, IsSymmetricTensor k → ∀ b c : Index,
      4 * quadraticSymbol G ξ k b c =
        ξ b * ξ c * tensorPairing G k k +
        2 * contracted G ξ k b * contracted G ξ k c -
        2 * symbolNorm G ξ * tensorSquare G k b c -
        metricTrace G k * (ξ b * contracted G ξ k c + ξ c * contracted G ξ k b -
          symbolNorm G ξ * k b c)
  polarization :
    ∀ k l : Tensor2, ∀ b c : Index,
      mixedQuadraticSymbol G ξ k l b c =
        (quadraticSymbol G ξ (k + l) b c - quadraticSymbol G ξ k b c -
          quadraticSymbol G ξ l b c) / 2
  hermitian_polarization :
    ∀ k l : ComplexTensor2, ∀ b c : Index,
      (hermitianQuadraticSymbol G ξ k l b c).re =
        mixedQuadraticSymbol G ξ (tensorRe k) (tensorRe l) b c +
        mixedQuadraticSymbol G ξ (tensorIm k) (tensorIm l) b c ∧
      (hermitianQuadraticSymbol G ξ k l b c).im =
        mixedQuadraticSymbol G ξ (tensorIm k) (tensorRe l) b c -
        mixedQuadraticSymbol G ξ (tensorRe k) (tensorIm l) b c ∧
      hermitianQuadraticSymbol G ξ k l b c = conj (hermitianQuadraticSymbol G ξ l k b c)
  gauge_connection :
    ∀ (v : Covector) (a b c : Index),
      connectionSymbol G ξ (pureGauge ξ v) a b c = ξ b * ξ c * raiseCovector G v a
  gauge_products :
    ∀ (v : Covector) (b c : Index),
      let C := connectionSymbol G ξ (pureGauge ξ v)
      let value := ξ b * ξ c * (∑ a, raiseCovector G ξ a * v a) ^ 2
      (∑ a, ∑ e, C a c e * C e b a) = value ∧ (∑ a, ∑ e, C a a e * C e b c) = value
  noncharacteristic_gauge :
    symbolNorm G ξ ≠ 0 → ∀ k : Tensor2, (∀ i j, ricciSymbol G ξ k i j = 0) →
      k = pureGauge ξ (kernelGaugeVector G ξ k)
  noncharacteristic_real :
    symbolNorm G ξ ≠ 0 → ∀ k l : Tensor2, (∀ i j, ricciSymbol G ξ k i j = 0) →
      (∀ i j, ricciSymbol G ξ l i j = 0) → ∀ b c : Index,
      mixedQuadraticSymbol G ξ k l b c = 0
  noncharacteristic_hermitian :
    symbolNorm G ξ ≠ 0 → ∀ k l : ComplexTensor2, (∀ i j, complexRicciSymbol G ξ k i j = 0) →
      (∀ i j, complexRicciSymbol G ξ l i j = 0) → ∀ b c : Index,
      hermitianQuadraticSymbol G ξ k l b c = 0
  null_kernel :
    symbolNorm G ξ = 0 → ∀ k : Tensor2, (∀ i j, ricciSymbol G ξ k i j = 0) ↔
      ∀ b, contracted G ξ k b = metricTrace G k * ξ b / 2
  null_real :
    symbolNorm G ξ = 0 → ∀ k : Tensor2, IsSymmetricTensor k →
      (∀ i j, ricciSymbol G ξ k i j = 0) → ∀ b c : Index,
      quadraticSymbol G ξ k b c = ξ b * ξ c * physicalPairing G k k / 4
  null_hermitian :
    symbolNorm G ξ = 0 → ∀ k l : ComplexTensor2, IsSymmetricComplexTensor k →
      IsSymmetricComplexTensor l → (∀ i j, complexRicciSymbol G ξ k i j = 0) →
      (∀ i j, complexRicciSymbol G ξ l i j = 0) → ∀ b c : Index,
      hermitianQuadraticSymbol G ξ k l b c =
        (ξ b : ℂ) * ξ c * hermitianPhysicalPairing G k l / 4
  real_gauge_cross_formula :
    ∀ k : Tensor2, IsSymmetricTensor k → ∀ v : Covector,
      physicalPairing G k (pureGauge ξ v) =
        2 * (∑ a, raiseCovector G (contracted G ξ k) a * v a) -
        metricTrace G k * (∑ a, raiseCovector G ξ a * v a)
  null_real_gauge_cross :
    symbolNorm G ξ = 0 → ∀ k : Tensor2, IsSymmetricTensor k →
      (∀ i j, ricciSymbol G ξ k i j = 0) → ∀ v : Covector, physicalPairing G k (pureGauge ξ v) = 0
  null_hermitian_gauge_cross :
    symbolNorm G ξ = 0 → ∀ k : ComplexTensor2, IsSymmetricComplexTensor k →
      (∀ i j, complexRicciSymbol G ξ k i j = 0) → ∀ v : ComplexCovector,
      hermitianPhysicalPairing G k (complexPureGauge ξ v) = 0
  null_real_nonnegative :
    symbolNorm G ξ = 0 → ∀ k : Tensor2, IsSymmetricTensor k →
      (∀ i j, ricciSymbol G ξ k i j = 0) → 0 ≤ physicalPairing G k k
  null_screen : symbolNorm G ξ = 0 → QuadraticNullScreen G ξ
  null_covariance :
    symbolNorm G ξ = 0 → ∀ (A : Matrix Pair Pair ℂ), A.PosSemidef →
      (∀ v : Pair → ℂ, let k := tensorOfVector (A *ᵥ v)
        IsSymmetricComplexTensor k ∧ ∀ i j, complexRicciSymbol G ξ k i j = 0) →
      let weight := (1 / 4 : ℂ) * physicalContraction G A
      0 ≤ weight.re ∧ weight.im = 0
  covariance_moment :
    ∀ (A : Matrix Pair Pair ℂ) (N : Matrix JetSlot JetSlot ℂ), A.PosSemidef →
      (∀ i j : JetSlot, N i j = (ξ i.1 : ℂ) * (ξ j.1 : ℂ) * A j.2 i.2) →
      (∀ v : Pair → ℂ, let k := tensorOfVector (A *ᵥ v)
        IsSymmetricComplexTensor k ∧ ∀ i j, complexRicciSymbol G ξ k i j = 0) →
      ∀ b d : Index,
        (∑ i : JetSlot, ∑ j : JetSlot, rawJetProductCoefficient G b d i j * (N i j).re) =
          if symbolNorm G ξ = 0 then (ξ b * ξ d) * (((1 / 4 : ℂ) * physicalContraction G A).re)
          else 0

private theorem quadraticNullScreen
    (G : Tensor2) (base : LorentzFrame G) (ξ : Covector) (hξ : ξ ≠ 0)
    (hs : symbolNorm G ξ = 0) : QuadraticNullScreen G ξ := by
  let e := NullFrame.normalizedFrame G base ξ hξ hs
  have he := NullFrame.normalizedFrame_frequency G base ξ hξ hs
  let screen : ComplexTensor2 →ₗ[ℂ] ℂ × ℂ :=
    { toFun := NullNormalForm.screenCoordinates e.components
      map_add' := NullNormalForm.screenCoordinates_add e.components
      map_smul' := NullNormalForm.screenCoordinates_smul e.components }
  refine ⟨⟨e, he, ?_, screen, fun _ => rfl, ?_, ?_, ?_⟩⟩
  · intro k hkS hk
    let l := TensorFrame.tensor e.components k
    have hS := TensorFrame.tensor_symmetric e.components k hkS
    have hK := LorentzPhysical.transformed_null_kernel G e ξ k hξ hs hk
    rw [he] at hK
    exact ⟨NullScreen.kernel_constraints l hS hK, NullScreen.kernel_decomposition l hS hK,
      (LorentzPhysical.physicalPairing_eq_transformed G e k k).trans
        (NullScreen.physicalPairing_self_eq_screen l hS hK)⟩
  · intro k l hkS hlS hk hl
    exact NullNormalForm.same_screenCoordinates_iff_gauge G e ξ he k l hkS hlS hk hl
  · intro u
    exact NullNormalForm.screenCoordinates_surjective G e ξ he u.1 u.2
  · intro k l hkS hlS hk hl
    exact NullNormalForm.hermitianPhysicalPairing_eq_coordinates G e ξ he k l hkS hlS hk hl

/-- The algebra at a four-dimensional Lorentz metric, for every nonzero
covector in the chosen coordinate basis. -/
theorem fullQuadraticSymbolAlgebra_of_frame
    (G : Tensor2) (frame : LorentzFrame G) (ξ : Covector) (hξ : ξ ≠ 0) :
    QuadraticSymbolAlgebra G ξ := by
  have hG := LorentzPhysical.metric_symmetric G frame
  refine {
    trace := fun k hk => connectionSymbol_trace G ξ k hG hk
    first_connection_product := fun k hk => four_connectionSymbol_first_product G ξ k hG hk
    second_connection_product := fun k hk => four_connectionSymbol_second_product G ξ k hG hk
    expansion := fun k hk => four_quadraticSymbol_expansion G ξ k hG hk
    polarization := mixedQuadraticSymbol_polarization G ξ
    hermitian_polarization := fun k l b c =>
      ⟨hermitianQuadraticSymbol_re G ξ k l b c, hermitianQuadraticSymbol_im G ξ k l b c,
        hermitianQuadraticSymbol_conj_symm G ξ k l b c⟩
    gauge_connection := connectionSymbol_pureGauge G ξ
    gauge_products := pureGauge_two_connection_products G hG ξ
    noncharacteristic_gauge := fun hs k => kernel_eq_pureGauge G ξ k hs
    noncharacteristic_real := fun hs k l => mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel G ξ k l hs
    noncharacteristic_hermitian := fun hs k l =>
      hermitianQuadraticSymbol_eq_zero_of_noncharacteristic_kernel G ξ k l hs
    null_kernel := fun hs k => null_kernel_iff_contracted G ξ k hξ hs
    null_real := fun hs k hkS => quadraticSymbol_eq_physicalPairing_of_null_kernel G ξ k hG hkS hξ hs
    null_hermitian := fun hs k l hkS hlS =>
      hermitianQuadraticSymbol_eq_physicalPairing_of_null_kernel G ξ k l hG hkS hlS hξ hs
    real_gauge_cross_formula := physicalPairing_pureGauge_cross_formula G hG ξ
    null_real_gauge_cross := fun hs k hkS hk v =>
      physicalPairing_pureGauge_eq_zero_of_null_kernel G ξ k v hG hkS hξ hs hk
    null_hermitian_gauge_cross := fun hs k hkS hk v =>
      hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel G ξ k v hG hkS hξ hs hk
    null_real_nonnegative := fun hs k hkS => LorentzPhysical.physicalPairing_self_nonneg G frame ξ k hkS hξ hs
    null_screen := quadraticNullScreen G frame ξ hξ
    null_covariance := ?_
    covariance_moment := fun A N hA hFact hKer =>
      Burnett.Microlocal.RawCovariance.rawJetContraction_eq_nullMoment_of_factored
        G ξ A N hG hξ hA hFact hKer }
  intro hs A hA hK
  dsimp only
  obtain ⟨hRe, hIm⟩ := Burnett.Microlocal.Overlap.physicalContraction_of_null_amplitude
    G frame ξ hξ hs A hA hK
  have hQuarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hQuarter]
  exact ⟨by simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hRe,
    by simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hIm, mul_zero, zero_mul, add_zero]⟩

section ActualChart

open Module Burnett.Geometry Burnett.Microlocal.Overlap
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open IntrinsicScalarEinstein (covariantForm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open UnitCosphere (Cosphere projection)
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Paper lines 432–465, on the actual inverse metric of any receiving chart.
The geometric signature supplies the pointwise frame used by the algebra. -/
theorem originalQuadraticSymbolAlgebra
    (B : Field (M := M)) (c : AtlasChart M) (hSig : HasLorentzSignature B)
    (x : M) (hx : x ∈ c.chart.source) (ξ : Covector) (hξ : ξ ≠ 0) :
    QuadraticSymbolAlgebra (Burnett.P01.receivingBackgroundInverse B c x) ξ := by
  rw [Burnett.P01.receivingBackgroundInverse_in_fiber B c hSig.isSymmetric hSig.isNondegenerate x hx]
  obtain ⟨e, he⟩ := hSig x
  exact fullQuadraticSymbolAlgebra_of_frame _ (BasisFrame.lorentzFrame
    (covariantForm B x) (hSig.isNondegenerate x) (chartTangentBasis c x hx) e he) ξ hξ

/-- The same algebra on the original receiving-chart covariance gives the
intrinsic quarter weight and its factored Ricci moment. -/
theorem originalQuadraticSymbolAlgebra_of_intrinsicAmplitude
    {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (hSig : HasLorentzSignature B) (J : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source)
    (hPos : ∀ b : Basis Index ℝ (TangentSpace Model (projection p)), (components b (J p)).PosSemidef)
    (hK : HasIntrinsicAmplitudeRicciKernel r B hSig.isNondegenerate J p) :
    let G := Burnett.P01.receivingBackgroundInverse B c (projection p)
    let ξ := atlasChartUnitCovector c p
    let A := atlasAmplitudeMatrix c J p
    let w := intrinsicPhysicalWeight B hSig.isNondegenerate J p
    QuadraticSymbolAlgebra G ξ ∧
    ((symbolNorm G ξ = 0) → (0 ≤ w ∧ (1 / 4 : ℂ) * physicalContraction G A = (w : ℂ))) ∧
    ∀ (N : Matrix JetSlot JetSlot ℂ)
      (_ : ∀ i j : JetSlot, N i j = (ξ i.1 : ℂ) * (ξ j.1 : ℂ) * A j.2 i.2)
      (b d : Index),
      (∑ i : JetSlot, ∑ j : JetSlot, rawJetProductCoefficient G b d i j * (N i j).re) =
        if symbolNorm G ξ = 0 then (ξ b * ξ d) * w else 0 := by
  intro G ξ A w
  have hAlgebra : QuadraticSymbolAlgebra G ξ :=
    originalQuadraticSymbolAlgebra B c hSig (projection p) hp ξ (atlasChartUnitCovector_ne_zero c p hp)
  have hA : A.PosSemidef := by
    dsimp only [A]
    rw [atlasAmplitudeMatrix_of_mem c J p hp]
    exact hPos (chartTangentBasis c (projection p) hp)
  have hKer (v : Pair → ℂ) :
      let k := tensorOfVector (A *ᵥ v)
      IsSymmetricComplexTensor k ∧ ∀ i j, complexRicciSymbol G ξ k i j = 0 :=
    Burnett.P01.atlasAmplitudeMatrix_receiving_ricciKernel B c hSig.isSymmetric
      hSig.isNondegenerate J p hp hK v
  have hReal : (((1 / 4 : ℂ) * physicalContraction G A).re) = w := by
    have h := Burnett.P01.receivingQuarterDensity_eq_intrinsicPhysicalWeight B c hSig.isSymmetric
      hSig.isNondegenerate J p hp
    change (physicalContraction G (coordinateCovariance 1 A)).re / 4 = w at h
    rw [coordinateCovariance, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith
  refine ⟨hAlgebra, ?_, ?_⟩
  · intro hs
    obtain ⟨hWeight, hImag⟩ := hAlgebra.null_covariance hs A hA hKer
    exact ⟨hReal ▸ hWeight, Complex.ext (by simpa only [Complex.ofReal_re] using hReal)
      (by simpa only [Complex.ofReal_im] using hImag)⟩
  · intro N hFact b d
    rw [← hReal]
    exact hAlgebra.covariance_moment A N hA hFact hKer b d

end ActualChart

end Burnett.F06
