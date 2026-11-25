import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalGaugePatchEnvelope
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeFullSource

set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option maxRecDepth 4600
noncomputable section
namespace Burnett.V11
open Set Matrix MeasureTheory Burnett.P01 Burnett.A07 Burnett.A08 Burnett.V08 Burnett.C02
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.V06 (ScreenMatrix)
open scoped ContDiff Matrix BigOperators ENNReal ComplexConjugate
open private integral_matrix_sum from Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeFullSource

def originalGaugePhysicalNumerator (θ : ℝ → ℝ) (κ : ℝ) (g : ScreenMatrix) (a : E → ℝ)
    (S : GaugeScreen) (z : ProjectionSchwartzMatrix) (x : Joint) : ℂ :=
  let m := inverseMatrix g
  let u := projectionFullSchwartz z
  ∑ I : TensorSlot, ∑ J : TensorSlot, (gaugeTriadCutoff θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ x.1 x.2 : ℂ)*
    lowGaugeTransportCoefficient m (metricDensity g) a (originalLowGaugePotential z) (gaugeFrozenContraction m) S x.1 x.2 I J *
    radianFourier (u J.1 J.2) x.2 * conj (radianFourier (u I.1 I.2) (x.2+x.1))

def gaugeMixedSourceEnergy (A : ProjectedSourceCoefficients) (d : Fin 4 → Fin 4 → SchwartzMap E ℝ)
    (T : TensorSlot → TensorSlot → (SchwartzMap E ℂ →ₗ[ℂ] FirstOrderLp 2)) (z : ProjectionSchwartzMatrix) : ℂ :=
  let u := projectionFullSchwartz z
  Complex.I * ∑ I : TensorSlot, ∑ J : TensorSlot,
      (inner ℂ (projectedSourceDivergenceL2 A u I.1 I.2) (T I J (u J.1 J.2)) -
      inner ℂ (T J I (u I.1 I.2)) (projectedSourceDivergenceL2 A u J.1 J.2) -
      weakDivergenceCommutatorPair d (T I J) (u J.1 J.2) (u I.1 I.2))

/-- Both appearances of the true wave source and every entry of the full
matrix energy equal the same original numerator integral. -/
theorem originalPatchSource_fullIdentity (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcut : ∀ t : ℝ, 1 ≤ t → θ t=0) (bound : ∀ t, |θ t|≤1) (κ : ℝ) (hκ : 0<κ) (hs : κ<1/16)
    (g : ScreenMatrix) (hg : gᵀ=g) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x≠0})
    (odd : ∀ ξ, a (-ξ) = -a ξ) (hom : ∀ t : ℝ, 0<t → ∀ ξ, a (t • ξ) = t*a ξ)
    (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0<η) (inn out : ℝ)
    (z : ProjectionSchwartzMatrix) (realZ : ∀ k l x, conj (z k l x)=z k l x) :
    let m := inverseMatrix g
    let S := (thinScreenAngular m i o hm hη inn out).matrix
    let E₀ := originalGaugePatchEnergy θ κ m (metricDensity g) a (gaugeFrozenContraction m) S z
    let N := originalGaugePhysicalNumerator θ κ g a S z
    Integrable N ∧ (tau^8)⁻¹ • ∫ x, N x = E₀ ∧
    ∃ T : TensorSlot → TensorSlot → (SchwartzMap E ℂ →ₗ[ℂ] FirstOrderLp 2),
      (∀ I J (u v : SchwartzMap E ℂ), inner ℂ (v.toLp 2 volume) (T I J u) =
        originalGaugeRadianPair θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m (metricDensity g) a (gaugeFrozenContraction m) S z I J u v ∧
        inner ℂ (v.toLp 2 volume) (T I J u)=inner ℂ (T J I v) (u.toLp 2 volume)) ∧
      ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (A : ProjectedSourceCoefficients),
      (∀ r s x, A.entry r s x=((m r s+d r s x : ℝ) : ℂ)) → gaugeMixedSourceEnergy A d T z=E₀ := by
  intro m S E₀ N
  let u := projectionFullSchwartz z
  let ct := gaugeCorrectionInfrared
  let C := gaugeFrozenContraction m
  let pair := originalGaugeRadianPair θ ct ct κ m (metricDensity g) a C S z
  let F (I J : TensorSlot) (x : Joint) := (gaugeTriadCutoff θ ct ct κ x.1 x.2 : ℂ)*
    lowGaugeTransportCoefficient m (metricDensity g) a (originalLowGaugePotential z) C S x.1 x.2 I J *
    radianFourier (u J.1 J.2) x.2 * conj (radianFourier (u I.1 I.2) (x.2+x.1))
  let val (I J : TensorSlot) := pair I J (u J.1 J.2) (constantWave m (u I.1 I.2))-pair I J (constantWave m (u J.1 J.2)) (u I.1 I.2)
  have one (I J : TensorSlot) : Integrable (F I J) ∧ (tau^8)⁻¹ • ∫ x, F I J x = Complex.I * val I J := by
    obtain ⟨meas,B,hB,order⟩ := originalScreenGauge_entry_control θ hθ.continuous.measurable hcut bound κ hκ hs g a ha odd hom i o hm hη inn out I J
    have p := originalGaugeRadianPair_eq_transportIntegral θ ct ct κ m (metricDensity g) a C S z I J B hB meas order (u J.1 J.2) (u I.1 I.2)
    exact ⟨p.1,p.2.symm⟩
  have r := integral_matrix_sum one
  have eq : (tau^8)⁻¹ • ∫ x, N x = E₀ := by simpa only [E₀,originalGaugePatchEnergy,Finset.mul_sum] using r.2
  refine ⟨r.1,eq,?_⟩
  obtain ⟨T,rep,sources⟩ := exists_originalScreenGauge_fullSource θ hθ hcut bound κ hκ hs g hg a ha odd hom i o hm hη inn out z realZ
  exact ⟨T,rep,fun d A hA => ((sources d A hA z z).2).symm.trans eq⟩

end Burnett.V11
