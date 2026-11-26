import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeRadianPair

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.V08

open Matrix MeasureTheory Burnett.P01 Burnett.A06 Burnett.A08
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open scoped ContDiff Matrix ComplexConjugate BigOperators

private def tensorEval (i j : Fin 4) : ComplexComponents →ₗ[ℂ] ℂ where
  toFun G := G i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tensorEval_apply (i j : Fin 4) (G : ComplexComponents) : tensorEval i j G = G i j := rfl

private def potentialLinear (loDir : E) (k : Fin 4) : ComplexComponents →ₗ[ℂ] ℂ :=
  (∑ j, (loDir j : ℂ) • tensorEval k j) -
    ((loDir k : ℂ) / 2) • (∑ i, (loDir i : ℂ) • (∑ j, (loDir j : ℂ) • tensorEval i j))

private theorem potentialLinear_apply (loDir : E) (k : Fin 4) (G : ComplexComponents) :
    potentialLinear loDir k G = normalizedGaugePotential loDir G k := by
  simp only [potentialLinear, tensorEval_apply, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, normalizedGaugePotential_apply]
  simp only [mul_comm (G _ _) (↑(loDir _) : ℂ)]
  ring

private def gaugeCorrectionLinear (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (p q : E) (i j : TensorSlot) :
    ComplexComponents →ₗ[ℂ] ℂ :=
  (((w / 3 * signedCyclicPhase a p q : ℝ) : ℂ) * (lowGaugeHighMatrix C S p q i j : ℂ)) •
    ∑ t : Fin 4, ∑ l : Fin 4,
      ((m t l : ℂ) * ((q + (p+q)) t : ℂ) * (‖p‖⁻¹ : ℝ)) • potentialLinear (‖p‖⁻¹ • p) l

private theorem gaugeCorrectionLinear_apply (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (p q : E) (i j : TensorSlot)
    (G : ComplexComponents) :
    gaugeCorrectionLinear m w a C S p q i j G =
      lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential G) C S p q i j := by
  simp only [gaugeCorrectionLinear, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    potentialLinear_apply, lowGaugeCorrectionCoefficient, lowGaugeHighDifference, gaugeEntryPotential,
    mul_comm, mul_left_comm, mul_assoc]

private theorem component_expansion (G : ComplexComponents) :
    (∑ k : TensorSlot, G k.1 k.2 • gaugeEntryBasis k) = G := by
  ext i j
  simp [gaugeEntryBasis, Matrix.sum_apply, Matrix.smul_apply, mul_ite]

/-- The sixteen true low Fourier factors occur exactly once. Their sum is the
full cut-off coefficient of the original tensor, with no division by a low entry. -/
theorem sum_gaugeRawEntry_spectrum (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : GaugeScreen) (z : ProjectionSchwartzMatrix) (i j : TensorSlot) (p q : E) :
    (∑ k : TensorSlot, gaugeRawEntry θ hi ho κ m w a C S k i j (p,q) *
      radianFourier (Burnett.C03.projectedGaugeComplement z k.1 k.2) p) =
    (gaugeTriadCutoff θ hi ho κ p q : ℂ) *
      lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential z) C S p q i j := by
  let G := originalGaugeSpectrum z p
  let L := gaugeCorrectionLinear m w a C S p q i j
  let d : ℂ := gaugeTriadCutoff θ hi ho κ p q
  let entry (k : TensorSlot) := lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential (gaugeEntryBasis k)) C S p q i j
  have basisValue (k : TensorSlot) : L (gaugeEntryBasis k) = entry k :=
    gaugeCorrectionLinear_apply m w a C S p q i j (gaugeEntryBasis k)
  have fullValue : L G = lowGaugeCorrectionCoefficient m w a (originalLowGaugePotential z) C S p q i j := by
    refine (gaugeCorrectionLinear_apply m w a C S p q i j G).trans ?_
    unfold lowGaugeCorrectionCoefficient
    rw [show gaugeEntryPotential G p = originalLowGaugePotential z p from rfl]
  have hs := congrArg L (component_expansion G)
  change L (∑ k : TensorSlot, G k.1 k.2 • gaugeEntryBasis k) = L G at hs
  rw [map_sum] at hs
  simp only [map_smul, smul_eq_mul] at hs
  change (∑ k : TensorSlot, (d * entry k) * G k.1 k.2) = d * _
  calc
    _ = ∑ k : TensorSlot, d * (G k.1 k.2 * L (gaugeEntryBasis k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [basisValue]
      ac_rfl
    _ = d * L G := (Finset.mul_sum _ _ _).symm.trans (congrArg (d*·) hs)
    _ = _ := congrArg (d*·) fullValue

/-- The same reconstructed raw entry is the actual independent low-angle profile
times the high magnitude in the separated frequency region. -/
theorem sum_gaugeRawEntry_eq_angular_profile
    (θ hi ho : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ s : ℝ, 0 < s → ∀ ξ, a (s • ξ) = s * a ξ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen)
    (hS : ∀ s : ℝ, 0 < s → ∀ ξ, S (s • ξ) = S ξ)
    (z : ProjectionSchwartzMatrix) (i j : TensorSlot) (loDir ratio Θ : E)
    (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) (hloDir : ‖loDir‖ = 1) (hΘ : ‖Θ‖ = 1)
    (hRatio : ‖ratio‖ < 1/2) (hScale : ratio = (P/Q) • loDir) :
    let p := P • loDir
    let q := Q • Θ
    (∑ k : TensorSlot, gaugeRawEntry θ hi ho κ m w a C S k i j (p,q) *
      radianFourier (Burnett.C03.projectedGaugeComplement z k.1 k.2) p) =
      (gaugeTriadCutoff θ hi ho κ p q : ℂ) * ((Q : ℂ) *
        lowGaugeAngularExpansionProfile m w a (originalGaugeSpectrum z p) C S i j ((ratio,Θ),loDir)) := by
  intro p q
  rw [sum_gaugeRawEntry_spectrum, originalLowGaugeCorrection_eq_highMagnitude_profile z m w a ha hOdd hHom C S hS
    loDir ratio Θ P Q hP hQ hloDir hΘ hRatio hScale i j]
  simp only [p, lowGaugeAngularExpansionProfile, lowGaugeJointProfile, mul_assoc]

/-- The exact constant-wave commutator has the output-minus-input polynomial,
using the same frozen matrix and genuine high functions before and after `P₀`. -/
theorem originalGaugeRadianPair_constantWave (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : GaugeScreen) (z : ProjectionSchwartzMatrix) (i j : TensorSlot)
    (B : ℝ) (hB : 0 ≤ B)
    (hMeas : ∀ k, Measurable (gaugeRawEntry θ hi ho κ m w a C S k i j))
    (hOrder : ∀ k (x : Joint), ‖gaugeRawEntry θ hi ho κ m w a C S k i j x‖ ≤ B*(1+‖x.1‖+‖x.2‖))
    (u v : SchwartzMap E ℂ) :
    originalGaugeRadianPair θ hi ho κ m w a C S z i j u (constantWave m v) -
      originalGaugeRadianPair θ hi ho κ m w a C S z i j (constantWave m u) v =
      ∑ k : TensorSlot, radianHighPair (fun x => ((frozenWavePhase m (x.1+x.2) - frozenWavePhase m x.2 : ℝ) : ℂ) *
        gaugeRawEntry θ hi ho κ m w a C S k i j x) (Burnett.C03.projectedGaugeComplement z k.1 k.2) u v := by
  rw [originalGaugeRadianPair, originalGaugeRadianPair, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have h := radianHighPair_constantWave_commutator m (gaugeRawEntry θ hi ho κ m w a C S k i j)
    (hMeas k) B hB (hOrder k) (Burnett.C03.projectedGaugeComplement z k.1 k.2) u v
  rw [h]
  congr 1
  funext x
  rw [add_comm x.1 x.2]
  rfl

end Burnett.V08
