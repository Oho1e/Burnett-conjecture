import Burnett.Analysis.FrozenTransport.GaugeCorrection.LowGaugeAngularJetBounds
import Burnett.Analysis.CubicEnergy.AngularCorrection.RadianWavePhase
import Burnett.Analysis.AngularCaps.WedgeTriad

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V08

open Matrix MeasureTheory Burnett.P01 Burnett.A06 Burnett.A08
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight)
open scoped Matrix ComplexConjugate BigOperators

abbrev GaugeScreen := E → Matrix TensorSlot TensorSlot ℝ

/-- The signed third frequency is `-(p+q)`. Each of the two high frequencies keeps its own radial cutoff. -/
def gaugeTriadCutoff (θ hi ho : ℝ → ℝ) (κ : ℝ) (p q : E) : ℝ :=
  lowSlotWeight θ κ p q (-(p+q)) * hi ‖q‖ * ho ‖p+q‖

theorem gaugeTriadCutoff_swap (θ hi ho : ℝ → ℝ) (κ : ℝ) (p q : E) :
    gaugeTriadCutoff θ hi ho κ (-p) (p+q) = gaugeTriadCutoff θ ho hi κ p q := by
  simp only [gaugeTriadCutoff, lowSlotWeight, neg_add_cancel_left, norm_neg]
  rw [add_comm (‖p+q‖^2) (‖q‖^2)]
  ring

/-- The real elementary tensor for one ordered entry of the original low gauge spectrum. -/
def gaugeEntryBasis (k : TensorSlot) : ComplexComponents :=
  fun i j => if (i,j) = k then 1 else 0

def gaugeEntryPotential (G : ComplexComponents) (p : E) : ComplexCovector :=
  fun i => (‖p‖⁻¹ : ℝ) * normalizedGaugePotential (‖p‖⁻¹ • p) G i

private theorem gaugeEntryPotential_reflection (k : TensorSlot) (p : E) (i : Fin 4) :
    gaugeEntryPotential (gaugeEntryBasis k) (-p) i = -conj (gaugeEntryPotential (gaugeEntryBasis k) p i) := by
  have hReal : (fun a b => conj (gaugeEntryBasis k a b)) = gaugeEntryBasis k := by
    funext a b
    by_cases h : (a,b) = k <;> simp [gaugeEntryBasis, h]
  have hr := normalizedGaugePotential_reflection (‖p‖⁻¹ • p) (gaugeEntryBasis k) i
  rw [hReal] at hr
  simp only [gaugeEntryPotential, norm_neg, smul_neg, hr, map_mul, Complex.conj_ofReal, mul_neg]

/-- Raw scalar symbol multiplying the actual low gauge field in one ordered slot. -/
def gaugeRawEntry (θ hi ho : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen)
    (k i j : TensorSlot) (x : Joint) : ℂ :=
  (gaugeTriadCutoff θ hi ho κ x.1 x.2 : ℂ) *
    lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential (gaugeEntryBasis k)) C S x.1 x.2 i j

theorem gaugeRawEntry_highAdjoint (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (ha : ∀ ξ, a (-ξ) = -a ξ)
    (C : Matrix TensorSlot TensorSlot ℝ) (hC : Cᵀ = C) (S : GaugeScreen) (k i j : TensorSlot) :
    highAdjointSymbol (gaugeRawEntry θ hi ho κ m w a C S k i j) =
      gaugeRawEntry θ ho hi κ m w a C S k j i := by
  funext x
  change conj ((gaugeTriadCutoff θ hi ho κ (-x.1) (x.2+x.1) : ℂ) * _) = _
  change conj ((gaugeTriadCutoff θ hi ho κ (-x.1) (x.2+x.1) : ℂ) *
    lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential (gaugeEntryBasis k)) C S (-x.1) (x.2+x.1) i j) = _
  rw [add_comm x.2 x.1, gaugeTriadCutoff_swap, lowGaugeCorrectionCoefficient_hermitian m w a _ C hC S ha
    (gaugeEntryPotential_reflection k) x.1 x.2 j i, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  rfl

private theorem gaugeRadianPair_conj_low (b : Joint → ℂ) (z : ProjectionSchwartzMatrix)
    (hReal : ∀ i j x, conj (z i j x) = z i j x) (k : TensorSlot) (u w : E → ℂ) :
    let G := Burnett.C03.projectedGaugeComplement z k.1 k.2
    radianHighPair b (fun x => conj (G x)) u w = radianHighPair b G u w := by
  intro G
  unfold radianHighPair
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  have h := congrFun (congrFun (originalGaugeSpectrum_reflection z hReal (-x.1)) k.1) k.2
  have g := radianFourier_conj_neg (G : E → ℂ) (-x.1)
  rw [neg_neg] at h g
  have eq : radianFourier (fun t => conj (G t)) x.1 = radianFourier G x.1 := g.trans h.symm
  simp only [radianHighPairWeight, eq]

/-- One complete high matrix entry, linear in the sixteen actual low gauge fields. -/
def originalGaugeRadianPair (θ hi ho : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen)
    (z : ProjectionSchwartzMatrix) (i j : TensorSlot) (u v : E → ℂ) : ℂ :=
  ∑ k : TensorSlot, radianHighPair (gaugeRawEntry θ hi ho κ m w a C S k i j)
    (Burnett.C03.projectedGaugeComplement z k.1 k.2) u v

/-- The adjoint of the raw `(i,j)` entry is the transposed `(j,i)` entry, with both
high frequency cutoffs exchanged. The two high functions may differ. -/
theorem originalGaugeRadianPair_adjoint (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (ha : ∀ ξ, a (-ξ) = -a ξ)
    (C : Matrix TensorSlot TensorSlot ℝ) (hC : Cᵀ = C) (S : GaugeScreen)
    (z : ProjectionSchwartzMatrix) (hReal : ∀ i j x, conj (z i j x) = z i j x)
    (i j : TensorSlot) (u v : E → ℂ) :
    originalGaugeRadianPair θ ho hi κ m w a C S z j i v u =
      conj (originalGaugeRadianPair θ hi ho κ m w a C S z i j u v) := by
  simp only [originalGaugeRadianPair, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← gaugeRawEntry_highAdjoint θ hi ho κ m w a ha C hC S k i j,
    ← gaugeRadianPair_conj_low _ z hReal k v u, radianHighPair_highAdjoint]

end Burnett.V08
