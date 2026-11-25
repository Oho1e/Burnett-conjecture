import Burnett.Analysis.FrozenTransport.LinearInputsForCubicPatch
import Burnett.Analysis.FrozenTransport.FixedInfraredCubicPatchReplacement

set_option autoImplicit false
set_option maxRecDepth 5300
set_option maxHeartbeats 8200000
noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.Analysis.TransportPatches
open Burnett.A07 (coordinateDerivative)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz projectionFullSchwartz_coordinateDerivative
  projectionMatrixDerivative)
open Burnett.C03 (ProjectedPatchLpBounds projectedGaugeComplement)
open scoped ComplexConjugate ContDiff ENNReal Topology

/-- The complete cubic input uses the original real physical projection. -/
def originalCubicPhysical (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) :
    RealEnergyField OrderedPair :=
  ⟨fun k => projectionFullSchwartz z k.1 k.2, projectionFullSchwartz_real_of_source z hz⟩

/-- The same original infrared gauge complement is used on both sides. -/
def originalCubicGauge (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) :
    RealEnergyField OrderedPair :=
  ⟨fun k => projectedGaugeComplement z k.1 k.2, projectedGaugeComplement_real_of_source z hz⟩

/-- The literal thin-screen output is the replacement real physical field. -/
def originalCubicThinScreen (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix)
    (hz : ∀ a b x, conj (z a b x) = z a b x) : RealEnergyField OrderedPair :=
  ⟨actualThinSchwartzField m wi wo hm hη i o z, actualThinSchwartzField_real m wi wo hm hη i o z hz⟩

theorem actualThinSchwartz_cubicGradientDifference (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) :
    let u (k : OrderedPair) := projectionFullSchwartz z k.1 k.2
    let v := actualThinSchwartzField m wi wo hm hη i o z
    let T := actualThinScreenMultiplier m wi wo hm hη i o
    euclideanFieldGradientL3 (u - v) =
      (eLpNorm (orderedGradientValue (fun a : Index × OrderedPair =>
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier z a.1 a.2 -
        multiplierCoordinateDerivative T z a.1 a.2)) 3 volume).toReal := by
  intro u v T
  apply euclideanFieldGradientL3_of_orderedDerivative
  intro a
  have hU : (coordinateDerivative a.1 (u a.2)).toLp 2 volume =
      multiplierCoordinateDerivative originalProjectedMatrixMultiplier z a.1 a.2 := by
    rw [originalProjectedMatrixMultiplier_derivative_eq_schwartz, projectionFullSchwartz_coordinateDerivative]
    rfl
  have hV : (coordinateDerivative a.1 (v a.2)).toLp 2 volume =
      multiplierCoordinateDerivative T z a.1 a.2 :=
    actualThinSchwartzField_coordinateDerivative m wi wo hm hη i o z a.1 a.2
  change SchwartzMap.toLpCLM ℂ ℂ 2 volume (coordinateDerivative a.1 (u a.2 - v a.2)) = _
  rw [map_sub, map_sub, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, hU, hV]

/-- Apply the complete A02 cubic energy to the three actual original patch
fields. For each fixed (\ell), the (n)-tail follows from the C02 thin-screen
estimate and the C03 value and derivative bounds on the same patch. -/
theorem exists_completeCubic_actualThinReplacement
    (c : EnergyIndex OrderedPair → OrderedPair → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → OrderedPair → OrderedPair → OrderedPair → ℝ) (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (hz : ∀ n a b x, conj (z n a b x) = z n a b x)
        (P : Set E) (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ grad → 0 ≤ Ce → 0 ≤ ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
      let T := actualThinScreenMultiplier m wi wo hm hη i o
      let diff (n : ℕ) (a : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) a.1 a.2 -
          multiplierCoordinateDerivative T (z n) a.1 a.2
      let mass := ((volume : Measure E) P).toReal
      (∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * mass ^ (1 / 3 : ℝ) + ε) →
      let u (n : ℕ) := originalCubicPhysical (z n) (hz n)
      let v (n : ℕ) := originalCubicThinScreen m wi wo hm hη i o (z n) (hz n)
      let G (n : ℕ) := originalCubicGauge (z n) (hz n)
      ∀ ε > 0, ∀ᶠ n in atTop,
        |completeCubicEnergy c q (fixedInfraredSymbol cut add b) (u n + G n) -
          completeCubicEnergy c q (fixedInfraredSymbol cut add b) (v n + G n)| ≤
          (C * (D + 1) * Ce * (4 * (64 * grad) + Ce)^2) * ell ^ alpha * mass + ε := by
  obtain ⟨C, hC, hEnergy⟩ := exists_completeCubic_patch_replacement c hc q cut add hcut hadd
  refine ⟨C, hC, ?_⟩
  intro b hb hom D hD jet m wi wo hm η hη i o z hz P value grad Ce ell alpha
    hg hCe hEll hEll1 hAlpha hValue hSource T diff mass hDiff u v G
  let u₀ (n : ℕ) (k : OrderedPair) := projectionFullSchwartz (z n) k.1 k.2
  let v₀ (n : ℕ) := actualThinSchwartzField m wi wo hm hη i o (z n)
  let G₀ (n : ℕ) (k : OrderedPair) := projectedGaugeComplement (z n) k.1 k.2
  have hGradDiff : ∀ ε > 0, ∀ᶠ n in atTop,
      euclideanFieldGradientL3 (u₀ n - v₀ n) ≤ Ce * ell ^ alpha * mass ^ (1 / 3 : ℝ) + ε := by
    intro ε hε
    filter_upwards [hDiff ε hε] with n hn
    exact (actualThinSchwartz_cubicGradientDifference m wi wo hm hη i o (z n)).le.trans hn
  obtain ⟨hU, hV, hG, hGrad⟩ := actualLinearFields_C03_budget m wi wo hm hη i o
    z P value grad hValue hSource
  have hm₀ : 0 ≤ mass := ENNReal.toReal_nonneg
  have hM : 0 ≤ mass ^ (1 / 3 : ℝ) := Real.rpow_nonneg hm₀ _
  have hEllA : ell ^ alpha ≤ 1 := Real.rpow_le_one hEll hEll1 hAlpha
  have hW := cubicPatch_W13_budgets u₀ v₀ G₀ (64 * grad) Ce (ell ^ alpha) (mass ^ (1 / 3 : ℝ))
    hCe hEllA hM hU hV hG hGrad hGradDiff
  apply hEnergy b hb hom D hD jet u v G Ce (4 * (64 * grad) + Ce) ell alpha mass hCe (by positivity) hEll hm₀
  · intro ε hε
    exact (hW ε hε).mono (fun _ h => h.1)
  · intro ε hε
    exact (hW ε hε).mono (fun _ h => h.2)

end Burnett.C02
