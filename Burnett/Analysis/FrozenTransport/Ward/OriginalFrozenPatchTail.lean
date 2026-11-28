import Burnett.Analysis.FrozenTransport.Ward.OriginalCubicDecomposition

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.C02 Burnett.RicciSymbol Burnett.V06
open Burnett.Analysis.TransportWardSymbol Burnett.V10.OriginalGaugeCompatibility
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V11 (originalGaugePhysicalNumerator)
open scoped BigOperators ComplexConjugate ContDiff Topology

/-- Sum the actual Ward bounds on a single C03 patch family and refinement.
The real and complex summands all use the raw field `Z j (σ n)`, the same
frozen metric and test, and the same thin field and infrared symbol. -/
theorem eventually_originalFrozenWardPatchSum_bound
    (s : Finset LatticeIndex) (σ : ℕ → ℕ) (ℓ W : ℝ) (hℓ : 0 < ℓ)
    (G : E → Mat) (a : Joint → ℝ) (Z : LatticeIndex → ℕ → ProjectionSchwartzMatrix)
    (ϑ : ℝ → ℝ) (κ δ d wi wo ci co phaseWindow : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hd : 0 < d) (hci : 0 ≤ ci) (hcio : ci < co)
    (hThin : co * (d * κ * δ^2) ≤ phaseWindow)
    (D : ℝ) (hD : 0 ≤ D)
    (Cnear ν Creplacement Cphase α Ccorrection : ℝ)
    (hCnear : 0 ≤ Cnear) (hCreplacement : 0 ≤ Creplacement) :
    let x₀ (j : s) := patchCenter ℓ j
    let γ (j : s) := G (x₀ j)
    let aj (j : s) (ξ : E) := a (x₀ j, ξ)
    let m (j : s) := inverseMatrix (γ j)
    let η := d * κ * δ^2
    let hη : 0 < η := mul_pos (mul_pos hd hκ) (pow_pos hδ _)
    let mass (j : s) := ((volume : Measure E) (closedBall (x₀ j) (6 * ℓ))).toReal
    ∀ (hVolume : (∑ j : s, mass j) ≤ W)
      (hG : ∀ j : s, IsUnit (γ j)) (hSym : ∀ j : s, IsSymmetricTensor (γ j))
      (frame : ∀ j : s, TensorFrame.LorentzFrame (m j))
      (ha : ∀ j : s, ContDiffOn ℝ ∞ (aj j) {ξ | ξ ≠ 0})
      (hOdd : ∀ (j : s) ξ, aj j (-ξ) = -aj j ξ)
      (hHom : ∀ (j : s) (t : ℝ), 0 < t → ∀ ξ, aj j (t • ξ) = t * aj j ξ)
      (hJets : ∀ (j : s) (k : ℕ), k ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ k (aj j) ξ‖ ≤ D)
      (hm : ∀ j : s, WideScreenFrequencySmooth wi wo (m j))
      (hWindow : ∀ (j : s) (e : Covector), e ⬝ᵥ e = 1 → |symbolNorm (m j) e| < phaseWindow →
        screenSecondDirection (m j) e ≠ 0 ∧ IsUnit (screenMetricExtension (m j) (screenDirectionProjection (m j) e)).det)
      (hZsym : ∀ (j : s) (n : ℕ) i k, Z j (σ n) i k = Z j (σ n) k i)
      (hZreal : ∀ (j : s) (n : ℕ) i k x, conj (Z j (σ n) i k x) = Z j (σ n) i k x),
    let z (j : s) (n : ℕ) := Z j (σ n)
    let β (j : s) := fixedInfraredSymbol wardFixedTestCutoff 0 (aj j)
    let E₀ (j : s) := completeCubicEnergy (frozenActionCubicLinear (γ j)) (frozenActionCubicQuadratic (γ j)) (β j)
    let raw (j : s) (n : ℕ) : RealEnergyField OrderedPair := ⟨fun k => z j n k.1 k.2, fun k => hZreal j n k.1 k.2⟩
    let thin (j : s) (n : ℕ) := originalCubicThinScreen (m j) wi wo (hm j) hη ci co (z j n) (hZreal j n) +
      originalCubicGauge (z j n) (hZreal j n)
    let H (j : s) (n : ℕ) := wardActualThinSpectrum (m j) wi wo (hm j) hη ci co (z j n)
    let near (j : s) (n : ℕ) : ℂ := ((tau^8)⁻¹ : ℝ) • ∫ x,
      (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) * wardCyclicCubicWeight (γ j) (aj j) (H j n) (H j n) (H j n) x
    let far (j : s) (n : ℕ) := originalFarPatchFourierWeight (γ j) (aj j) ϑ κ δ wi wo (hm j) hη ci co (z j n)
    let gauge (j : s) (n : ℕ) := originalGaugePhysicalNumerator ϑ κ (γ j) (aj j)
      (thinScreenAngular (m j) wi wo (hm j) hη ci co).matrix (z j n)
    let phase (j : s) (n : ℕ) := wardPhysicalPhaseRemainder ϑ κ (m j) (metricDensity (γ j)) (aj j)
      wi wo (hm j) hη ci co (z j n)
    let I (A : Joint → ℂ) := ((tau^8)⁻¹ : ℝ) • (∫ x, A x)
    let frozen (j : s) (n : ℕ) := E₀ j (raw j n)
    (∀ j : s, ∀ᶠ n in atTop, |(near j n).re| ≤ Cnear * δ^ν * mass j) →
    (∀ j : s, ∀ ε > 0, ∀ᶠ n in atTop,
      |frozen j n - E₀ j (thin j n)| ≤ Creplacement * ℓ^α * mass j + ε) →
    (∀ (j : s) (n : ℕ) (k : Fin 7), Integrable (wardActualTensorWeight (m j) (wardPhysicalPhaseSlots k)
      (wardPhysicalPhaseTensorSymbol ϑ κ (m j) (metricDensity (γ j)) (aj j) k) wi wo (hm j) hη ci co (z j n))) →
    (∀ ε > 0, ∀ᶠ n in atTop, (∑ j : s, ‖phase j n‖) ≤ Cphase * ℓ^α * W + ε) →
    (∀ ε > 0, ∀ᶠ n in atTop, (∀ j : s, Integrable (far j n) ∧ Integrable (gauge j n)) ∧
      (∑ j : s, (‖I (far j n)‖ + ‖I (gauge j n)‖)) ≤ Ccorrection * ℓ * W + ε) →
    ∀ ε > 0, ∀ᶠ n in atTop, (∑ j : s, |frozen j n|) ≤
      (Cnear * δ^ν + (Creplacement + Cphase) * ℓ^α + 3 * Ccorrection * ℓ) * W + ε := by
  classical
  intro x₀ γ aj m η hη mass hVolume hG hSym frame ha hOdd hHom hJets hm hWindow hZsym hZreal
    z β E₀ raw thin H near far gauge phase I frozen hNear hReplace hSeven hPhase hCorrection ε hε
  let count : ℝ := Fintype.card s
  let t := ε / (count + 4)
  have hDen : 0 < count + 4 := by dsimp only [count]; positivity
  have ht : 0 < t := div_pos hε hDen
  have htSum : count * t + t + 3 * t = ε := by
    calc
      _ = t * (count + 4) := by ring
      _ = ε := div_mul_cancel₀ ε hDen.ne'
  filter_upwards [eventually_all.2 hNear, eventually_all.2 (fun j => hReplace j t ht),
    hPhase t ht, hCorrection t ht] with n hN hR hP hC
  have hEntry (j : s) : |frozen j n| ≤
      (Cnear * δ^ν + Creplacement * ℓ^α) * mass j + t +
        ‖phase j n‖ + 3 * (‖I (far j n)‖ + ‖I (gauge j n)‖) := by
    have hExact : frozen j n = (near j n).re + (frozen j n - E₀ j (thin j n)) + (phase j n).re +
        (3 * (I (far j n)).re + 3 * (I (gauge j n)).re) :=
      originalRawFrozenCubic_eq_thinReplacement_add_Ward (γ j) (hG j) (hSym j) (frame j) (aj j)
        (ha j) (hOdd j) (hHom j) D hD (hJets j) ϑ κ δ wi wo (hm j) hη ci co phaseWindow
        hci hcio hThin (hWindow j) (z j n) (hZsym j n) (hZreal j n) (hC.1 j).1 (hC.1 j).2 (hSeven j n)
    let A := (near j n).re
    let R := frozen j n - E₀ j (thin j n)
    let P := (phase j n).re
    let F := 3 * (I (far j n)).re
    let Gc := 3 * (I (gauge j n)).re
    change frozen j n = A + R + P + (F + Gc) at hExact
    have hF : |F| ≤ 3 * ‖I (far j n)‖ := by
      change |3 * (I (far j n)).re| ≤ _
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    have hG' : |Gc| ≤ 3 * ‖I (gauge j n)‖ := by
      change |3 * (I (gauge j n)).re| ≤ _
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    calc
      _ = |A + R + P + (F + Gc)| := congrArg abs hExact
      _ ≤ |A| + |R| + |P| + (|F| + |Gc|) :=
        (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)) (abs_add_le _ _))
      _ ≤ _ := by
        have hA : |A| ≤ _ := hN j
        have hB : |R| ≤ _ := hR j
        have hQ : |P| ≤ ‖phase j n‖ := Complex.abs_re_le_norm _
        rw [add_mul, mul_add]
        linarith
  have hCoeff : 0 ≤ Cnear * δ^ν + Creplacement * ℓ^α := by positivity
  calc
    _ ≤ ∑ j : s, ((Cnear * δ^ν + Creplacement * ℓ^α) * mass j + t +
        ‖phase j n‖ + 3 * (‖I (far j n)‖ + ‖I (gauge j n)‖)) := Finset.sum_le_sum (fun j _ => hEntry j)
    _ = (Cnear * δ^ν + Creplacement * ℓ^α) * (∑ j : s, mass j) + count * t +
        (∑ j : s, ‖phase j n‖) + 3 * (∑ j : s, (‖I (far j n)‖ + ‖I (gauge j n)‖)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, count]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (Cnear * δ^ν + Creplacement * ℓ^α) * W + count * t +
        (Cphase * ℓ^α * W + t) + 3 * (Ccorrection * ℓ * W + t) :=
      add_le_add (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left hVolume hCoeff) _) hP)
        (mul_le_mul_of_nonneg_left hC.2 (by norm_num))
    _ = (Cnear * δ^ν + (Creplacement + Cphase) * ℓ^α + 3 * Ccorrection * ℓ) * W +
        (count * t + t + 3 * t) := by ring
    _ = _ := by rw [htSum]

end Burnett.V03
