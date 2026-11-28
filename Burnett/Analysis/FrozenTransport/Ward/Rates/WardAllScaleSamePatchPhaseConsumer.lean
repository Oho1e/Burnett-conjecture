import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScalePhasePatchSum

set_option autoImplicit false
set_option maxRecDepth 7600
set_option maxHeartbeats 10500000

noncomputable section

namespace Burnett.C02

open Set Filter Metric MeasureTheory Burnett.RicciSymbol Burnett.Fourier Burnett.A02.FrequencySplit
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter)
open scoped ContDiff Topology

/-- The original finite C03 patch family consumes the paired C02 thin
gradient tails. The Ward phase error uses the same patch fields and the
same wide screen for the full family. -/
theorem exists_wardPhysicalPhase_originalPatchFamily
    (K V : Set E) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (m : E → Tensor2) (w : E → ℝ)
    (hm : ∀ a b, ContDiffOn ℝ ∞ (fun x => m x a b) V) (hw : ContDiffOn ℝ ∞ w V)
    (hSym : ∀ c ∈ K, IsSymmetricTensor (m c))
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ x ξ, a (x,-ξ) = -a (x,ξ))
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a (x,t • ξ) = t * a (x,ξ))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (wi wo : ℝ) (hs : ∀ x ∈ K, WideScreenFrequencySmooth wi wo (m x)) (η : ℝ) (hη : 0 < η)
      (i o : ℝ) (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ), ℓ ≤ 1 →
    let x₀ := patchCenter ℓ
    let P (j : LatticeIndex) := closedBall (x₀ j) (6 * ℓ)
    ∀ (hPatch : ∀ j ∈ s, P j ⊆ K)
      (Z : LatticeIndex → ℕ → ProjectionSchwartzMatrix)
      (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (Cp Ce α : ℝ),
      0 ≤ Cp → 0 ≤ Ce → 0 ≤ α →
    (∀ j ∈ s, ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (Z j n) (P j) (Cp * e n) (Cp * (1+e n/ℓ))) →
    (∀ (j : LatticeIndex) (hj : j ∈ s),
      let T := actualThinScreenMultiplier (m (x₀ j)) wi wo
        (hs (x₀ j) (hPatch j hj (mem_closedBall_self (by positivity)))) hη i o
      let diff (n : ℕ) (b : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (Z j n) b.1 b.2 -
          multiplierCoordinateDerivative T (Z j n) b.1 b.2
      let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar (m (x₀ j)))
        (multiplierCoordinateDerivative T (Z j n) b.1 b.2)
      let Vj := ((volume : Measure E) (P j)).toReal ^ (1 / 3 : ℝ)
      ∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ℓ ^ α * Vj + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ℓ ^ α * Vj + ε) →
    let Φ (j : LatticeIndex) (n : ℕ) := by
      classical
      exact if hc : x₀ j ∈ K then
        wardPhysicalPhaseRemainder ϑ κ (m (x₀ j)) (w (x₀ j)) (fun ξ => a (x₀ j,ξ))
          wi wo (hs (x₀ j) hc) hη i o (Z j n) else 0
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∑ j ∈ s, ‖Φ j n‖) ≤ (17 ^ 4 : ℝ) * (C * Ce * (128 * (2 * Cp) + Ce)^2) *
        ℓ ^ α * ((volume : Measure E) K).toReal + ε := by
  classical
  obtain ⟨C,hC,hClose⟩ := exists_wardPhysicalPhaseRemainder_compactPatchUniform K V hK hV hKV m w hm hw hSym
    a ha hOdd hHom ϑ hϑ hCut hFlat κ hκ hSmall
  refine ⟨C,hC,?_⟩
  intro wi wo hs η hη i o s ℓ hℓ hℓ₁ x₀ P hPatch Z e he Cp Ce α hCp hCe hα hRaw hGrad Φ
  have hE : Tendsto (fun n => Cp * e n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul he
  have hSmallE : ∀ᶠ n in atTop, e n ≤ ℓ := ((tendsto_order.1 he).2 ℓ hℓ).mono (fun _ hn => hn.le)
  have hC' : 0 ≤ C * Ce * (128 * (2 * Cp) + Ce)^2 :=
    mul_nonneg (mul_nonneg hC hCe) (sq_nonneg _)
  refine wardPhysicalPhase_sum_scaled_patch s ℓ hℓ K hK hPatch Φ _ α hC' ?_
  intro j hj ε hε
  have hx : x₀ j ∈ K := hPatch j hj (mem_closedBall_self (by positivity))
  have hSourceReal : ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (Z j n) (P j) (Cp * e n) (2 * Cp) := by
    filter_upwards [hRaw j hj, hSmallE] with n hb hn
    refine hb.mono le_rfl ?_
    calc
      Cp * (1 + e n/ℓ) ≤ Cp * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add_left ((div_le_one hℓ).mpr hn) 1) hCp
      _ = 2 * Cp := by ring
  have he' := hClose (x₀ j) hx wi wo (hs (x₀ j) hx) η hη i o (Z j) (P j)
    (fun n => Cp * e n) (2 * Cp) Ce ℓ α hCe hℓ hℓ₁ hα hE hSourceReal (hGrad j hj) ε hε
  change ∀ᶠ n in atTop, ‖Φ j n‖ ≤
    (C * Ce * (128 * (2 * Cp) + Ce)^2) * ℓ ^ α * ((volume : Measure E) (P j)).toReal + ε
  simpa only [Φ, dif_pos hx] using he'

end Burnett.C02
