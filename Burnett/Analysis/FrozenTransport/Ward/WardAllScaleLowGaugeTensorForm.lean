import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

set_option autoImplicit false
set_option maxRecDepth 6700
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds projectedGaugeComplement)
open scoped ContDiff Topology

private abbrev WardOrderedTriple := OrderedPair × OrderedPair × OrderedPair

/-- The original two-frequency integral of the recombined tensor weight. -/
def wardLowGaugeMiddleTensorForm (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) : ℂ :=
  (tau^8)⁻¹ • (∫ x, wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z x)

theorem wardLowGaugeMiddleTensorForm_eq_sum (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    let V := actualThinSchwartzField m wi wo hm hη i o z
    let G (b : OrderedPair) := projectedGaugeComplement z b.1 b.2
    let F (s : WardOrderedTriple) := wardLowGaugeMiddleSymbol ϑ κ m w a (wardTensorBasis s.1)
      (wardTensorBasis s.2.1) (wardTensorBasis s.2.2)
    Integrable (wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z) ∧
      wardLowGaugeMiddleTensorForm ϑ κ m w a wi wo hm hη i o z =
        ∑ s : WardOrderedTriple, radianTrilinearForm (F s) (G s.1) (V s.2.1) (V s.2.2) := by
  intro V G F
  let W (s : WardOrderedTriple) := radianTrilinearWeight (F s) (G s.1) (V s.2.1) (V s.2.2)
  have hInt (s : WardOrderedTriple) : Integrable (W s) := by
    obtain ⟨_,_,h⟩ := exists_actualWardLowGaugeMiddleComponent_bound ϑ hϑ hCut κ hκ hSmall m w a ha hOdd hHom
      s.1 s.2.1 s.2.2
    exact (h wi wo hm η hη i o z).1
  have hW : wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z = fun x => ∑ s, W s x := by
    funext x
    simpa only [Fintype.sum_prod_type, W, F, G, V] using
      wardLowGaugeMiddleTensorWeight_eq_sum ϑ κ m w a wi wo hm hη i o z x
  refine ⟨hW.symm ▸ integrable_finset_sum Finset.univ (fun s _ => hInt s), ?_⟩
  change (tau^8)⁻¹ • (∫ x, wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z x) =
    ∑ s : WardOrderedTriple, (tau^8)⁻¹ • (∫ x, W s x)
  rw [hW, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun s _ => hInt s)]

/-- Finite ordered tensor assembly on the same fixed original C02 patch.
The absolute bound keeps the exact volume and the same original C03 source
and thin comparison rates as each component. -/
theorem exists_actualWardLowGaugeMiddleTensor_patch_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E)
        (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ grad → 0 ≤ Ce → 0 < ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
      let mass := ((volume : Measure E) P).toReal
      let M := mass ^ (1 / 3 : ℝ)
      let T := actualThinScreenMultiplier m wi wo hm hη i o
      let diff (n : ℕ) (b : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b.1 b.2 -
          multiplierCoordinateDerivative T (z n) b.1 b.2
      let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar m)
        (multiplierCoordinateDerivative T (z n) b.1 b.2)
      (∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε) →
      ∀ ε > 0, ∀ᶠ n in atTop, ‖wardLowGaugeMiddleTensorForm ϑ κ m w a wi wo hm hη i o (z n)‖ ≤
        (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  classical
  choose C hC hBound using fun s : WardOrderedTriple =>
    exists_actualWardLowGaugeMiddleComponent_patch_bound ϑ hϑ hCut κ hκ hSmall m w a ha hOdd hHom s.1 s.2.1 s.2.2
  refine ⟨∑ s, C s, Finset.sum_nonneg (fun s _ => hC s), ?_⟩
  intro wi wo hm η hη i o z P value grad Ce ell alpha hGrad hCe hEll hEll₁ hAlpha hv hSource mass M T diff phase hRate ε hε
  let V n := actualThinSchwartzField m wi wo hm hη i o (z n)
  let G (n : ℕ) (j : OrderedPair) := projectedGaugeComplement (z n) j.1 j.2
  let F (s : WardOrderedTriple) := wardLowGaugeMiddleSymbol ϑ κ m w a (wardTensorBasis s.1)
    (wardTensorBasis s.2.1) (wardTensorBasis s.2.2)
  let g := Ce * (128 * grad + Ce)^2 * ell ^ alpha * mass
  let K : ℝ := Fintype.card WardOrderedTriple
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  have hLocal : ∀ᶠ n in atTop, ∀ s : WardOrderedTriple,
      ‖radianTrilinearForm (F s) (G n s.1) (V n s.2.1) (V n s.2.2)‖ ≤ C s * g + ε / K := by
    rw [Filter.eventually_all]
    intro s
    simpa only [F, G, V, g, mul_assoc] using hBound s wi wo hm η hη i o z P value grad Ce ell alpha
      hGrad hCe hEll hEll₁ hAlpha hv hSource hRate (ε / K) (div_pos hε hK)
  filter_upwards [hLocal] with n hn
  rw [(wardLowGaugeMiddleTensorForm_eq_sum ϑ hϑ hCut κ hκ hSmall m w a ha hOdd hHom wi wo hm hη i o (z n)).2]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun s _ => hn s).trans_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have he : K * (ε / K) = ε := mul_div_cancel₀ _ hK.ne'
  change (∑ s, C s) * g + K * (ε / K) = _
  rw [he]
  simp only [g, mul_assoc]

end Burnett.C02
