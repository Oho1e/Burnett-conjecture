import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformTensorPatch
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCubicActualGaugeAssembly
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorVertexLink
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhysicalPhaseRecombination
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleUniformTensorPatch

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 15300000

noncomputable section

namespace Burnett.C02

open Set Filter Matrix MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit Burnett.A05
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ComplexConjugate ContDiff Matrix Topology

open private wardActualTensorWeight_eq_originalSpectra from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorVertexLink
open private wardMiddleTensorTrilinear wardMiddleTensorTrilinear_apply from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleUniformTensorPatch

theorem exists_wardPhysicalPhaseRemainder_compactPatchUniform
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E), c ∈ K →
      ∀ (wi wo : ℝ) (hs : WideScreenFrequencySmooth wi wo (m c)) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E)
        (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ Ce → 0 < ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
      let mass := ((volume : Measure E) P).toReal
      let M := mass ^ (1 / 3 : ℝ)
      let T := actualThinScreenMultiplier (m c) wi wo hs hη i o
      let diff (n : ℕ) (b : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b.1 b.2 -
          multiplierCoordinateDerivative T (z n) b.1 b.2
      let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar (m c))
        (multiplierCoordinateDerivative T (z n) b.1 b.2)
      (∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε) →
      ∀ ε > 0, ∀ᶠ n in atTop,
        ‖wardPhysicalPhaseRemainder ϑ κ (m c) (w c) (fun ξ => a (c,ξ)) wi wo hs hη i o (z n)‖ ≤ (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  obtain ⟨C,hC,hBound⟩ := exists_wardPhysicalPhaseTensor_compactPatchUniform K V hK hV hKV m w hm hw hSym
    a ha hOdd hHom ϑ hϑ hCut hFlat κ hκ hSmall
  refine ⟨9 * C, mul_nonneg (by norm_num) hC,?_⟩
  intro c hc wi wo hs η hη i o z P value grad Ce ell alpha hCe hEll hEll₁ hAlpha hv hSource mass M T diff phase hRate
  let A (s : Fin 7) := wardPhysicalPhaseTensorSymbol ϑ κ (m c) (w c) (fun ξ => a (c,ξ)) s
  let F (n : ℕ) (s : Fin 7) := wardActualTensorForm (m c) (wardPhysicalPhaseSlots s) (A s) wi wo hs hη i o (z n)
  let B := (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass
  have hF : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s, ‖F n s‖ ≤ B + ε := by
    intro ε hε
    rw [Filter.eventually_all]
    intro s
    exact (hBound c hc s).2 wi wo hs η hη i o z P value grad Ce ell alpha
      hCe hEll hEll₁ hAlpha hv hSource hRate ε hε
  intro ε hε
  filter_upwards [wardPhysicalPhaseWeightedSum_bound F B hF ε hε] with n hn
  change ‖-Complex.I * ∑ s, (wardPhysicalPhaseMultiplicity s : ℂ) * F n s‖ ≤ _
  refine hn.trans_eq ?_
  unfold B
  ring
end Burnett.C02
