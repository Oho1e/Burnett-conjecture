import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeNormalizedSymbol
import Burnett.Analysis.FrozenTransport.GaugeCorrection.CyclicLowPhaseSmooth

set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.V08

open Set Matrix Burnett.P01
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff BigOperators Matrix

/-- The actual normalized low-gauge coefficient on its independent
low direction, Cartesian ratio, and high direction. -/
def lowGaugeJointProfile (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (G : ComplexComponents) (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (i j : TensorSlot) (x : E × E × E) : ℂ :=
  ((w / 3 * cyclicLowNormalizedPhase a x.1 x.2.1 x.2.2 : ℝ) : ℂ) *
    lowGaugeNormalizedHighDifference m G x.1 x.2.1 x.2.2 *
    (lowGaugeHighMatrix C S x.2.1 x.2.2 i j : ℂ)

/-- All independent joint derivatives exist on the complete low-angle
profile, including ratio zero, when the two high screens are smooth on
nonzero covectors. -/
theorem lowGaugeJointProfile_contDiffOn
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (G : ComplexComponents) (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun ξ => S ξ i j) {ξ : E | ξ ≠ 0})
    (i j : TensorSlot) :
    ContDiffOn ℝ ∞ (lowGaugeJointProfile m w a G C S i j) cyclicLowProfileSet := by
  let W := cyclicLowProfileSet
  have hHigh : ContDiff ℝ ∞ (fun x : E × E × E => x.2.2) := contDiff_snd.comp contDiff_snd
  have hRatio : ContDiff ℝ ∞ (fun x : E × E × E => x.2.1) := contDiff_fst.comp contDiff_snd
  have hHighNe (x : E × E × E) (hx : x ∈ W) : x.2.2 ≠ 0 := by
    obtain ⟨_, _, h⟩ := hx
    exact norm_ne_zero_iff.mp (ne_of_gt ((by norm_num : (0 : ℝ) < 3/4).trans h))
  have hOutNe (x : E × E × E) (hx : x ∈ W) : x.2.1 + x.2.2 ≠ 0 := by
    obtain ⟨_, hR, hH⟩ := hx
    intro hz
    have hθ : x.2.2 = -(x.2.1) := eq_neg_of_add_eq_zero_right hz
    rw [hθ, norm_neg] at hH
    linarith
  have hInput (k l : TensorSlot) :
      ContDiffOn ℝ ∞ (fun x : E × E × E => S x.2.2 k l) W :=
    (hS k l).comp hHigh.contDiffOn hHighNe
  have hOutput (k l : TensorSlot) :
      ContDiffOn ℝ ∞ (fun x : E × E × E => S (x.2.1 + x.2.2) k l) W :=
    (hS k l).comp (hRatio.add hHigh).contDiffOn hOutNe
  have hMatrix : ContDiffOn ℝ ∞ (fun x : E × E × E => lowGaugeHighMatrix C S x.2.1 x.2.2 i j) W := by
    simp only [lowGaugeHighMatrix, Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffOn.sum fun k _ => (ContDiffOn.sum fun l _ =>
      (hOutput l i).mul contDiffOn_const).mul (hInput k j)
  have hDifference : ContDiffOn ℝ ∞
      (fun x : E × E × E => lowGaugeNormalizedHighDifference m G x.1 x.2.1 x.2.2) W := by
    have hHighSum : ContDiff ℝ ∞ (fun x : E × E × E => x.2.2 + (x.2.1 + x.2.2)) :=
      hHigh.add (hRatio.add hHigh)
    have hCoord (k : Fin 4) : ContDiff ℝ ∞
        (fun x : E × E × E => ((x.2.2 + (x.2.1 + x.2.2)) k : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hHighSum)
    simp only [lowGaugeNormalizedHighDifference, lowGaugeHighDifference]
    exact ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      (contDiffOn_const.mul
        ((normalizedGaugePotential_contDiff G l).comp contDiff_fst).contDiffOn).mul (hCoord k).contDiffOn
  have hTest : ContDiffOn ℝ ∞
      (fun x : E × E × E => ((w / 3 * cyclicLowNormalizedPhase a x.1 x.2.1 x.2.2 : ℝ) : ℂ)) W :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul (cyclicLowNormalizedPhase_contDiffOn a ha))
  exact (hTest.mul hDifference).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hMatrix)

end Burnett.V08
