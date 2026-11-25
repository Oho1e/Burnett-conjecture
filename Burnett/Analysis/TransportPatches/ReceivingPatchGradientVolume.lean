import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge
import Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

/-! Use the very same C01 cutoff in the actual receiving-chart derivative tests. -/

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 5900000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open Burnett.Microlocal.AtlasVolumeGradient (fixedPerturbation)
open Burnett.P01 (receivingCutoffFluctuation projectionMatrixDerivative projectionMatrixLpNorm)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [SecondCountableTopology M]

/-- The real matrix to which the C01 first-derivative estimate applies. -/
def receivingRealPatchField (B g : Field (M := M)) (c : AtlasChart M) (χ : D) (x : E) : Tensor2 :=
  (χ : E → ℝ) x • fixedPerturbation B g c x

private def tensorEntry (i j : Index) : Tensor2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index => Index → ℝ) i)

private theorem coordinateBasis_single (i : Index) : coordinateBasis i = EuclideanSpace.single i 1 :=
  EuclideanSpace.basisFun_apply _ _ i

theorem receivingCutoffFluctuation_derivative_eq_realPatchField
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (n : ℕ) (b i j : Index) (x : E) :
    projectionMatrixDerivative b (receivingCutoffFluctuation B g hB hg c χ hχ n) i j x =
      ((fderiv ℝ (receivingRealPatchField B (g n) c χ) x (coordinateBasis b) i j : ℝ) : ℂ) := by
  let F := receivingRealPatchField B (g n) c χ
  let w := receivingCutoffFluctuation B g hB hg c χ hχ n
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro b
    change ContDiff ℝ ∞ (fun y => (w a b y).re)
    exact Complex.reCLM.contDiff.comp (w a b).smooth'
  have hFun : (w i j : E → ℂ) = (Complex.ofRealCLM.comp (tensorEntry i j)) ∘ F := rfl
  have hD := (Complex.ofRealCLM.comp (tensorEntry i j)).hasFDerivAt.comp x
    ((hF.differentiable (by simp) x).hasFDerivAt)
  change (coordinateDerivative b (w i j)) x = _
  rw [coordinateDerivative, SchwartzMap.pderivCLM_apply, hFun, hD.fderiv, coordinateBasis_single]
  rfl

/-- The raw chart gradient estimate controls every actual complex Schwartz
coordinate row with the same patch volume and no additional factor. -/
theorem receivingCutoffFluctuation_derivative_Lp_le
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (p : ℝ) (n : ℕ) (b : Index) :
    projectionMatrixLpNorm p (projectionMatrixDerivative b (receivingCutoffFluctuation B g hB hg c χ hχ n)) ≤
      eLpNorm (fderiv ℝ (receivingRealPatchField B (g n) c χ)) (ENNReal.ofReal p) volume := by
  apply eLpNorm_mono
  intro x
  let L := fderiv ℝ (receivingRealPatchField B (g n) c χ) x
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg L)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg L)).2
  intro j
  rw [receivingCutoffFluctuation_derivative_eq_realPatchField, Complex.norm_real]
  change ‖L (coordinateBasis b) i j‖ ≤ ‖L‖
  have hb : ‖coordinateBasis b‖ = 1 := by
    rw [coordinateBasis_single, EuclideanSpace.norm_single, norm_one]
  exact ((norm_le_pi_norm (L (coordinateBasis b) i) j).trans
    (norm_le_pi_norm (L (coordinateBasis b)) i)).trans (by simpa only [hb, mul_one] using L.le_opNorm (coordinateBasis b))

/-- The conclusion of the C01 matrix derivative-volume estimate, carried
on the actual receiving cutoff and the chosen original subsequence. -/
theorem receivingCutoffFluctuation_eventually_derivative_volume
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (P : Set E) (p C : ℝ)
    (hVolume : ∀ᶠ n in atTop, eLpNorm (fderiv ℝ (receivingRealPatchField B (g n) c χ))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * (volume : Measure E) P ^ (1 / p)) :
    ∀ᶠ n in atTop, ∀ b : Index, projectionMatrixLpNorm p
      (projectionMatrixDerivative b (receivingCutoffFluctuation B g hB hg c χ hχ (σ n))) ≤
        ENNReal.ofReal C * (volume : Measure E) P ^ (1 / p) := by
  filter_upwards [hσ.tendsto_atTop.eventually hVolume] with n hn
  intro b
  exact (receivingCutoffFluctuation_derivative_Lp_le B g hB hg c χ hχ p (σ n) b).trans hn

end Burnett.C02
