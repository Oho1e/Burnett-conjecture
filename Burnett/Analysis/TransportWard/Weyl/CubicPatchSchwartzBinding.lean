import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Burnett.Analysis.Sobolev.TestJet

set_option autoImplicit false

noncomputable section

namespace Burnett.C01

open Filter Set Burnett.A02.FrequencySplit
open Burnett.X02.SobolevTestJet
open scoped BigOperators ContDiff Manifold Topology

/-- The complex Schwartz input representing the original real compact cutoff. -/
def realTestComplexSchwartz (d : D) : SchwartzMap E ℂ :=
  ((test_compactSupport d).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (test_smooth d))

/-- Use exactly the original real cubic partition in the Schwartz fields
used by the principal variation. The complex cubes sum to one as germs. -/
theorem exists_complexSchwartzCutoffs_of_real_cubic_family {J : Type}
    (s : Finset J) (χ : J → E → ℝ) (K V : Set E) (hV : IsOpen V) (hKV : K ⊆ V)
    (hCut : ∀ j ∈ s, ∃ d : D, (d : E → ℝ) = χ j)
    (hCube : ∀ x ∈ V, ∑ j ∈ s, χ j x ^ 3 = 1) :
    ∃ η : J → SchwartzMap E ℂ,
      (∀ j ∈ s, ∀ x, η j x = (χ j x : ℂ)) ∧
      ∀ x ∈ K, (fun y => ∑ j ∈ s, η j y ^ 3) =ᶠ[𝓝 x] fun _ : E => (1 : ℂ) := by
  classical
  let η (j : J) := if hj : j ∈ s then realTestComplexSchwartz ((hCut j hj).choose) else 0
  have hη (j : J) (hj : j ∈ s) (x : E) : η j x = (χ j x : ℂ) := by
    simp only [η, dif_pos hj]
    change Complex.ofReal (((hCut j hj).choose : E → ℝ) x) = _
    rw [(hCut j hj).choose_spec]
  refine ⟨η, hη, ?_⟩
  intro x hx
  filter_upwards [hV.mem_nhds (hKV hx)] with y hy
  calc
    _ = ∑ j ∈ s, (χ j y : ℂ)^3 :=
      Finset.sum_congr rfl (fun j hj => congrArg (fun t : ℂ => t^3) (hη j hj y))
    _ = ((∑ j ∈ s, χ j y ^ 3 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum, Complex.ofReal_pow]
    _ = (1 : ℂ) := by rw [hCube y hy, Complex.ofReal_one]

end Burnett.C01

namespace Burnett.P01

open Burnett.A02.FrequencySplit Burnett.RicciSymbol Burnett.Geometry
open ManifoldMetric ManifoldBilinear MaximalChart
open ConnectionDifference (metricComponents)
open Burnett.X02.SobolevTestJet
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- Multiplying the original cutoff perturbation by a patch cutoff is
exactly the C03 patch input when the original cutoff equals one there. -/
theorem receivingCutoffFluctuation_eq_patch_product_of_plateau
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ d : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (hd : tsupport (d : E → ℝ) ⊆ c.chart.target)
    (hOne : ∀ x ∈ tsupport (d : E → ℝ), (χ : E → ℝ) x = 1)
    (n : ℕ) (i j : Index) :
    energyProduct (Burnett.C01.realTestComplexSchwartz d)
        (receivingCutoffFluctuation B g hB hg c χ hχ n i j) =
      receivingCutoffFluctuation B g hB hg c d hd n i j := by
  ext x
  let H := metricComponents (fixedForm (g n) c) x i j - metricComponents (fixedForm B c) x i j
  change Complex.ofReal ((d : E → ℝ) x) * Complex.ofReal ((χ : E → ℝ) x * H) =
    Complex.ofReal ((d : E → ℝ) x * H)
  by_cases h : (d : E → ℝ) x = 0
  · simp only [h, Complex.ofReal_zero, zero_mul]
  · have hχOne := hOne x (subset_tsupport (d : E → ℝ) h)
    rw [hχOne, one_mul, Complex.ofReal_mul]

end Burnett.P01
