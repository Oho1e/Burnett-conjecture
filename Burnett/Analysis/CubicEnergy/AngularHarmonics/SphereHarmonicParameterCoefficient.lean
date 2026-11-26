import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicAngularJets

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A06

open Metric MeasureTheory
open scoped BigOperators ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Taking the coefficient of one actual real harmonic is a continuous
linear functional on the space of continuous real angular slices. -/
def roundSphereHarmonicCoefficientCLM (i : SphereHarmonicIndex) : C(RoundSphere3, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (sphereHarmonicFamilyLp i)).comp (ContinuousMap.toLp 2 roundSphere3Measure ℝ)

theorem roundSphereHarmonicCoefficientCLM_apply (i : SphereHarmonicIndex) (f : C(RoundSphere3, ℝ)) :
    roundSphereHarmonicCoefficientCLM i f =
      ∫ x, f x * sphereHarmonicFamily i x ∂roundSphere3Measure := by
  change inner ℝ (sphereHarmonicFamilyLp i) (ContinuousMap.toLp 2 roundSphere3Measure ℝ f) = _
  rw [← roundSphereHarmonicHilbertBasis_apply, ← HilbertBasis.repr_apply_apply]
  exact roundSphereHarmonicHilbertBasis_repr_apply f i

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate the actual coefficient of a family of continuous angular
slices by integrating its parameter derivative against the same harmonic. -/
theorem iteratedFDeriv_roundSphereHarmonicCoefficient_apply (i : SphereHarmonicIndex)
    (j : ℕ) {F : E → C(RoundSphere3, ℝ)} {p : E} (hF : ContDiffAt ℝ j F p)
    (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun z => ∫ x, F z x * sphereHarmonicFamily i x ∂roundSphere3Measure) p v =
      ∫ x, (iteratedFDeriv ℝ j F p v) x * sphereHarmonicFamily i x ∂roundSphere3Measure := by
  simp_rw [← roundSphereHarmonicCoefficientCLM_apply]
  change iteratedFDeriv ℝ j ((roundSphereHarmonicCoefficientCLM i) ∘ F) p v =
    roundSphereHarmonicCoefficientCLM i (iteratedFDeriv ℝ j F p v)
  rw [(roundSphereHarmonicCoefficientCLM i).iteratedFDeriv_comp_left hF le_rfl]
  rfl

/-- A local parameter derivative inherits the same degree decay whenever its
angular slices have a uniform bound on the actual twelve rotation jets. -/
theorem exists_norm_iteratedFDeriv_roundSphereHarmonicCoefficient_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℕ) (F : E → C(RoundSphere3, ℝ)) (p : E),
      ContDiffAt ℝ j F p → ∀ C : ℝ, 0 ≤ C →
      (∀ v : Fin j → E, ∃ f : RotationSpace → ℝ, ContDiff ℝ 12 f ∧
        (∀ x : RoundSphere3, f x = (iteratedFDeriv ℝ j F p v) x) ∧
        roundRotationJetBound 12 f (C * ∏ a, ‖v a‖)) →
      ∀ i : SphereHarmonicIndex,
      ‖iteratedFDeriv ℝ j (fun z => ∫ x, F z x * sphereHarmonicFamily i x ∂roundSphere3Measure) p‖ ≤
        K * (((i.1 : ℝ) + 1)^12)⁻¹ * C := by
  obtain ⟨K, hK, hcoeff⟩ := exists_roundSphereHarmonicCoefficient_rotationJetBound
  refine ⟨K, hK, ?_⟩
  intro j F p hF C hC hj i
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  obtain ⟨f, hf, hsame, hjet⟩ := hj v
  have hp : 0 ≤ C * ∏ a, ‖v a‖ := by positivity
  have hi :
      (∫ x, (iteratedFDeriv ℝ j F p v) x * sphereHarmonicFamily i x ∂roundSphere3Measure) =
        ∫ x : RoundSphere3, f x * sphereHarmonicFamily i x ∂roundSphere3Measure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrArg (· * sphereHarmonicFamily i x) (hsame x).symm
  rw [iteratedFDeriv_roundSphereHarmonicCoefficient_apply i j hF, hi]
  calc
    _ ≤ K * (((i.1 : ℝ) + 1)^12)⁻¹ * (C * ∏ a, ‖v a‖) :=
      hcoeff hf (C * ∏ a, ‖v a‖) hp hjet i
    _ = _ := by ring

end Burnett.A06
