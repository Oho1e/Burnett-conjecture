import Burnett.Analysis.CubicEnergy.AngularHarmonics.JointAngularComplexCoefficient

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 MeasureTheory Metric Set
open scoped ContDiff

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem smoothCoefficientOnProduct
    {F : E × RotationSpace → ℂ} {U : Set E} {V : Set RotationSpace}
    (hU : IsOpen U) (hV : IsOpen V) (hs : sphere (0 : RotationSpace) 1 ⊆ V)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V)) (i : SphereHarmonicIndex) :
    ContDiffOn ℝ ∞ (jointSphereHarmonicCoefficientComplex F i) U := by
  let A := Complex.ofRealCLM
  let B : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM
  apply contDiffOn_infty.mpr
  intro n
  have hf : ContDiffOn ℝ (n + 1 : ℕ) F (U ×ˢ V) :=
    hF.of_le (WithTop.coe_le_coe.mpr le_top)
  have hr := jointSphereHarmonicCoefficient_contDiffOn n
    (Complex.reCLM.contDiff.comp_contDiffOn hf) hU hV hs i
  have hi := jointSphereHarmonicCoefficient_contDiffOn n
    (Complex.imCLM.contDiff.comp_contDiffOn hf) hU hV hs i
  refine ((A.contDiff.comp_contDiffOn hr).add (B.contDiff.comp_contDiffOn hi)).congr ?_
  intro p hp
  have hx : Continuous fun x : RoundSphere3 => F (p,x) :=
    hF.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun x => ⟨hp, hs x.property⟩)
  let g (x : RoundSphere3) := F (p,x) * (sphereHarmonicFamily i x : ℂ)
  have hg : Continuous g :=
    hx.mul (Complex.continuous_ofReal.comp (sphereHarmonicFamily i).continuous)
  have hgi : Integrable g roundSphere3Measure :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have re_coefficient : (jointSphereHarmonicCoefficientComplex F i p).re =
      jointSphereHarmonicCoefficient (Complex.reCLM ∘ F) i p := by
    simpa [jointSphereHarmonicCoefficientComplex, jointSphereHarmonicCoefficient, g,
      Function.comp_apply, Complex.mul_re] using (Complex.reCLM.integral_comp_comm hgi).symm
  have im_coefficient : (jointSphereHarmonicCoefficientComplex F i p).im =
      jointSphereHarmonicCoefficient (Complex.imCLM ∘ F) i p := by
    simpa [jointSphereHarmonicCoefficientComplex, jointSphereHarmonicCoefficient, g,
      Function.comp_apply, Complex.mul_im] using (Complex.imCLM.integral_comp_comm hgi).symm
  change jointSphereHarmonicCoefficientComplex F i p =
    A (jointSphereHarmonicCoefficient (Complex.reCLM ∘ F) i p) +
      B (jointSphereHarmonicCoefficient (Complex.imCLM ∘ F) i p)
  rw [← re_coefficient, ← im_coefficient]
  simp only [A, B, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact (Complex.re_add_im _).symm

/-- Smoothness and the 27-to-15 bound use the same actual complex coefficient.
Only the first 27 derivatives enter the quantitative estimate. -/
theorem exists_smoothComplexAngularCoefficient_jet15 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : E × RotationSpace → ℂ} {W : Set (E × RotationSpace)} {K : Set E},
      IsOpen W → IsCompact K → K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W →
      ContDiffOn ℝ ∞ F W → ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ 27 → ∀ p ∈ K, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) →
      ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧
      ∀ i : SphereHarmonicIndex, ContDiffOn ℝ ∞ (jointSphereHarmonicCoefficientComplex F i) U ∧
        ∀ j : ℕ, j ≤ 15 → ∀ p ∈ K,
          ‖iteratedFDeriv ℝ j (jointSphereHarmonicCoefficientComplex F i) p‖ ≤
            C * (((i.1 : ℝ) + 1)^12)⁻¹ * M := by
  obtain ⟨C,hC,jet⟩ := exists_jointSphereHarmonicCoefficientComplex_on_open_neighborhood (E := E)
  refine ⟨C,hC,?_⟩
  intro F W K hW hK hKW hf M hM hjet
  obtain ⟨U,hU,hKU,V,hV,hVS,hWV⟩ := exists_jointAngular_open_product hK hW hKW
  obtain ⟨U',hU',hKU',bound⟩ :=
    jet (F := F) hW hK hKW 15 (hf.of_le (WithTop.coe_le_coe.mpr le_top)) M hM hjet
  exact ⟨U ∩ U',hU.inter hU',fun _ p => ⟨hKU p,hKU' p⟩, fun i =>
    ⟨(smoothCoefficientOnProduct hU hV hVS (hf.mono hWV) i).mono inter_subset_left,(bound i).2⟩⟩

end Burnett.A07
