import Burnett.Analysis.AngularCaps.LinearFourierChange

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Filter
open scoped ENNReal

abbrev ComplexLp (p : ℝ≥0∞) := Lp ℂ p (volume : Measure Space)

def pullbackNormFactor (A : Space ≃L[ℝ] Space) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (linearJacobian A)⁻¹ ^ (1 / p).toReal

theorem pullbackNormFactor_symm_mul (A : Space ≃L[ℝ] Space) (p : ℝ≥0∞) :
    (pullbackNormFactor A p).toReal * (pullbackNormFactor A.symm p).toReal = 1 := by
  rw [← ENNReal.toReal_mul]
  have h : ENNReal.ofReal (linearJacobian A)⁻¹ * ENNReal.ofReal (linearJacobian A) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (linearJacobian_pos A).le),
      inv_mul_cancel₀ (linearJacobian_pos A).ne',ENNReal.ofReal_one]
  rw [pullbackNormFactor,pullbackNormFactor,linearJacobian_symm,inv_inv,
    ← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,h,ENNReal.one_rpow,ENNReal.toReal_one]

theorem quasiMeasurePreserving_linear (A : Space ≃L[ℝ] Space) :
    Measure.QuasiMeasurePreserving A (volume : Measure Space) volume := by
  refine ⟨A.continuous.measurable,?_⟩
  rw [map_linear_volume]
  exact Measure.smul_absolutelyContinuous

theorem memLp_comp_linearEquiv {p : ℝ≥0∞} {f : Space → ℂ}
    (A : Space ≃L[ℝ] Space) (hf : MemLp f p volume) : MemLp (f ∘ A) p volume := by
  have hm : MemLp f p (Measure.map A volume) := by
    rw [map_linear_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map A.continuous.measurable.aemeasurable

theorem eLpNorm_comp_linearEquiv {p : ℝ≥0∞} (hp : p ≠ ∞) {f : Space → ℂ}
    (A : Space ≃L[ℝ] Space) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (f ∘ A) p volume = pullbackNormFactor A p * eLpNorm f p volume := by
  have hm : AEStronglyMeasurable f (Measure.map A volume) :=
    hf.mono_ac (quasiMeasurePreserving_linear A).absolutelyContinuous
  rw [← eLpNorm_map_measure hm A.continuous.measurable.aemeasurable, map_linear_volume,
    eLpNorm_smul_measure_of_ne_top hp,pullbackNormFactor,smul_eq_mul]

private def pullbackRep {p : ℝ≥0∞} (A : Space ≃L[ℝ] Space)
    (f : ComplexLp p) : ComplexLp p :=
  (memLp_comp_linearEquiv A (Lp.memLp f)).toLp (f ∘ A)

private theorem pullbackRep_ae {p : ℝ≥0∞} (A : Space ≃L[ℝ] Space) (f : ComplexLp p) :
    (pullbackRep A f : Space → ℂ) =ᵐ[volume] (f ∘ A) :=
  (memLp_comp_linearEquiv A (Lp.memLp f)).coeFn_toLp

private theorem pullbackRep_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : Space ≃L[ℝ] Space) (f : ComplexLp p) :
    ‖pullbackRep A f‖ = (pullbackNormFactor A p).toReal * ‖f‖ := by
  rw [Lp.norm_def (pullbackRep A f),eLpNorm_congr_ae (pullbackRep_ae A f),
    eLpNorm_comp_linearEquiv hp A (Lp.memLp f).aestronglyMeasurable,
    ENNReal.toReal_mul,← Lp.norm_def f]

private def pullbackLinear {p : ℝ≥0∞} (A : Space ≃L[ℝ] Space) :
    ComplexLp p →ₗ[ℂ] ComplexLp p where
  toFun := pullbackRep A
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [pullbackRep_ae A (f + g),pullbackRep_ae A f,pullbackRep_ae A g,
      (quasiMeasurePreserving_linear A).ae_eq_comp (Lp.coeFn_add f g),
      Lp.coeFn_add (pullbackRep A f) (pullbackRep A g)] with x hfg hf hg hfg' hadd
    simp only [Function.comp_apply,Pi.add_apply] at *
    exact hfg.trans (hfg'.trans (by rw [hadd,hf,hg]))
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [pullbackRep_ae A (c • f),pullbackRep_ae A f,
      (quasiMeasurePreserving_linear A).ae_eq_comp (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (pullbackRep A f)] with x hcf hf hcf' hsmul
    simp only [Function.comp_apply,Pi.smul_apply,RingHom.id_apply] at *
    exact hcf.trans (hcf'.trans (by rw [hsmul,hf]))

/-- Pullback of a complex Lᵖ function by an invertible real linear map.
Its only norm change is the Jacobian raised to the exponent -1/p. -/
def linearLpPullback {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (A : Space ≃L[ℝ] Space) :
    ComplexLp p →L[ℂ] ComplexLp p := by
  apply (pullbackLinear (p := p) A).mkContinuous (pullbackNormFactor A p).toReal
  intro f
  change ‖pullbackRep A f‖ ≤ _
  exact (pullbackRep_norm hp A f).le

theorem linearLpPullback_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : Space ≃L[ℝ] Space) (f : ComplexLp p) :
    (linearLpPullback hp A f : Space → ℂ) =ᵐ[volume] (f ∘ A) :=
  pullbackRep_ae A f

theorem linearLpPullback_toLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : Space ≃L[ℝ] Space) {f : Space → ℂ} (hf : MemLp f p volume) :
    linearLpPullback hp A (hf.toLp f) =
      (memLp_comp_linearEquiv A hf).toLp (f ∘ A) := by
  apply Lp.ext
  exact (linearLpPullback_ae hp A _).trans <|
    ((quasiMeasurePreserving_linear A).ae_eq_comp hf.coeFn_toLp).trans
      (memLp_comp_linearEquiv A hf).coeFn_toLp.symm

theorem linearLpPullback_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : Space ≃L[ℝ] Space) (f : ComplexLp p) :
    ‖linearLpPullback hp A f‖ = (pullbackNormFactor A p).toReal * ‖f‖ :=
  pullbackRep_norm hp A f

end Burnett.Analysis.CapFourier
