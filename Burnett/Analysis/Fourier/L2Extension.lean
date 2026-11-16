import Burnett.Analysis.Fourier.SchwartzDensity
import Burnett.Analysis.Fourier.SchwartzParseval
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Completeness

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Filter
open scoped FourierTransform Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

abbrev ComplexL2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] :=
  Lp ℂ 2 (volume : Measure V)

theorem schwartz_toLp_norm_sq (f : SchwartzMap V ℂ) :
    ‖f.toLp 2 volume‖^2 = ∫ x, ‖f x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem schwartz_fourier_toLp_norm (f : SchwartzMap V ℂ) :
    ‖(SchwartzMap.fourierTransformCLM ℂ f).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [schwartz_toLp_norm_sq, schwartz_toLp_norm_sq]
  exact schwartz_parseval f

def schwartzLpMap : SchwartzMap V ℂ →L[ℂ] ComplexL2 V :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume

def schwartzL2Range : Submodule ℂ (ComplexL2 V) :=
  LinearMap.range (schwartzLpMap (V := V)).toLinearMap

def schwartzRangeEquiv : SchwartzMap V ℂ ≃ₗ[ℂ] schwartzL2Range (V := V) :=
  LinearEquiv.ofInjective (schwartzLpMap (V := V)).toLinearMap
    (SchwartzMap.injective_toLp 2 volume)

def fourierOnSchwartzRangeLinear : schwartzL2Range (V := V) →ₗ[ℂ] ComplexL2 V :=
  (schwartzLpMap (V := V)).toLinearMap.comp
    ((SchwartzMap.fourierTransformCLM ℂ).toLinearMap.comp
      (schwartzRangeEquiv (V := V)).symm.toLinearMap)

theorem fourierOnSchwartzRangeLinear_norm (x : schwartzL2Range (V := V)) :
    ‖fourierOnSchwartzRangeLinear x‖ = ‖x‖ := by
  obtain ⟨f, rfl⟩ := (schwartzRangeEquiv (V := V)).surjective x
  simp only [fourierOnSchwartzRangeLinear, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  change ‖(SchwartzMap.fourierTransformCLM ℂ f).toLp 2 volume‖ = ‖f.toLp 2 volume‖
  exact schwartz_fourier_toLp_norm f

def fourierOnSchwartzRange : schwartzL2Range (V := V) →ₗᵢ[ℂ] ComplexL2 V :=
  ⟨fourierOnSchwartzRangeLinear, fourierOnSchwartzRangeLinear_norm⟩

theorem schwartzL2Range_dense : Dense (schwartzL2Range (V := V) : Set (ComplexL2 V)) :=
  schwartz_toLp_denseRange

/-- The actual continuous L² Fourier extension is constructed along the
Schwartz image equipped with its inherited L² norm, rather than along the
stronger Schwartz topology. -/
def fourierL2CLM : ComplexL2 V →L[ℂ] ComplexL2 V :=
  (fourierOnSchwartzRange (V := V)).toContinuousLinearMap.extend
    (schwartzL2Range (V := V)).subtypeL schwartzL2Range_dense.denseRange_val
    (schwartzL2Range (V := V)).subtypeₗᵢ.isometry.isUniformInducing

theorem fourierL2CLM_schwartz (f : SchwartzMap V ℂ) :
    fourierL2CLM (f.toLp 2 volume) = (SchwartzMap.fourierTransformCLM ℂ f).toLp 2 volume := by
  have he := ContinuousLinearMap.extend_eq
    (fourierOnSchwartzRange (V := V)).toContinuousLinearMap
    (schwartzL2Range (V := V)).subtypeL schwartzL2Range_dense.denseRange_val
    (schwartzL2Range (V := V)).subtypeₗᵢ.isometry.isUniformInducing
    (schwartzRangeEquiv f)
  change fourierL2CLM (f.toLp 2 volume) =
    fourierOnSchwartzRange (schwartzRangeEquiv f) at he
  rw [he]
  change (SchwartzMap.fourierTransformCLM ℂ
    ((schwartzRangeEquiv (V := V)).symm (schwartzRangeEquiv f))).toLp 2 volume = _
  rw [LinearEquiv.symm_apply_apply]

theorem fourierL2CLM_norm (x : ComplexL2 V) : ‖fourierL2CLM x‖ = ‖x‖ := by
  apply (schwartz_toLp_denseRange (V := V)).induction_on (p := fun y => ‖fourierL2CLM y‖ = ‖y‖) x
  · exact isClosed_eq fourierL2CLM.continuous.norm continuous_norm
  · intro f
    rw [fourierL2CLM_schwartz]
    exact schwartz_fourier_toLp_norm f

def fourierL2 : ComplexL2 V →ₗᵢ[ℂ] ComplexL2 V :=
  ⟨fourierL2CLM.toLinearMap, fourierL2CLM_norm⟩

theorem fourierL2_surjective : Function.Surjective (fourierL2 (V := V)) := by
  have hr : Set.range (fun f : SchwartzMap V ℂ => f.toLp 2 (volume : Measure V)) ⊆
      Set.range (fourierL2 (V := V)) := by
    rintro _ ⟨f, rfl⟩
    refine ⟨((SchwartzMap.fourierTransformCLE ℂ).symm f).toLp 2 volume, ?_⟩
    change fourierL2CLM _ = _
    rw [fourierL2CLM_schwartz]
    change ((SchwartzMap.fourierTransformCLE ℂ)
      ((SchwartzMap.fourierTransformCLE ℂ).symm f)).toLp 2 volume = f.toLp 2 volume
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hd : DenseRange (fourierL2 (V := V)) := schwartz_toLp_denseRange.mono hr
  have hc := (fourierL2 (V := V)).isometry.isClosedEmbedding.isClosed_range
  have ht := hd.closure_range
  rw [hc.closure_eq] at ht
  exact Set.range_eq_univ.mp ht

/-- The Fourier transform on actual complex L²(volume), including its
inverse, as a linear isometric equivalence. -/
def fourierL2Equiv : ComplexL2 V ≃ₗᵢ[ℂ] ComplexL2 V :=
  LinearIsometryEquiv.ofSurjective fourierL2 fourierL2_surjective

theorem fourierL2Equiv_schwartz (f : SchwartzMap V ℂ) :
    fourierL2Equiv (f.toLp 2 volume) = (SchwartzMap.fourierTransformCLE ℂ f).toLp 2 volume :=
  fourierL2CLM_schwartz f

theorem fourierL2Equiv_symm_schwartz (f : SchwartzMap V ℂ) :
    fourierL2Equiv.symm (f.toLp 2 volume) =
      ((SchwartzMap.fourierTransformCLE ℂ).symm f).toLp 2 volume := by
  apply (fourierL2Equiv (V := V)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourierL2Equiv_schwartz,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The extension agrees a.e. with the actual Fourier integral on every
Schwartz function, including the fixed `2π` normalization. -/
theorem fourierL2Equiv_schwartz_ae (f : SchwartzMap V ℂ) :
    (fourierL2Equiv (f.toLp 2 volume) : V → ℂ) =ᵐ[volume] 𝓕 (f : V → ℂ) := by
  rw [fourierL2Equiv_schwartz]
  exact (SchwartzMap.fourierTransformCLE ℂ f).coeFn_toLp 2 volume

theorem fourierL2Equiv_symm_schwartz_ae (f : SchwartzMap V ℂ) :
    (fourierL2Equiv.symm (f.toLp 2 volume) : V → ℂ) =ᵐ[volume] 𝓕⁻ (f : V → ℂ) := by
  rw [fourierL2Equiv_symm_schwartz]
  simpa only [SchwartzMap.fourierTransformCLE_symm_apply] using
    ((SchwartzMap.fourierTransformCLE ℂ).symm f).coeFn_toLp 2 volume

end Burnett.Fourier
