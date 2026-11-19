import Burnett.Geometry.Cotangent.RadialExtension
import Burnett.Counterexamples.Bianchi.NormChange

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.CotangentUnitNormalization

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The actual unit shell of the continuous-dual tangent bundle for the auxiliary metric r. -/
def unitShell (r : Metric (M := M)) : Set (CotangentBundle M) :=
  {p | dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p = 1}

theorem unitShell_punctured (r : Metric (M := M)) {p : CotangentBundle M} (hp : p ∈ unitShell r) :
    p ∈ puncturedCotangent := by
  intro hz
  have he : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p = 0 := by
    unfold dualEnergy
    rw [hz]
    rfl
  rw [hp] at he
  norm_num at he

theorem unitShell_cotangentNorm (r : Metric (M := M)) (p : unitShell r) :
    cotangentNorm r p.1 = 1 := by
  have hp : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p.1 = 1 := p.property
  simp only [cotangentNorm, hp, Real.sqrt_one]

def shellScale (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) : ℝ := cotangentNorm r₂ p.1

theorem shellScale_pos (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) : 0 < shellScale r₁ r₂ p :=
  cotangentNorm_pos r₂ (unitShell_punctured r₁ p.property)

theorem shellScale_continuous (r₁ r₂ : Metric (M := M)) : Continuous (shellScale r₁ r₂) :=
  ((contMDiffOn_cotangentNorm r₂).continuousOn.mono (fun _ hp => unitShell_punctured r₁ hp)).restrict

def shellNormalize (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) : unitShell r₂ :=
  ⟨cotangentNormalize r₂ p.1, cotangentNormalize_auxiliary_square r₂ (unitShell_punctured r₁ p.property)⟩

theorem shellNormalize_continuous (r₁ r₂ : Metric (M := M)) : Continuous (shellNormalize r₁ r₂) := by
  exact (((contMDiffOn_cotangentNormalize r₂).continuousOn.mono
    (fun _ hp => unitShell_punctured r₁ hp)).restrict).subtype_mk _

theorem shellNormalize_inverse (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) :
    shellNormalize r₂ r₁ (shellNormalize r₁ r₂ p) = p := by
  apply Subtype.ext
  change cotangentNormalize r₁ (cotangentScale (shellScale r₁ r₂ p)⁻¹ p.1) = p.1
  rw [cotangentNormalize_scale r₁ (unitShell_punctured r₁ p.property)
    (inv_pos.mpr (shellScale_pos r₁ r₂ p))]
  exact cotangentNormalize_of_auxiliary_one r₁ p.1 p.property

/-- A genuine homeomorphism between arbitrary auxiliary unit cotangent shells on the same manifold. -/
def unitShellHomeomorph (r₁ r₂ : Metric (M := M)) : unitShell r₁ ≃ₜ unitShell r₂ where
  toFun := shellNormalize r₁ r₂
  invFun := shellNormalize r₂ r₁
  left_inv := shellNormalize_inverse r₁ r₂
  right_inv := shellNormalize_inverse r₂ r₁
  continuous_toFun := shellNormalize_continuous r₁ r₂
  continuous_invFun := shellNormalize_continuous r₂ r₁

theorem unitShellHomeomorph_symm (r₁ r₂ : Metric (M := M)) :
    (unitShellHomeomorph r₁ r₂).symm = unitShellHomeomorph r₂ r₁ := by
  apply Homeomorph.ext
  intro p
  rfl

theorem unitShellHomeomorph_projection (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) :
    ((unitShellHomeomorph r₁ r₂ p).1).proj = p.1.proj := rfl

theorem unitShellHomeomorph_value (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) :
    (unitShellHomeomorph r₁ r₂ p).1 = cotangentScale (shellScale r₁ r₂ p)⁻¹ p.1 := rfl

theorem shellScale_inverse (r₁ r₂ : Metric (M := M)) (p : unitShell r₁) :
    shellScale r₂ r₁ (unitShellHomeomorph r₁ r₂ p) = (shellScale r₁ r₂ p)⁻¹ := by
  change cotangentNorm r₁ (cotangentScale (shellScale r₁ r₂ p)⁻¹ p.1) = _
  rw [cotangentNorm_scale r₁ p.1 (inv_pos.mpr (shellScale_pos r₁ r₂ p)), unitShell_cotangentNorm, mul_one]

theorem unitShellHomeomorph_dualEnergy (r₁ r₂ : Metric (M := M))
    (g : ManifoldBilinear.Field (M := M)) (hgn : ManifoldBilinear.IsNondegenerate g)
    (p : unitShell r₁) :
    dualEnergy g hgn (unitShellHomeomorph r₁ r₂ p).1 =
      (shellScale r₁ r₂ p)⁻¹ ^ 2 * dualEnergy g hgn p.1 := by
  rw [unitShellHomeomorph_value, dualEnergy_cotangentScale]

theorem unitShellHomeomorph_null_iff (r₁ r₂ : Metric (M := M))
    (g : ManifoldBilinear.Field (M := M)) (hgn : ManifoldBilinear.IsNondegenerate g)
    (p : unitShell r₁) :
    dualEnergy g hgn (unitShellHomeomorph r₁ r₂ p).1 = 0 ↔ dualEnergy g hgn p.1 = 0 := by
  rw [unitShellHomeomorph_dualEnergy, mul_eq_zero]
  simp [(shellScale_pos r₁ r₂ p).ne']

section Measure

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

def renormalized (r₁ r₂ : Metric (M := M)) (μ : Measure (unitShell r₁)) : Measure (unitShell r₂) :=
  Burnett.Bianchi.NormChange.rescaled μ (unitShellHomeomorph r₁ r₂) (shellScale r₁ r₂)

theorem renormalized_locallyFinite (r₁ r₂ : Metric (M := M)) (μ : Measure (unitShell r₁))
    [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (renormalized r₁ r₂ μ) :=
  Burnett.Bianchi.NormChange.rescaled_locallyFinite μ (unitShellHomeomorph r₁ r₂)
    (shellScale r₁ r₂) (shellScale_continuous r₁ r₂)

theorem renormalized_null_iff (r₁ r₂ : Metric (M := M)) (μ : Measure (unitShell r₁))
    (S : Set (unitShell r₂)) :
    renormalized r₁ r₂ μ S = 0 ↔ μ ((unitShellHomeomorph r₁ r₂) ⁻¹' S) = 0 :=
  Burnett.Bianchi.NormChange.rescaled_null_iff μ (unitShellHomeomorph r₁ r₂)
    (shellScale r₁ r₂) (shellScale_continuous r₁ r₂) (shellScale_pos r₁ r₂) S

theorem renormalized_null_support_iff (r₁ r₂ : Metric (M := M)) (μ : Measure (unitShell r₁))
    (g : ManifoldBilinear.Field (M := M)) (hgn : ManifoldBilinear.IsNondegenerate g) :
    renormalized r₁ r₂ μ {p | dualEnergy g hgn p.1 ≠ 0} = 0 ↔
      μ {p | dualEnergy g hgn p.1 ≠ 0} = 0 := by
  rw [renormalized_null_iff]
  have hs : (unitShellHomeomorph r₁ r₂) ⁻¹' {p | dualEnergy g hgn p.1 ≠ 0} =
      {p | dualEnergy g hgn p.1 ≠ 0} := by
    ext p
    exact not_congr (unitShellHomeomorph_null_iff r₁ r₂ g hgn p)
  rw [hs]

theorem renormalized_quadratic_tests (r₁ r₂ : Metric (M := M)) (μ : Measure (unitShell r₁))
    (q : CotangentBundle M → ℝ)
    (hq : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), q (cotangentScale t p) = t ^ 2 * q p) :
    (Integrable (fun p : unitShell r₂ => q p.1) (renormalized r₁ r₂ μ) ↔
      Integrable (fun p : unitShell r₁ => q p.1) μ) ∧
      (∫ p : unitShell r₂, q p.1 ∂renormalized r₁ r₂ μ) = ∫ p : unitShell r₁, q p.1 ∂μ := by
  apply Burnett.Bianchi.NormChange.divided_quadratic_test_preserved μ (unitShellHomeomorph r₁ r₂)
    (shellScale r₁ r₂) (shellScale_continuous r₁ r₂) (shellScale_pos r₁ r₂)
  intro p
  rw [unitShellHomeomorph_value,
    hq p.1 (unitShell_punctured r₁ p.property) _ (inv_pos.mpr (shellScale_pos r₁ r₂ p)), inv_pow]
  exact (div_eq_inv_mul _ _).symm

theorem renormalized_inverse (r₁ r₂ : Metric (M := M)) (μ : Measure (unitShell r₁)) :
    renormalized r₂ r₁ (renormalized r₁ r₂ μ) = μ := by
  have hF : unitShellHomeomorph r₂ r₁ = (unitShellHomeomorph r₁ r₂).symm :=
    (unitShellHomeomorph_symm r₁ r₂).symm
  have hA : shellScale r₂ r₁ = Burnett.Bianchi.NormChange.inverseScale
      (unitShellHomeomorph r₁ r₂) (shellScale r₁ r₂) := by
    funext p
    have h := shellScale_inverse r₁ r₂ ((unitShellHomeomorph r₁ r₂).symm p)
    simpa only [Homeomorph.apply_symm_apply, Burnett.Bianchi.NormChange.inverseScale] using h
  unfold renormalized
  rw [hF, hA]
  exact Burnett.Bianchi.NormChange.rescaled_inverse μ (unitShellHomeomorph r₁ r₂)
    (shellScale r₁ r₂) (shellScale_continuous r₁ r₂) (shellScale_pos r₁ r₂)

end Measure

end Burnett.Geometry.CotangentUnitNormalization
