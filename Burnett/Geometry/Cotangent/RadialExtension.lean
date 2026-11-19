import Burnett.Geometry.Cotangent.SmoothExtension

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.CotangentAngularExtension

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.FiberMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The norm of a real cotangent vector in the given auxiliary metric. -/
def cotangentNorm (r : Metric (M := M)) (p : CotangentBundle M) : ℝ :=
  Real.sqrt (dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p)

theorem auxiliary_dualEnergy_pos (r : Metric (M := M)) {p : CotangentBundle M}
    (hp : p ∈ puncturedCotangent) :
    0 < dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p := by
  let g : LinearMap.BilinForm ℝ (TangentSpace Model p.1) :=
    LinearMap.mk₂ ℝ (fun u v => r.inner p.1 u v)
      (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])
  let b := coordinateBasis.map
    ((trivializationAt CoordinateSpace (TangentSpace Model) p.1).continuousLinearEquivAt ℝ
      p.1 (mem_chart_source CoordinateSpace p.1)).symm.toLinearEquiv
  let h := GlobalLeviCivita.inner_nondegenerate r p.1
  let v := sharp (g) h b p.2.toLinearMap
  have hv : v ≠ 0 := by
    intro hz
    apply hp
    ext U
    have hq := sharp_lower (g) h b p.2.toLinearMap U
    change r.inner p.1 v U = p.2 U at hq
    rw [hz] at hq
    simpa using hq.symm
  have he : r.inner p.1 v v = p.2 v :=
    sharp_lower (g) h b p.2.toLinearMap v
  change 0 < p.2 v
  rw [← he]
  exact r.pos p.1 v hv

theorem cotangentNorm_pos (r : Metric (M := M)) {p : CotangentBundle M} (hp : p ∈ puncturedCotangent) :
    0 < cotangentNorm r p :=
  Real.sqrt_pos.mpr (auxiliary_dualEnergy_pos r hp)

theorem cotangentNorm_sq (r : Metric (M := M)) {p : CotangentBundle M} (hp : p ∈ puncturedCotangent) :
    (cotangentNorm r p)^2 = dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p :=
  Real.sq_sqrt (auxiliary_dualEnergy_pos r hp).le

theorem contMDiffOn_cotangentNorm (r : Metric (M := M)) :
    ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ (cotangentNorm r) puncturedCotangent := by
  intro p hp
  have hde := contMDiff_dualEnergy r.inner (ManifoldBilinear.isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) r.symm
  have hs := (Real.contDiffAt_sqrt (n := ∞) (auxiliary_dualEnergy_pos r hp).ne').contMDiffAt
  exact hs.comp_contMDiffWithinAt p (hde.contMDiffAt.contMDiffWithinAt)

theorem cotangentNorm_scale (r : Metric (M := M)) (p : CotangentBundle M) {t : ℝ} (ht : 0 < t) :
    cotangentNorm r (cotangentScale t p) = t * cotangentNorm r p := by
  simp only [cotangentNorm, dualEnergy_cotangentScale, Real.sqrt_mul (sq_nonneg t),
    Real.sqrt_sq_eq_abs, abs_of_pos ht]

theorem cotangentScale_mul (p : CotangentBundle M) (s t : ℝ) :
    cotangentScale s (cotangentScale t p) = cotangentScale (s * t) p := by
  cases p
  simp [cotangentScale, smul_smul]

theorem cotangentScale_one (p : CotangentBundle M) : cotangentScale 1 p = p := by
  cases p
  simp [cotangentScale]

/-- Positive-ray normalization in the actual auxiliary sphere bundle. -/
def cotangentNormalize (r : Metric (M := M)) (p : CotangentBundle M) : CotangentBundle M :=
  cotangentScale (cotangentNorm r p)⁻¹ p

theorem cotangentNormalize_projection (r : Metric (M := M)) (p : CotangentBundle M) :
    (cotangentNormalize r p).1 = p.1 := rfl

theorem contMDiffOn_cotangentNormalize (r : Metric (M := M)) :
    ContMDiffOn CotangentModelWithCorners CotangentModelWithCorners ∞
      (cotangentNormalize r) puncturedCotangent :=
  contMDiff_cotangentScale.comp_contMDiffOn
    (((contMDiffOn_cotangentNorm r).inv₀
      (fun _ hp ↦ (cotangentNorm_pos r hp).ne')).prodMk contMDiffOn_id)

theorem cotangentNormalize_scale (r : Metric (M := M)) {p : CotangentBundle M}
    (hp : p ∈ puncturedCotangent) {t : ℝ} (ht : 0 < t) :
    cotangentNormalize r (cotangentScale t p) = cotangentNormalize r p := by
  rw [cotangentNormalize, cotangentNorm_scale r p ht, cotangentScale_mul, cotangentNormalize]
  congr 1
  field_simp [(cotangentNorm_pos r hp).ne', ht.ne']

theorem cotangentNormalize_auxiliary_square (r : Metric (M := M)) {p : CotangentBundle M}
    (hp : p ∈ puncturedCotangent) :
    dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) (cotangentNormalize r p) = 1 := by
  rw [cotangentNormalize, dualEnergy_cotangentScale, ← cotangentNorm_sq r hp, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero _ (cotangentNorm_pos r hp).ne')

theorem cotangentNormalize_of_auxiliary_one (r : Metric (M := M)) (p : CotangentBundle M)
    (hp : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p = 1) :
    cotangentNormalize r p = p := by
  simp only [cotangentNormalize, cotangentNorm, hp, Real.sqrt_one, inv_one, cotangentScale_one]

theorem cotangentNormalize_mem_unitNull (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) {p : CotangentBundle M}
    (hp : p ∈ puncturedCotangent) (hn : dualEnergy g hgn p = 0) :
    cotangentNormalize r p ∈ cotangentUnitNull r g hgn := by
  refine ⟨cotangentNormalize_auxiliary_square r hp, ?_⟩
  simp only [cotangentNormalize, dualEnergy_cotangentScale, hn, mul_zero]

def degreeOneRadialExtension (r : Metric (M := M)) (f : CotangentBundle M → ℝ)
    (p : CotangentBundle M) : ℝ :=
  cotangentNorm r p * f (cotangentNormalize r p)

theorem degreeOneRadialExtension_smooth (r : Metric (M := M)) (f : CotangentBundle M → ℝ)
    (hf : ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ f) :
    ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ (degreeOneRadialExtension r f) puncturedCotangent :=
  (contMDiffOn_cotangentNorm r).mul (hf.comp_contMDiffOn (contMDiffOn_cotangentNormalize r))

theorem degreeOneRadialExtension_scale (r : Metric (M := M)) (f : CotangentBundle M → ℝ)
    {p : CotangentBundle M} (hp : p ∈ puncturedCotangent) {t : ℝ} (ht : 0 < t) :
    degreeOneRadialExtension r f (cotangentScale t p) = t * degreeOneRadialExtension r f p := by
  simp only [degreeOneRadialExtension, cotangentNorm_scale r p ht, cotangentNormalize_scale r hp ht, mul_assoc]

theorem degreeOneRadialExtension_of_auxiliary_one (r : Metric (M := M))
    (f : CotangentBundle M → ℝ) (p : CotangentBundle M)
    (hp : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p = 1) :
    degreeOneRadialExtension r f p = f p := by
  simp only [degreeOneRadialExtension, cotangentNormalize_of_auxiliary_one r p hp,
    cotangentNorm, hp, Real.sqrt_one, one_mul]

theorem degreeOneRadialExtension_tsupport (r : Metric (M := M)) (f : CotangentBundle M → ℝ)
    {K : Set M} (hK : IsClosed K) (hF : tsupport f ⊆ (fun p => p.1) ⁻¹' K) :
    tsupport (degreeOneRadialExtension r f) ⊆ (fun p => p.1) ⁻¹' K := by
  refine closure_minimal (fun p hp ↦ ?_) (hK.preimage continuous_cotangent_projection)
  change cotangentNorm r p * f (cotangentNormalize r p) ≠ 0 at hp
  change p.1 ∈ K
  exact hF (a := cotangentNormalize r p) (subset_tsupport f (right_ne_zero_of_mul hp))

theorem actual_weightedTrace_degreeOne_extension [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (b s : CotangentBundle M → ℝ)
    (hb : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent)
    (hcompact : HasCompactSupport (fun p : puncturedCotangent (M := M) => b p.1))
    (hs : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s (cotangentUnitNull r g hgn))
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p) :
    ∃ K : Set M, IsCompact K ∧ ∃ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent ∧
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) ∧
      (∀ p ∈ puncturedCotangent, dualEnergy g hgn p = 0 →
        a p = cotangentNorm r p * intrinsicWeightedTrace b s (cotangentNormalize r p)) ∧
      tsupport a ⊆ (fun p => p.1) ⁻¹' K := by
  obtain ⟨K, hK, f, hf, hF, hS⟩ :=
    actual_weightedTrace_angular_extension r g hg hgn hgs b s hb hcompact hs hpos
  refine ⟨K, hK, degreeOneRadialExtension r f, degreeOneRadialExtension_smooth r f hf,
    fun p hp t ht ↦ degreeOneRadialExtension_scale r f hp ht, ?_,
    degreeOneRadialExtension_tsupport r f hK.isClosed hS⟩
  intro p hp hn
  unfold degreeOneRadialExtension
  rw [hF (cotangentNormalize_mem_unitNull r g hgn hp hn)]

end Burnett.Geometry.CotangentAngularExtension
