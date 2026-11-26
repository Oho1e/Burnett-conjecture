import Burnett.Analysis.CubicEnergy.AngularHarmonics.SpherePolynomialRestriction
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 6800000

noncomputable section

namespace Burnett.A06

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _

local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Nonempty open patches of the actual sphere measure contain the directions
of a nonempty open cone in the four-dimensional Haar volume. -/
instance roundSphere3Measure_isOpenPosMeasure : roundSphere3Measure.IsOpenPosMeasure where
  open_pos U hU hUne := by
    let r : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
    let half : Ioi (0 : ℝ) := ⟨(1/2 : ℝ), by norm_num⟩
    let h := homeomorphUnitSphereProd RotationSpace
    let W := h ⁻¹' (U ×ˢ Iio r)
    let cone := ((↑) : ({(0 : RotationSpace)}ᶜ : Set RotationSpace) → RotationSpace) '' W
    have hW : IsOpen W := (hU.prod isOpen_Iio).preimage h.continuous
    have hc : IsOpen cone := isOpen_compl_singleton.isOpenMap_subtype_val W hW
    obtain ⟨x, hx⟩ := hUne
    have hhalf : half ∈ Iio r := by
      change (1/2 : ℝ) < 1
      norm_num
    have hpoint : h.symm (x, half) ∈ W := by
      change h (h.symm (x, half)) ∈ U ×ˢ Iio r
      rw [h.apply_symm_apply]
      exact ⟨hx, hhalf⟩
    have hn : cone.Nonempty := ⟨_, mem_image_of_mem _ hpoint⟩
    have hm := hc.measure_ne_zero (volume : Measure RotationSpace) hn
    change (volume : Measure RotationSpace).toSphere U ≠ 0
    rw [Measure.toSphere_apply' _ hU.measurableSet,
      ← (volume : Measure RotationSpace).toSphere_apply_aux U r]
    exact mul_ne_zero (by simp) hm

abbrev RoundSphereL2 := Lp ℝ 2 roundSphere3Measure

/-- Restrict the same harmonic polynomial to the actual sphere and take its L² class. -/
def sphereHarmonicToLp (d : ℕ) : sphereHarmonicSubmodule d →ₗ[ℝ] RoundSphereL2 :=
  (ContinuousMap.toLp 2 roundSphere3Measure ℝ).toLinearMap.comp
    ((sphereHomogeneousRestriction d).comp (sphereHarmonicSubmodule d).subtype)

theorem sphereHarmonicToLp_ae_eval (d : ℕ) (P : sphereHarmonicSubmodule d) :
    (sphereHarmonicToLp d P : RoundSphere3 → ℝ) =ᵐ[roundSphere3Measure]
      fun x => spherePolynomialValue ((P : SphereHomogeneous d) : SpherePolynomial) x :=
  (sphereHomogeneousRestriction d P.val).coeFn_toLp (p := 2) (𝕜 := ℝ) roundSphere3Measure

theorem sphereHarmonicToLp_injective (d : ℕ) : Function.Injective (sphereHarmonicToLp d) :=
  (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) roundSphere3Measure).comp
    ((sphereHomogeneousRestriction_injective d).comp Subtype.val_injective)

def sphereHarmonicLpRange (d : ℕ) : Submodule ℝ RoundSphereL2 :=
  LinearMap.range (sphereHarmonicToLp d)

def sphereHarmonicLpEquiv (d : ℕ) : sphereHarmonicSubmodule d ≃ₗ[ℝ] sphereHarmonicLpRange d :=
  LinearEquiv.ofInjective (sphereHarmonicToLp d) (sphereHarmonicToLp_injective d)

theorem sphereHarmonicLpRange_finrank (d : ℕ) :
    Module.finrank ℝ (sphereHarmonicLpRange d) = (d + 1)^2 :=
  (sphereHarmonicLpEquiv d).finrank_eq.symm.trans (sphereHarmonic_finrank d)

instance sphereHarmonicLpRange_finiteDimensional (d : ℕ) :
    FiniteDimensional ℝ (sphereHarmonicLpRange d) := by
  apply FiniteDimensional.of_finrank_pos
  rw [sphereHarmonicLpRange_finrank]
  positivity

/-- An orthonormal basis of the actual degree-d real harmonic L² subspace. -/
def sphereHarmonicLpOrthonormalBasis (d : ℕ) :
    OrthonormalBasis (Fin ((d + 1)^2)) ℝ (sphereHarmonicLpRange d) :=
  (stdOrthonormalBasis ℝ (sphereHarmonicLpRange d)).reindex
    (finCongr (sphereHarmonicLpRange_finrank d))

def sphereHarmonicPolynomialBasis (d : ℕ) :
    Module.Basis (Fin ((d + 1)^2)) ℝ (sphereHarmonicSubmodule d) :=
  (sphereHarmonicLpOrthonormalBasis d).toBasis.map (sphereHarmonicLpEquiv d).symm

/-- The actual continuous representatives of the harmonics in the L² basis. -/
def sphereHarmonicBasisFunction (d : ℕ) (i : Fin ((d + 1)^2)) : C(RoundSphere3, ℝ) :=
  sphereHomogeneousRestriction d (sphereHarmonicPolynomialBasis d i : SphereHomogeneous d)

theorem sphereHarmonicBasisFunction_toLp (d : ℕ) (i : Fin ((d + 1)^2)) :
    ContinuousMap.toLp 2 roundSphere3Measure ℝ (sphereHarmonicBasisFunction d i) =
      (sphereHarmonicLpOrthonormalBasis d i : RoundSphereL2) := by
  change ((sphereHarmonicLpEquiv d) (sphereHarmonicPolynomialBasis d i) : RoundSphereL2) = _
  simp only [sphereHarmonicPolynomialBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
    LinearEquiv.apply_symm_apply]

theorem sphereHarmonicBasisFunction_integral_mul (d : ℕ) (i j : Fin ((d + 1)^2)) :
    (∫ x, sphereHarmonicBasisFunction d i x * sphereHarmonicBasisFunction d j x
      ∂roundSphere3Measure) = if i = j then 1 else 0 := by
  have eq := (sphereHarmonicLpOrthonormalBasis d).inner_eq_ite i j
  change inner ℝ (sphereHarmonicLpOrthonormalBasis d i : RoundSphereL2)
    (sphereHarmonicLpOrthonormalBasis d j : RoundSphereL2) = _ at eq
  rw [← sphereHarmonicBasisFunction_toLp, ← sphereHarmonicBasisFunction_toLp,
    ContinuousMap.inner_toLp] at eq
  simpa [mul_comm] using eq

end Burnett.A06
