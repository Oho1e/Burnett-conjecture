import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicCompleteness

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.A06

open Metric MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private def sphereRotationCLM (i j : Fin 4) : RotationSpace →L[ℝ] RotationSpace :=
  (EuclideanSpace.proj i).smulRight (EuclideanSpace.single j 1) -
    (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1)

theorem contDiff_planeRotationDerivative {n : WithTop ℕ∞} {f : RotationSpace → ℝ}
    (hf : ContDiff ℝ (n + 1) f) (i j : Fin 4) :
    ContDiff ℝ n (planeRotationDerivative i j f) := by
  have hg : ContDiff ℝ n (sphereRotationCLM i j) := (sphereRotationCLM i j).contDiff
  have h : planeRotationDerivative i j f = fun x => fderiv ℝ f x (sphereRotationCLM i j x) := by
    funext x
    rw [planeRotationDerivative, planeRotationGenerator_eq]
    rfl
  rw [h]
  exact (hf.fderiv_right le_rfl).clm_apply hg

private theorem contDiff_planeRotationCasimir {n : WithTop ℕ∞} {f : RotationSpace → ℝ}
    (hf : ContDiff ℝ (n + 2) f) : ContDiff ℝ n (planeRotationCasimir f) := by
  unfold planeRotationCasimir
  apply ContDiff.sum
  intro p _
  have h : ContDiff ℝ ((n + 1) + 1) f := by simpa only [add_assoc, one_add_one_eq_two] using hf
  exact contDiff_planeRotationDerivative (contDiff_planeRotationDerivative h p.1 p.2) p.1 p.2

private theorem integrable_round_sphere_product {f g : RotationSpace → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x : RoundSphere3 => f x * g x) roundSphere3Measure :=
  ((hf.mul hg).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual sphere Casimir is symmetric on restrictions of ambient C² tests. -/
theorem integral_planeRotationCasimir_mul {f g : RotationSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x : RoundSphere3, planeRotationCasimir f x * g x ∂roundSphere3Measure) =
      ∫ x : RoundSphere3, f x * planeRotationCasimir g x ∂roundSphere3Measure := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg₁ : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have df (p : Fin 4 × Fin 4) : ContDiff ℝ 1 (planeRotationDerivative p.1 p.2 f) :=
    contDiff_planeRotationDerivative (by simpa only [one_add_one_eq_two] using hf) p.1 p.2
  have dg (p : Fin 4 × Fin 4) : ContDiff ℝ 1 (planeRotationDerivative p.1 p.2 g) :=
    contDiff_planeRotationDerivative (by simpa only [one_add_one_eq_two] using hg) p.1 p.2
  let L (p : Fin 4 × Fin 4) (x : RoundSphere3) :=
    planeRotationDerivative p.1 p.2 (planeRotationDerivative p.1 p.2 f) x * g x
  let R (p : Fin 4 × Fin 4) (x : RoundSphere3) :=
    f x * planeRotationDerivative p.1 p.2 (planeRotationDerivative p.1 p.2 g) x
  have hL (p : Fin 4 × Fin 4) : Integrable (L p) roundSphere3Measure :=
    integrable_round_sphere_product (continuous_planeRotationDerivative _ _ (df p)) hg.continuous
  have hR (p : Fin 4 × Fin 4) : Integrable (R p) roundSphere3Measure :=
    integrable_round_sphere_product hf.continuous (continuous_planeRotationDerivative _ _ (dg p))
  calc
    _ = ∫ x, ∑ p ∈ rotationPairs, L p x ∂roundSphere3Measure := by
      simp only [planeRotationCasimir, Finset.sum_mul, L]
    _ = ∑ p ∈ rotationPairs, ∫ x, L p x ∂roundSphere3Measure :=
      integral_finset_sum _ fun p _ => hL p
    _ = ∑ p ∈ rotationPairs, ∫ x, R p x ∂roundSphere3Measure := by
      apply Finset.sum_congr rfl
      intro p hp
      have hn : p.1 ≠ p.2 := ne_of_lt ((mem_rotationPairs p.1 p.2).mp hp)
      have left := integral_planeRotationDerivative_mul hn (df p) hg₁
      have right := integral_planeRotationDerivative_mul hn hf₁ (dg p)
      simp only [L, R, left, right, neg_neg]
    _ = ∫ x, ∑ p ∈ rotationPairs, R p x ∂roundSphere3Measure :=
      (integral_finset_sum _ fun p _ => hR p).symm
    _ = _ := by simp only [planeRotationCasimir, Finset.mul_sum, R]

/-- The restriction of I minus the actual sum of the six squares. -/
def roundShiftCasimir (f : RotationSpace → ℝ) (x : RotationSpace) : ℝ :=
  f x - planeRotationCasimir f x

def roundShiftCasimirPower : ℕ → (RotationSpace → ℝ) → RotationSpace → ℝ
  | 0, f => f
  | n + 1, f => roundShiftCasimir (roundShiftCasimirPower n f)

theorem roundShiftCasimirPower_contDiff {f : RotationSpace → ℝ} (n k : ℕ)
    (hf : ContDiff ℝ (k + 2 * n : ℕ) f) : ContDiff ℝ k (roundShiftCasimirPower n f) := by
  induction n generalizing k with
  | zero => simpa only [Nat.mul_zero, Nat.add_zero, roundShiftCasimirPower] using hf
  | succ n ih =>
    have hsame : k + 2 + 2 * n = k + 2 * (n + 1) := by omega
    have h : ContDiff ℝ (k + 2 + 2 * n : ℕ) f := by rwa [hsame]
    have hg : ContDiff ℝ ((k : WithTop ℕ∞) + 2) (roundShiftCasimirPower n f) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using ih (k + 2) h
    have h₀ : ContDiff ℝ k (roundShiftCasimirPower n f) := hg.of_le (by exact le_add_of_nonneg_right (by norm_num))
    change ContDiff ℝ k (fun x => roundShiftCasimirPower n f x - planeRotationCasimir (roundShiftCasimirPower n f) x)
    exact h₀.sub (contDiff_planeRotationCasimir hg)

/-- Transfer one copy of I−Δ to the harmonic using the actual integral. -/
theorem integral_roundShiftCasimir_mul_harmonic {f : RotationSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (i : SphereHarmonicIndex) :
    (∫ x : RoundSphere3, roundShiftCasimir f x * sphereHarmonicFamily i x ∂roundSphere3Measure) =
      ((i.1 : ℝ) + 1)^2 *
        ∫ x : RoundSphere3, f x * sphereHarmonicFamily i x ∂roundSphere3Measure := by
  let P := ((sphereHarmonicPolynomialBasis i.1 i.2 : SphereHomogeneous i.1) : SpherePolynomial)
  let g := spherePolynomialValue P
  have hg : ContDiff ℝ 2 g := contDiff_infty.mp (spherePolynomialValue_contDiff P) 2
  have hC (x : RoundSphere3) : f x * planeRotationCasimir g x =
      (-((i.1 : ℝ) * ((i.1 : ℝ) + 2))) * (f x * g x) := by
    rw [sphereHarmonicBasisFunction_casimir i.1 i.2 x]
    change f x * (-((i.1 : ℝ) * ((i.1 : ℝ) + 2)) * g x) = _
    ring
  change (∫ x : RoundSphere3, (f x - planeRotationCasimir f x) * g x ∂roundSphere3Measure) =
      ((i.1 : ℝ) + 1)^2 * ∫ x : RoundSphere3, f x * g x ∂roundSphere3Measure
  simp only [sub_mul]
  rw [integral_sub (integrable_round_sphere_product hf.continuous hg.continuous)
      (integrable_round_sphere_product (contDiff_planeRotationCasimir (n := 0) hf).continuous hg.continuous),
    integral_planeRotationCasimir_mul hf hg]
  simp only [hC, integral_const_mul]
  ring

/-- Exact identity after repeatedly moving I−Δ across the actual sphere pairing. -/
theorem integral_roundShiftCasimirPower_mul_harmonic {f : RotationSpace → ℝ}
    (n : ℕ) (hf : ContDiff ℝ (2 * n : ℕ) f) (i : SphereHarmonicIndex) :
    (∫ x : RoundSphere3, roundShiftCasimirPower n f x * sphereHarmonicFamily i x ∂roundSphere3Measure) =
      (((i.1 : ℝ) + 1)^2)^n *
        ∫ x : RoundSphere3, f x * sphereHarmonicFamily i x ∂roundSphere3Measure := by
  induction n with
  | zero => simp [roundShiftCasimirPower]
  | succ n ih =>
    have heq : 2 + 2 * n = 2 * (n + 1) := by omega
    have hr : ContDiff ℝ (2 + 2 * n : ℕ) f := by rwa [heq]
    have h : ContDiff ℝ 2 (roundShiftCasimirPower n f) := roundShiftCasimirPower_contDiff n 2 hr
    have hf' : ContDiff ℝ (2 * n : ℕ) f := hf.of_le (by exact_mod_cast show 2 * n ≤ 2 * (n + 1) by omega)
    rw [roundShiftCasimirPower, integral_roundShiftCasimir_mul_harmonic h, ih hf',
      pow_succ' (((i.1 : ℝ) + 1)^2) n, mul_assoc]

/-- The actual restriction of (I−Δ)^6 applied to a real C¹² angular test. -/
def roundShiftCasimirSixOnSphere {f : RotationSpace → ℝ} (hf : ContDiff ℝ 12 f) :
    C(RoundSphere3, ℝ) :=
  ⟨fun x => roundShiftCasimirPower 6 f x,
    (roundShiftCasimirPower_contDiff 6 0 hf).continuous.comp continuous_subtype_val⟩

/-- The actual coefficient decays by precisely (d+1)⁻¹² against the L² norm
of the actual (I−Δ)^6 applied to the angular slice. -/
theorem norm_roundSphereHarmonicCoefficient_le {f : RotationSpace → ℝ} (hf : ContDiff ℝ 12 f)
    (i : SphereHarmonicIndex) :
    ‖∫ x : RoundSphere3, f x * sphereHarmonicFamily i x ∂roundSphere3Measure‖ ≤
      (((i.1 : ℝ) + 1)^12)⁻¹ *
        ‖ContinuousMap.toLp 2 roundSphere3Measure ℝ (roundShiftCasimirSixOnSphere hf)‖ := by
  let F := ContinuousMap.toLp 2 roundSphere3Measure ℝ (roundShiftCasimirSixOnSphere hf)
  have hn : ‖sphereHarmonicFamilyLp i‖ = 1 := sphereHarmonicFamilyLp_orthonormal.norm_eq_one i
  have hcs : ‖inner ℝ (sphereHarmonicFamilyLp i) F‖ ≤ ‖F‖ := by
    simpa only [hn, one_mul] using (norm_inner_le_norm (𝕜 := ℝ) (sphereHarmonicFamilyLp i) F)
  have hp := roundSphereHarmonicHilbertBasis_repr_apply (roundShiftCasimirSixOnSphere hf) i
  rw [HilbertBasis.repr_apply_apply, roundSphereHarmonicHilbertBasis_apply] at hp
  change inner ℝ (sphereHarmonicFamilyLp i) F =
    ∫ x : RoundSphere3, roundShiftCasimirPower 6 f x * sphereHarmonicFamily i x ∂roundSphere3Measure at hp
  rw [hp, integral_roundShiftCasimirPower_mul_harmonic 6 hf, ← pow_mul, norm_mul] at hcs
  have hpos : 0 < ((i.1 : ℝ) + 1)^12 := by positivity
  rw [Real.norm_of_nonneg hpos.le] at hcs
  calc
    _ = (((i.1 : ℝ) + 1)^12)⁻¹ *
          (((i.1 : ℝ) + 1)^12 * ‖∫ x : RoundSphere3, f x * sphereHarmonicFamily i x ∂roundSphere3Measure‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcs (by positivity)

end Burnett.A06
