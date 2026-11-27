import Burnett.Analysis.SpatialFreezing.FixedCubeFourier
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedRescaledSymbolJets
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ComplexConjugate RealInnerProductSpace BigOperators

/-- Fourier coefficients of the actual real spatial profile. -/
def spatialRealProfileCoefficient (P : ℝ) (k : Index → ℤ)
    (f : CoordinateSpace → ℝ) : ℂ :=
  spatialCubeFourierCoefficient P k (fun y => (f y : ℂ))

def spatialCosineCoefficient (P : ℝ) (k : Index → ℤ) (f : CoordinateSpace → ℝ) : ℝ :=
  2 * (spatialRealProfileCoefficient P k f).re

def spatialSineCoefficient (P : ℝ) (k : Index → ℤ) (f : CoordinateSpace → ℝ) : ℝ :=
  -2 * (spatialRealProfileCoefficient P k f).im

private theorem frequency_neg (P : ℝ) (k : Index → ℤ) :
    spatialModeFrequency P (-k) = -spatialModeFrequency P k := by
  ext j
  change (2 * P)⁻¹ * ((-k j : ℤ) : ℝ) = -((2 * P)⁻¹ * (k j : ℝ))
  rw [Int.cast_neg, mul_neg]

private theorem phase_neg (P : ℝ) (k : Index → ℤ) (y : CoordinateSpace) :
    spatialModePhase P (-k) y = -spatialModePhase P k y := by
  simp only [spatialModePhase, frequency_neg, inner_neg_right, mul_neg]

/-- Reality of the input gives conjugation of the actual reflected mode. -/
theorem spatial_real_profile_coefficient_reflection (P : ℝ) (k : Index → ℤ)
    (f : CoordinateSpace → ℝ) :
    spatialRealProfileCoefficient P (-k) f = conj (spatialRealProfileCoefficient P k f) := by
  simp only [spatialRealProfileCoefficient, spatialCubeFourierCoefficient, phase_neg, neg_neg,
    Complex.real_smul, map_mul, Complex.conj_ofReal, ← integral_conj, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.ofReal_neg,
    map_neg, Complex.conj_I, neg_mul, mul_neg, neg_neg]

private theorem real_mode_pair (P : ℝ) (k : Index → ℤ) (f : CoordinateSpace → ℝ)
    (y : CoordinateSpace) :
    spatialRealProfileCoefficient P k f * Complex.exp ((spatialModePhase P k y : ℂ) * Complex.I) +
      spatialRealProfileCoefficient P (-k) f * Complex.exp ((spatialModePhase P (-k) y : ℂ) * Complex.I) =
      (spatialCosineCoefficient P k f * Real.cos (spatialModePhase P k y) +
        spatialSineCoefficient P k f * Real.sin (spatialModePhase P k y) : ℝ) := by
  rw [spatial_real_profile_coefficient_reflection, phase_neg]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_re, spatialCosineCoefficient, spatialSineCoefficient]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_im]
    ring

/-- The real finite sum has one constant mode and one cosine and sine for
each selected nonzero reflected pair. -/
def spatialRealFourierPartialSum (P : ℝ) (K : Finset (Index → ℤ))
    (f : CoordinateSpace → ℝ) (y : CoordinateSpace) : ℝ :=
  (spatialRealProfileCoefficient P 0 f).re +
    ∑ k ∈ K, (spatialCosineCoefficient P k f * Real.cos (spatialModePhase P k y) +
      spatialSineCoefficient P k f * Real.sin (spatialModePhase P k y))

/-- The real finite expansion equals the complex Fourier sum over the same
zero mode and both sides of each selected sign pair. -/
theorem spatial_real_fourier_partial_sum_eq (P : ℝ) (K : Finset (Index → ℤ))
    (hZero : 0 ∉ K) (hDisjoint : Disjoint K (K.image fun k => -k))
    (f : CoordinateSpace → ℝ) (y : CoordinateSpace) :
    (spatialRealFourierPartialSum P K f y : ℂ) =
      ∑ k ∈ insert 0 (K ∪ K.image fun k => -k),
        spatialRealProfileCoefficient P k f * Complex.exp ((spatialModePhase P k y : ℂ) * Complex.I) := by
  classical
  let W (k : Index → ℤ) := spatialRealProfileCoefficient P k f *
    Complex.exp ((spatialModePhase P k y : ℂ) * Complex.I)
  have absent : 0 ∉ K ∪ K.image (fun k => -k) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hZero h
    · obtain ⟨k, hk, eq⟩ := Finset.mem_image.mp h
      exact hZero (by simpa only [neg_eq_zero.mp eq] using hk)
  have zeroPhase : spatialModePhase P 0 y = 0 := by
    have hL : spatialLatticeVector (0 : Index → ℤ) = 0 := by ext j; simp [spatialLatticeVector]
    simp [spatialModePhase, spatialModeFrequency, hL]
  have zeroMode : W 0 = ((spatialRealProfileCoefficient P 0 f).re : ℂ) := by
    have reflected := spatial_real_profile_coefficient_reflection P (0 : Index → ℤ) f
    have h := congrArg Complex.im reflected
    simp only [neg_zero, Complex.conj_im] at h
    simp only [W, zeroPhase, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      linarith
  change (spatialRealFourierPartialSum P K f y : ℂ) = ∑ k ∈ insert 0 (K ∪ K.image fun k => -k), W k
  rw [Finset.sum_insert absent, Finset.sum_union hDisjoint, Finset.sum_image (fun _ _ _ _ eq => neg_injective eq),
    ← Finset.sum_add_distrib, zeroMode]
  unfold spatialRealFourierPartialSum
  rw [Complex.ofReal_add, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (real_mode_pair P k f y).symm

private theorem real_profile_coefficient_mul_const (P : ℝ) (k : Index → ℤ)
    (f : CoordinateSpace → ℝ) (d : ℝ) :
    spatialRealProfileCoefficient P k (fun y => d * f y) = d • spatialRealProfileCoefficient P k f := by
  simp only [spatialRealProfileCoefficient, spatialCubeFourierCoefficient,
    Complex.real_smul, Complex.ofReal_mul, smul_eq_mul]
  have move (y : CoordinateSpace) : Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I) *
      ((d : ℂ) * (f y : ℂ)) = (d : ℂ) *
        (Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I) * (f y : ℂ)) := by ring
  simp_rw [move, integral_const_mul]
  ring

/-- The complex coefficient as a function of the actual frequency variable. -/
def localizedSpatialFourierCoefficient (P : ℝ) (k : Index → ℤ)
    (χ : CoordinateSpace → ℝ) (a : CoordinateSpace → CoordinateSpace → ℝ)
    (c : CoordinateSpace) (ℓ : ℝ) (ξ : CoordinateSpace) : ℂ :=
  spatialRealProfileCoefficient P k
    (rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ)

/-- The real and imaginary parts of every spatial coefficient are odd and
positively homogeneous of degree one in the original frequency variable. -/
theorem localized_spatial_fourier_real_modes_odd_homogeneous
    (P : ℝ) (k : Index → ℤ) (χ : CoordinateSpace → ℝ)
    (a : CoordinateSpace → CoordinateSpace → ℝ) (c : CoordinateSpace) (ℓ : ℝ)
    (odd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ) :
    let b := localizedSpatialFourierCoefficient P k χ a c ℓ
    (∀ ξ, (b (-ξ)).re = -(b ξ).re ∧ (b (-ξ)).im = -(b ξ).im) ∧
    (∀ (t : ℝ), 0 < t → ∀ ξ, (b (t • ξ)).re = t * (b ξ).re ∧
      (b (t • ξ)).im = t * (b ξ).im) := by
  intro b
  have oddCoefficient (ξ : CoordinateSpace) : b (-ξ) = -b ξ := by
    have eq : rescaledLocalizedSymbolDifference χ (fun x => a x (-ξ)) c ℓ =
        fun y => (-1 : ℝ) * rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ y := by
      funext y
      simp only [rescaledLocalizedSymbolDifference, rescaledSpatialDifference, odd, smul_eq_mul]
      ring
    change spatialRealProfileCoefficient P k (rescaledLocalizedSymbolDifference χ (fun x => a x (-ξ)) c ℓ) =
      -spatialRealProfileCoefficient P k (rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ)
    rw [eq, real_profile_coefficient_mul_const, neg_one_smul]
  have homogeneous (t : ℝ) (ht : 0 < t) (ξ : CoordinateSpace) : b (t • ξ) = t • b ξ := by
    have eq : rescaledLocalizedSymbolDifference χ (fun x => a x (t • ξ)) c ℓ =
        fun y => t * rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ y := by
      funext y
      simp only [rescaledLocalizedSymbolDifference, rescaledSpatialDifference, hom _ _ ht, smul_eq_mul]
      ring
    change spatialRealProfileCoefficient P k (rescaledLocalizedSymbolDifference χ (fun x => a x (t • ξ)) c ℓ) =
      t • spatialRealProfileCoefficient P k (rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ)
    rw [eq, real_profile_coefficient_mul_const]
  refine ⟨?_, ?_⟩
  · intro ξ
    rw [oddCoefficient ξ, Complex.neg_re, Complex.neg_im]
    exact ⟨rfl, rfl⟩
  · intro t ht ξ
    rw [homogeneous t ht ξ, Complex.real_smul]
    exact ⟨by simp [Complex.mul_re], by simp [Complex.mul_im]⟩

end Burnett.A03
