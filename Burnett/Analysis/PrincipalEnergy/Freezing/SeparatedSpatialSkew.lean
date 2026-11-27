import Burnett.Analysis.PrincipalEnergy.Freezing.SkewDerivativePlacement
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory
open scoped ComplexConjugate ContDiff ENNReal

/-- The actual separated test in the freezing argument. Both occurrences of
the multiplier use the same radian Fourier action and the same real profile. -/
def separatedSkewAction (f : SchwartzMap E ℂ) (b : E → ℝ) (u : SchwartzMap E ℂ)
    (x : E) : ℂ :=
  (f x * radianSkewAction b u x + radianSkewAction b (energyProduct f u) x) / 2

/-- The actual commutator of the separated test with scalar multiplication. -/
def separatedSkewCommutator (f : SchwartzMap E ℂ) (b : E → ℝ) (R u : SchwartzMap E ℂ)
    (x : E) : ℂ :=
  separatedSkewAction f b (energyProduct R u) x - R x * separatedSkewAction f b u x

theorem separatedSkewAction_preserves_real (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hf : ∀ x, conj (f x) = f x) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (u : SchwartzMap E ℂ) (hu : ∀ x, conj (u x) = u x) (x : E) :
    conj (separatedSkewAction f b u x) = separatedSkewAction f b u x := by
  have hProduct (y : E) : conj (energyProduct f u y) = energyProduct f u y := by
    simp only [energyProduct_apply, map_mul, hf, hu]
  simp only [separatedSkewAction, map_div₀, map_add, map_mul, map_ofNat, hf,
    radianSkewAction_preserves_real b hodd u hu,
    radianSkewAction_preserves_real b hodd (energyProduct f u) hProduct]

private theorem skewAction_memLp_two (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (u : SchwartzMap E ℂ) : MemLp (radianSkewAction b u) 2 volume := by
  obtain ⟨_, _, estimate⟩ := radian_degree_one_gradient_bound 2 (by norm_num) b hb hom
  have hU : MemLp (radianAction b u) 2 volume := by simpa using (estimate u).1
  exact hU.const_mul (-Complex.I)

private theorem conj_memLp_two {g : E → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun x => conj (g x)) 2 volume :=
  hg.mono (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
    (Filter.Eventually.of_forall fun x => by simp)

/-- The original separated action has finite L² norm on actual Schwartz
inputs, so both pairings below are genuine integrable products. -/
theorem separatedSkewAction_memLp_two (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (u : SchwartzMap E ℂ) : MemLp (separatedSkewAction f b u) 2 volume := by
  have hFirst : MemLp (fun x => f x * radianSkewAction b u x) 2 volume :=
    (skewAction_memLp_two b hb hom u).mul' (f.memLp ⊤ volume)
  have hSum := hFirst.add (skewAction_memLp_two b hb hom (energyProduct f u))
  simpa only [separatedSkewAction, Pi.add_apply, div_eq_mul_inv] using hSum.mul_const (2 : ℂ)⁻¹

/-- Skewness in the Hermitian test pairing, linear in the first slot. -/
theorem separatedSkewAction_skew_adjoint (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hf : ∀ x, conj (f x) = f x) (u v : SchwartzMap E ℂ) :
    (∫ x, separatedSkewAction f b u x * conj (v x)) =
      -∫ x, u x * conj (separatedSkewAction f b v x) := by
  let U := energyProduct f u
  let V := energyProduct f v
  have hFirst : Integrable (fun x => radianSkewAction b u x * conj (V x)) :=
    (skewAction_memLp_two b hb hom u).integrable_mul (conj_memLp_two (V.memLp 2 volume))
  have hSecond : Integrable (fun x => radianSkewAction b U x * conj (v x)) :=
    (skewAction_memLp_two b hb hom U).integrable_mul (conj_memLp_two (v.memLp 2 volume))
  have hThird : Integrable (fun x => u x * conj (radianSkewAction b V x)) :=
    (u.memLp 2 volume).integrable_mul (conj_memLp_two (skewAction_memLp_two b hb hom V))
  have hFourth : Integrable (fun x => U x * conj (radianSkewAction b v x)) :=
    (U.memLp 2 volume).integrable_mul (conj_memLp_two (skewAction_memLp_two b hb hom v))
  calc
    _ = ((∫ x, radianSkewAction b u x * conj (V x)) +
        (∫ x, radianSkewAction b U x * conj (v x))) / 2 := by
      have hPoint : (fun x => separatedSkewAction f b u x * conj (v x)) =
          fun x => (radianSkewAction b u x * conj (V x) +
            radianSkewAction b U x * conj (v x)) / 2 := by
        funext x
        simp only [separatedSkewAction, U, V, energyProduct_apply, map_mul, hf]
        ring
      rw [hPoint, integral_div, integral_add hFirst hSecond]
    _ = -(((∫ x, u x * conj (radianSkewAction b V x)) +
        (∫ x, U x * conj (radianSkewAction b v x))) / 2) := by
      rw [radianSkewAction_skew_adjoint b hb hom u V, radianSkewAction_skew_adjoint b hb hom U v]
      ring
    _ = _ := by
      have hPoint : (fun x => u x * conj (separatedSkewAction f b v x)) =
          fun x => (u x * conj (radianSkewAction b V x) +
            U x * conj (radianSkewAction b v x)) / 2 := by
        funext x
        simp only [separatedSkewAction, U, V, energyProduct_apply, map_div₀, map_add,
          map_mul, hf, map_ofNat]
        ring
      rw [hPoint, integral_div, integral_add hThird hFourth]

/-- The real bilinear pairing used to exchange the two derivative slots. -/
theorem separatedSkewAction_real_pairing (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (hf : ∀ x, conj (f x) = f x) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (u v : SchwartzMap E ℂ) (hv : ∀ x, conj (v x) = v x) :
    (∫ x, separatedSkewAction f b u x * v x) =
      -∫ x, u x * separatedSkewAction f b v x := by
  simpa only [hv, separatedSkewAction_preserves_real f b hf hodd v hv] using
    separatedSkewAction_skew_adjoint f b hb hom hf u v

/-- The exact physical identity for the coefficient commutator. In each slot,
the skew multiplier commutator is the actual radian commutator times -i. -/
theorem separatedSkewCommutator_eq_radian (f : SchwartzMap E ℂ) (b : E → ℝ)
    (R u : SchwartzMap E ℂ) (x : E) :
    separatedSkewCommutator f b R u x =
      (f x * (-Complex.I * radianCommutator b R u x) +
        (-Complex.I * radianCommutator b R (energyProduct f u) x)) / 2 := by
  have hProduct : energyProduct f (energyProduct R u) = energyProduct R (energyProduct f u) := by
    ext y
    simp only [energyProduct_apply]
    ring
  have hComm (v : SchwartzMap E ℂ) : radianCommutator b R v x =
      radianAction b (energyProduct R v) x - R x * radianAction b v x := rfl
  simp only [separatedSkewCommutator, separatedSkewAction, radianSkewAction, hProduct, hComm]
  ring

end Burnett.A02.FrequencySplit
