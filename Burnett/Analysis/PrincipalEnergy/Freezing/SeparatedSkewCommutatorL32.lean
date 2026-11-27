import Burnett.Analysis.PrincipalEnergy.Freezing.CoefficientGradientLp
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSpatialSkew
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeRadianCommutator
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearEstimate

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory Metric Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal

/-- The two physical commutator placements both use the L³ first derivative
of the actual coefficient R and the L³ value of the test input. -/
theorem separated_skew_coefficient_commutator_L32_sphere_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f R u : SchwartzMap E ℂ,
        MemLp (separatedSkewCommutator f b R u) (ENNReal.ofReal (3 / 2)) volume ∧
        eLpNorm (separatedSkewCommutator f b R u) (ENNReal.ofReal (3 / 2)) volume ≤
          C * ENNReal.ofReal D * (eLpNorm (f : E → ℂ) ⊤ volume * energyGradientNorm R *
            eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume) := by
  obtain ⟨C, hC, estimate⟩ := radian_commutator_Lp_sphere_bound 3 3 (3 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro b hb hom D hD jet f R u
  let p := ENNReal.ofReal 3
  let q := ENNReal.ofReal (3 / 2)
  let c := C * ENNReal.ofReal D
  let F := eLpNorm (f : E → ℂ) ⊤ volume
  let G := energyGradientNorm R
  let U := eLpNorm (u : E → ℂ) p volume
  let W := c * (F * G * U)
  let T (v : SchwartzMap E ℂ) := (-Complex.I) • radianCommutator b R v
  have bound (v : SchwartzMap E ℂ) : MemLp (T v) q volume ∧
      eLpNorm (T v) q volume ≤ c * (G * eLpNorm (v : E → ℂ) p volume) := by
    obtain ⟨hasLp, estimateV⟩ := estimate b hb hom D hD jet R v
    refine ⟨hasLp.const_smul _, ?_⟩
    change eLpNorm ((-Complex.I) • radianCommutator b R v) q volume ≤ _
    have hI : ‖(-Complex.I : ℂ)‖ₑ = 1 := by
      rw [← ofReal_norm_eq_enorm, norm_neg, Complex.norm_I, ENNReal.ofReal_one]
    rw [eLpNorm_const_smul, hI, one_mul]
    exact estimateV
  let A := (f : E → ℂ) • T u
  let B := T (energyProduct f u)
  have hA : MemLp A q volume := (bound u).1.smul (f.memLp ⊤ volume)
  have hB : MemLp B q volume := (bound (energyProduct f u)).1
  have boundA : eLpNorm A q volume ≤ W := calc
    _ ≤ F * eLpNorm (T u) q volume :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm q (bound u).1.aestronglyMeasurable (f : E → ℂ)
    _ ≤ F * (c * (G * U)) := mul_le_mul_left' (bound u).2 _
    _ = _ := by dsimp only [W]; ring
  have boundB : eLpNorm B q volume ≤ W := calc
    _ ≤ c * (G * eLpNorm (energyProduct f u : E → ℂ) p volume) := (bound (energyProduct f u)).2
    _ ≤ c * (G * (F * U)) :=
      mul_le_mul_left' (mul_le_mul_left' (energyProduct_eLpNorm_le p f u) _) _
    _ = _ := by dsimp only [W]; ring
  have form : separatedSkewCommutator f b R u = (2 : ℂ)⁻¹ • (A + B) := by
    funext x
    simp only [separatedSkewCommutator_eq_radian, div_eq_inv_mul, Pi.smul_apply,
      Pi.add_apply, Pi.mul_apply, smul_eq_mul, A, B, T]
  have half : ‖(2 : ℂ)⁻¹‖ₑ = (2 : ℝ≥0∞)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, norm_inv, Complex.norm_two,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [form]
  refine ⟨(hA.add hB).const_smul _, ?_⟩
  change eLpNorm ((2 : ℂ)⁻¹ • (A+B)) q volume ≤ W
  rw [eLpNorm_const_smul, half]
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (eLpNorm A q volume + eLpNorm B q volume) :=
      mul_le_mul_left' (eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable
        (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2))) _
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (W + W) := mul_le_mul_left' (add_le_add boundA boundB) _
    _ = ((2 : ℝ≥0∞)⁻¹ * 2) * W := by ring
    _ = W := by rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp), one_mul]

/-- The operator-norm gradient in the commutator estimate is bounded by the
sum of the original four coordinate derivative L³ norms. -/
theorem energyGradientNorm_le_coordinate_L3_sum (R : SchwartzMap E ℂ) :
    energyGradientNorm R ≤ ∑ j : Index,
      eLpNorm (energyPartial j R : E → ℂ) (ENNReal.ofReal 3) volume := by
  let P := ENNReal.ofReal 3
  let G := fderiv ℝ (R : E → ℂ)
  let T (j : Index) (x : E) := ‖energyPartial j R x‖
  have pointwise (x : E) : ‖G x‖ ≤ ∑ j, T j x := by
    apply (G x).opNorm_le_bound (Finset.sum_nonneg fun j _ => norm_nonneg _)
    intro v
    have expand : (∑ j : Index, v j • EuclideanSpace.single j 1) = v := by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun Index ℝ).sum_repr v
    have eq : G x v = ∑ j : Index, v j • energyPartial j R x := by
      calc
        _ = G x (∑ j : Index, v j • EuclideanSpace.single j 1) :=
          congrArg (fun z : E => G x z) expand.symm
        _ = _ := by simp only [map_sum, map_smul, G, energyPartial, SchwartzMap.pderivCLM_apply]
    rw [eq]
    calc
      _ ≤ ∑ j : Index, ‖v j • energyPartial j R x‖ := norm_sum_le _ _
      _ ≤ ∑ j : Index, T j x * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    energyGradientNorm R = eLpNorm (fun x => ‖G x‖) P volume := by
      simp only [energyGradientNorm, G, P, eLpNorm_norm]
    _ ≤ eLpNorm (∑ j : Index, T j) P volume := by
      apply eLpNorm_mono
      intro x
      rw [Finset.sum_apply, Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg (energyPartial j R x))]
      exact pointwise x
    _ ≤ ∑ j : Index, eLpNorm (T j) P volume :=
      eLpNorm_sum_le (fun j _ => (energyPartial j R).continuous.norm.aestronglyMeasurable)
        (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3)
    _ = _ := by simp only [T, P, eLpNorm_norm]

end Burnett.A02.FrequencySplit
