import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.Algebra.Order.Archimedean

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.DenseComplexFunctional

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℚ E]

/-- A bounded rational-linear functional on a dense rational test space
extends to a genuine complex-linear map, once the test space and functional
respect multiplication by the imaginary unit. -/
theorem existsUnique_complexFunctional_of_dense_rat_submodule
    (S : Submodule ℚ E) (hS : Dense (S : Set E)) (L : S →L[ℚ] ℂ)
    (hmem : ∀ x : S, Complex.I • (x : E) ∈ S)
    (hI : ∀ x : S, L ⟨Complex.I • (x : E), hmem x⟩ = Complex.I * L x)
    (C : ℝ) (hC : ∀ x : S, ‖L x‖ ≤ C * ‖(x : E)‖) :
    ∃! G : E →L[ℂ] ℂ, (∀ x : S, G (x : E) = L x) ∧
      ∀ x : E, ‖G x‖ ≤ C * ‖x‖ := by
  let e := S.subtypeL
  have hd : DenseRange e := hS.denseRange_val
  have hi : IsUniformInducing e :=
    (isometry_subtype_coe (s := (S : Set E))).isUniformInducing
  let F := L.extend e hd hi
  have hF (x : S) : F (x : E) = L x := ContinuousLinearMap.extend_eq L e hd hi x
  have hFi (x : E) : F (Complex.I • x) = Complex.I * F x := by
    apply hd.induction_on (p := fun y => F (Complex.I • y) = Complex.I * F y) x
    · exact isClosed_eq (F.continuous.comp (continuous_const_smul _))
        (continuous_const.mul F.continuous)
    · intro y
      change F ((⟨Complex.I • (y : E), hmem y⟩ : S) : E) = Complex.I * F (y : E)
      rw [hF, hF]
      exact hI y
  have hFr (r : ℝ) (x : E) : F ((r : ℂ) • x) = (r : ℂ) * F x := by
    apply Rat.denseRange_cast.induction_on
      (p := fun t : ℝ => F ((t : ℂ) • x) = (t : ℂ) * F x) r
    · exact isClosed_eq (F.continuous.comp (Complex.continuous_ofReal.smul continuous_const))
        (Complex.continuous_ofReal.mul continuous_const)
    · intro q
      rw [Complex.ofReal_ratCast, ratCast_smul_eq ℂ ℚ q x]
      simpa only [← ratCast_smul_eq ℂ ℚ q (F x), smul_eq_mul] using F.map_smul q x
  let G : E →L[ℂ] ℂ := {
    toFun := F
    map_add' := F.map_add
    map_smul' := fun z x => by
      change F (z • x) = z * F x
      rw [← Complex.re_add_im z, add_smul, mul_smul, F.map_add, hFr, hFr, hFi, add_mul, mul_assoc]
    cont := F.continuous
  }
  refine ⟨G, ⟨hF, ?_⟩, ?_⟩
  · intro x
    apply hd.induction_on (p := fun y => ‖G y‖ ≤ C * ‖y‖) x
    · exact isClosed_le G.continuous.norm (continuous_const.mul continuous_norm)
    · intro y
      change ‖F (y : E)‖ ≤ C * ‖(y : E)‖
      rw [hF]
      exact hC y
  · intro H hH
    apply ContinuousLinearMap.coeFn_injective
    apply hd.equalizer H.continuous G.continuous
    funext y
    exact (hH.1 y).trans (hF y).symm

end Burnett.Microlocal.DenseComplexFunctional
