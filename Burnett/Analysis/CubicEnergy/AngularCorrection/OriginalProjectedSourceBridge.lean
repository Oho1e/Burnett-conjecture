import Burnett.Analysis.GaugeProjection.ProjectedDivergenceDefinitions
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator
import Burnett.Analysis.CubicEnergy.AngularCorrection.RadianWavePhase

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open Filter MeasureTheory
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative realSchwartzMultiply realSchwartzMultiply_apply)
open Burnett.A08 (constantWave schwartzDivergence)
open scoped BigOperators ENNReal


local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- For the same global coefficient (a=m+d), the source of the actual
projected field agrees componentwise in (L^2) with the frozen wave plus
the variable divergence used in the weak energy identity. -/
theorem projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence
    (A : ProjectedSourceCoefficients) (m : Fin 4 → Fin 4 → ℝ)
    (d : Fin 4 → Fin 4 → SchwartzMap E ℝ)
    (hA : ∀ a b x, A.entry a b x = ((m a b + d a b x : ℝ) : ℂ))
    (z : ProjectionSchwartzMatrix) (i j : Fin 4) :
    let u := projectionFullSchwartz z
    projectedSourceDivergenceL2 A u i j =
      (constantWave m (u i j) + schwartzDivergence d (u i j)).toLp 2 volume := by
  intro u
  let v := u i j
  let p (a b : Fin 4) := (m a b : ℂ) • coordinateDerivative b v +
    realSchwartzMultiply (d a b) (coordinateDerivative b v)
  have hProduct (a b : Fin 4) :
      (fun x => A.entry a b x * coordinateDerivative b v x) = (p a b : E → ℂ) := by
    funext x
    rw [hA]
    simp only [Complex.ofReal_add, add_mul, p, SchwartzMap.add_apply, SchwartzMap.smul_apply,
      smul_eq_mul, realSchwartzMultiply_apply]
  let source := constantWave m v + schwartzDivergence d v
  have hSplit : -(∑ a : Fin 4, ∑ b : Fin 4, coordinateDerivative a (p a b)) = source := by
    simp only [p, source, constantWave, schwartzDivergence, map_add, map_smul,
      Finset.sum_add_distrib, neg_add]
  have hPoint (x : E) : projectedSourceDivergencePointwise A u i j x = source x := by
    let eval : SchwartzMap E ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun w => w x
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    rw [← hSplit]
    change -(∑ a : Fin 4, ∑ b : Fin 4,
        fderiv ℝ (fun y => A.entry a b y * coordinateDerivative b v y) x (EuclideanSpace.single a 1)) =
      eval (-(∑ a : Fin 4, ∑ b : Fin 4, coordinateDerivative a (p a b)))
    simp only [map_neg, map_sum]
    apply congrArg (Neg.neg : ℂ → ℂ)
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hProduct a b]
    simp only [eval, LinearMap.coe_mk, AddHom.coe_mk, coordinateDerivative, SchwartzMap.pderivCLM_apply]
  apply Lp.ext
  filter_upwards [projectedSourceDivergenceL2_ae A u i j, source.coeFn_toLp 2 volume] with x hx hs
  exact hx.trans ((hPoint x).trans hs.symm)


end Burnett.P01
