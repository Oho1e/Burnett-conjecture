import Burnett.Analysis.GaugeProjection.EuclideanGaugeProjection
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinApplications
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.P01

open Matrix Set Filter
open Burnett.A02.FrequencySplit (E MikhlinRealization homogeneous_multiplier_all_Lp)
open scoped BigOperators ContDiff Topology Matrix

/-- A scalar entry of the actual perpendicular matrix in Euclidean frequencies. -/
def directionProjectionEntry (a b : Fin 4) (ξ : E) : ℝ :=
  directionProjection (fun j => ξ j) a b

private theorem directionProjectionEntry_ratio (a b : Fin 4) (ξ : E) :
    directionProjectionEntry a b ξ =
      (if a = b then 1 else 0) - ξ a * ξ b / ‖ξ‖^2 := by
  have hn : (fun j : Fin 4 => ξ j) ⬝ᵥ (fun j : Fin 4 => ξ j) = ‖ξ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  simp only [directionProjectionEntry, directionProjection, hn, sub_apply, one_apply,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, div_eq_mul_inv]
  rw [mul_comm ((‖ξ‖^2)⁻¹)]

theorem directionProjectionEntry_contDiffOn (a b : Fin 4) :
    ContDiffOn ℝ ∞ (directionProjectionEntry a b) {ξ : E | ξ ≠ 0} := by
  have coordinate (i : Fin 4) : ContDiff ℝ ∞ (fun ξ : E => ξ i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have squared : ContDiff ℝ ∞ (fun ξ : E => ‖ξ‖^2) := contDiff_norm_sq ℝ
  have divided : ContDiffOn ℝ ∞ (fun ξ : E => ξ a * ξ b / ‖ξ‖^2) {ξ : E | ξ ≠ 0} :=
    ((coordinate a).mul (coordinate b)).contDiffOn.div squared.contDiffOn
      (fun ξ hξ => pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  rw [show directionProjectionEntry a b =
    (fun ξ : E => (if a = b then 1 else 0) - ξ a * ξ b / ‖ξ‖^2) from
      funext (directionProjectionEntry_ratio a b)]
  exact (contDiff_const (c := if a = b then (1 : ℝ) else 0)).contDiffOn.sub divided

theorem directionProjectionEntry_scale (a b : Fin 4) (t : ℝ) (ht : 0 < t) (ξ : E) :
    directionProjectionEntry a b (t • ξ) = directionProjectionEntry a b ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  simp only [directionProjectionEntry_ratio, norm_smul, Real.norm_of_nonneg ht.le,
    PiLp.smul_apply, smul_eq_mul]
  have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  field_simp [ht.ne', hnorm]

/-- Coefficient of input entry `(c,d)` in output entry `(a,b)` of `Π_E(ξ)`. -/
def gaugeProjectionSymbol (a b c d : Fin 4) (ξ : E) : ℝ :=
  directionProjectionEntry a c ξ * directionProjectionEntry d b ξ

theorem gaugeProjectionSymbol_even (a b c d : Fin 4) (ξ : E) :
    gaugeProjectionSymbol a b c d (-ξ) = gaugeProjectionSymbol a b c d ξ := by
  simp [gaugeProjectionSymbol, directionProjectionEntry_ratio]

theorem gaugeProjectionSymbol_contDiffOn (a b c d : Fin 4) :
    ContDiffOn ℝ ∞ (gaugeProjectionSymbol a b c d) {ξ : E | ξ ≠ 0} :=
  (directionProjectionEntry_contDiffOn a c).mul (directionProjectionEntry_contDiffOn d b)

theorem gaugeProjectionSymbol_scale (a b c d : Fin 4) (t : ℝ) (ht : 0 < t) (ξ : E) :
    gaugeProjectionSymbol a b c d (t • ξ) = gaugeProjectionSymbol a b c d ξ := by
  simp only [gaugeProjectionSymbol, directionProjectionEntry_scale _ _ t ht ξ]

theorem gaugeProjectionSymbol_mikhlin (a b c d : Fin 4) (p : ℝ) (hp : 1 < p) :
    MikhlinRealization (gaugeProjectionSymbol a b c d) p hp :=
  homogeneous_multiplier_all_Lp _ (gaugeProjectionSymbol_contDiffOn a b c d)
    (gaugeProjectionSymbol_scale a b c d) p hp

/-- A fixed smooth infrared regularization of the actual projection symbol. -/
def gaugeProjectionInfrared (r : ℝ) : ℝ :=
  Real.smoothTransition (r - 1)

theorem gaugeProjectionInfrared_contDiff : ContDiff ℝ ∞ gaugeProjectionInfrared :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem gaugeProjectionInfrared_zero {r : ℝ} (hr : r ≤ 1) :
    gaugeProjectionInfrared r = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr)

theorem gaugeProjectionInfrared_one {r : ℝ} (hr : 2 ≤ r) :
    gaugeProjectionInfrared r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def regularizedGaugeProjectionSymbol (a b c d : Fin 4) (ξ : E) : ℝ :=
  gaugeProjectionInfrared ‖ξ‖ * gaugeProjectionSymbol a b c d ξ

theorem regularizedGaugeProjectionSymbol_even (a b c d : Fin 4) (ξ : E) :
    regularizedGaugeProjectionSymbol a b c d (-ξ) = regularizedGaugeProjectionSymbol a b c d ξ := by
  simp only [regularizedGaugeProjectionSymbol, norm_neg, gaugeProjectionSymbol_even]

theorem regularizedGaugeProjectionSymbol_zero (a b c d : Fin 4) {ξ : E} (hξ : ‖ξ‖ ≤ 1) :
    regularizedGaugeProjectionSymbol a b c d ξ = 0 := by
  simp only [regularizedGaugeProjectionSymbol, gaugeProjectionInfrared_zero hξ, zero_mul]

theorem regularizedGaugeProjectionSymbol_high (a b c d : Fin 4) {ξ : E} (hξ : 2 ≤ ‖ξ‖) :
    regularizedGaugeProjectionSymbol a b c d ξ = gaugeProjectionSymbol a b c d ξ := by
  simp only [regularizedGaugeProjectionSymbol, gaugeProjectionInfrared_one hξ, one_mul]

theorem regularizedGaugeProjectionSymbol_contDiff (a b c d : Fin 4) :
    ContDiff ℝ ∞ (regularizedGaugeProjectionSymbol a b c d) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have hSmall : ∀ᶠ y in 𝓝 (0 : E), ‖y‖ < 1 :=
      (continuous_norm.tendsto (0 : E)).eventually (Iio_mem_nhds (by simp))
    have he : (fun _ : E => (0 : ℝ)) =ᶠ[𝓝 (0 : E)] regularizedGaugeProjectionSymbol a b c d :=
      hSmall.mono (fun y hy => (regularizedGaugeProjectionSymbol_zero a b c d hy.le).symm)
    exact contDiffAt_const.congr_of_eventuallyEq he.symm
  · have hN : {y : E | y ≠ 0} ∈ 𝓝 ξ := isOpen_compl_singleton.mem_nhds hξ
    exact (gaugeProjectionInfrared_contDiff.contDiffAt.comp ξ (contDiffAt_norm ℝ hξ)).mul
      ((gaugeProjectionSymbol_contDiffOn a b c d).contDiffAt hN)

end Burnett.P01
