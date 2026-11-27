import Burnett.Analysis.PrincipalEnergy.Freezing.ModeLpJetBounds
import Burnett.Analysis.PrincipalEnergy.Freezing.EnergyHolder
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.Module

set_option autoImplicit false
set_option maxHeartbeats 1450000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal BigOperators Burnett.A03

private theorem patch_pair_integrable (u : PatchLp3) (φ : SchwartzMap E ℂ) :
    Integrable (fun x => u x * φ x) :=
  (energy_integral_three_three_halves (Lp.memLp u) (φ.memLp (ENNReal.ofReal (3 / 2)) volume)).1

/-- The genuine bilinear integral against one fixed Schwartz coefficient. -/
def patchLpPair (φ : SchwartzMap E ℂ) : PatchLp3 →L[ℂ] ℂ := by
  let L : PatchLp3 →ₗ[ℂ] ℂ :=
    { toFun := fun u => ∫ x, u x * φ x
      map_add' := fun u v => by
        calc
          _ = ∫ x, (u x + v x) * φ x := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add u v] with x h
            rw [h, Pi.add_apply]
          _ = (∫ x, u x * φ x) + ∫ x, v x * φ x := by
            simp_rw [add_mul]
            exact integral_add (patch_pair_integrable u φ) (patch_pair_integrable v φ)
      map_smul' := fun a u => by
        simp only [RingHom.id_apply]
        calc
          _ = ∫ x, a • (u x * φ x) := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul a u] with x h
            rw [h, Pi.smul_apply]
            simp only [smul_eq_mul, mul_assoc]
          _ = a • (∫ x, u x * φ x) := integral_smul a _ }
  let N := eLpNorm (φ : E → ℂ) (ENNReal.ofReal (3 / 2)) volume
  refine L.mkContinuous N.toReal (fun u => ?_)
  change ‖∫ x, u x * φ x‖ ≤ N.toReal * ‖u‖
  have hφ := φ.memLp (ENNReal.ofReal (3 / 2)) volume
  have hu := Lp.memLp u
  have bound := (energy_integral_three_three_halves hu hφ).2
  have htop := ENNReal.mul_lt_top hu.eLpNorm_lt_top hφ.eLpNorm_lt_top
  have h := ENNReal.toReal_mono htop.ne bound
  rw [← ofReal_norm_eq_enorm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul] at h
  rw [Lp.norm_def, mul_comm]
  exact h

theorem patch_lp_pair_toLp (φ : SchwartzMap E ℂ) {u : E → ℂ}
    (hu : MemLp u (ENNReal.ofReal 3) volume) :
    patchLpPair φ (hu.toLp u) = ∫ x, u x * φ x := by
  change (∫ x, (hu.toLp u) x * φ x) = _
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hu] with x h
  rw [h]

/-- A coordinate derivative interpreted by the original distribution pairing. -/
def HasWeakCoordinateDerivative3 (u v : PatchLp3) (a : Index) : Prop :=
  ∀ φ : SchwartzMap E ℂ, patchLpPair (energyPartial a φ) u = -patchLpPair φ v

theorem separated_mode_Lp_jet_is_weak_derivative
    {f u : SchwartzMap E ℂ} {b : E → ℝ} (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (h : SeparatedModeLpJet f b u) (a : Index) :
    HasWeakCoordinateDerivative3 h.valueLp (h.coordinateLp a) a := by
  intro φ
  let w := separatedSkewAction f b u
  let d := separatedModeCoordinateDerivative f b u a
  let p := ENNReal.ofReal (3 / 2)
  have left : Integrable (fun x => w x * energyPartial a φ x) :=
    (energy_integral_three_three_halves h.value ((energyPartial a φ).memLp p volume)).1
  have right : Integrable (fun x => d x * φ x) :=
    (energy_integral_three_three_halves (h.coordinate a) (φ.memLp p volume)).1
  have zero : Integrable (fun x => w x * φ x) :=
    (energy_integral_three_three_halves h.value (φ.memLp p volume)).1
  have eq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := w) (g := (φ : E → ℂ)) (v := EuclideanSpace.single a 1)
    right left zero (separated_skew_bounded_coordinate_jet f b hb hom u).1 φ.differentiable
  rw [SeparatedModeLpJet.valueLp, SeparatedModeLpJet.coordinateLp, patch_lp_pair_toLp, patch_lp_pair_toLp]
  exact eq

theorem weak_coordinate_derivative_finset_sum {I : Type*} (s : Finset I) (u v : I → PatchLp3) (a : Index)
    (h : ∀ k ∈ s, HasWeakCoordinateDerivative3 (u k) (v k) a) :
    HasWeakCoordinateDerivative3 (∑ k ∈ s, u k) (∑ k ∈ s, v k) a := by
  intro φ
  rw [map_sum, map_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k hk => h k hk φ

/-- Weak differentiation survives the actual norm-convergent series. -/
theorem weak_coordinate_derivative_hasSum {I : Type*} (u v : I → PatchLp3) (U V : PatchLp3) (a : Index)
    (hU : HasSum u U) (hV : HasSum v V) (h : ∀ k, HasWeakCoordinateDerivative3 (u k) (v k) a) :
    HasWeakCoordinateDerivative3 U V a := by
  intro φ
  have left := hU.mapL (patchLpPair (energyPartial a φ))
  have right := (hV.mapL (patchLpPair φ)).neg
  have eq : (fun k => patchLpPair (energyPartial a φ) (u k)) =
      (fun k => -patchLpPair φ (v k)) := funext fun k => h k φ
  rw [← eq] at right
  exact left.unique right

end Burnett.A03
