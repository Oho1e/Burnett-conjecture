import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinIntersection
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Burnett.Analysis.Microlocal.AngularCommutator.FourierRepresentation

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Filter Burnett.Fourier Burnett.RicciSymbol Burnett.Microlocal.AngularCommutator
open scoped Topology ContDiff ENNReal FourierTransform

/-- Under the paper's convention Dⱼ = −i∂ⱼ, the real Riesz factor is ξⱼ/|ξ|. -/
def mikhlinRiesz (j : Index) (ξ : E) : ℝ := ξ j / ‖ξ‖

theorem mikhlinRiesz_regular (j : Index) :
    ContDiffOn ℝ ∞ (mikhlinRiesz j) {ξ | ξ ≠ 0} ∧
    ∀ t : ℝ, 0<t → ∀ ξ, mikhlinRiesz j (t • ξ) = mikhlinRiesz j ξ := by
  constructor
  · intro ξ hx
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.div
      (contDiffAt_id.norm ℝ hx) (norm_ne_zero_iff.mpr hx)).contDiffWithinAt
  · intro t ht ξ
    change (t*ξ j)/‖t • ξ‖ = ξ j / ‖ξ‖
    rw [norm_smul,Real.norm_of_nonneg ht.le,mul_div_mul_left _ _ ht.ne']

theorem mikhlin_action_test (m : E → ℝ) (M : BoundedSymbol E) (hM : ∀ ξ, M ξ = (m ξ : ℂ))
    (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ)=m ξ) (f : SchwartzMap E ℂ) :
    (fourierMultiplier M (f.toLp 2 volume) : E → ℂ) =ᵐ[volume] radianAction m f := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := fun ξ => M ξ * F ξ
  have h₁ : Integrable G := F.integrable.bdd_mul M.measurable ⟨M.bound,M.norm_le⟩
  have he : (symbolL2 M (fourierL2Equiv (f.toLp 2 volume)) : E → ℂ) =ᵐ[volume] G := by
    filter_upwards [symbolL2_ae M (fourierL2Equiv (f.toLp 2 volume)),fourierL2Equiv_schwartz_ae f] with ξ h h'
    rw [h,h']
    rfl
  have h₂ := (Lp.memLp _).ae_eq he
  have eq : symbolL2 M (fourierL2Equiv (f.toLp 2 volume)) = h₂.toLp G := Lp.ext (he.trans h₂.coeFn_toLp.symm)
  rw [fourierMultiplier_apply,eq]
  refine (fourierL2Equiv_symm_eq_inverse_ae_of_integrable G h₁ h₂).trans (Eventually.of_forall fun x => ?_)
  rw [radianAction_eq_orderOne,show (fun ν => m (tau • ν)) = m from funext (hh _ (mul_pos (by norm_num) Real.pi_pos))]
  unfold orderOneAction
  have hG : G = fun ξ => (m ξ : ℂ)*𝓕 (f : E → ℂ) ξ := funext fun ξ => by
    change M ξ * F ξ = _
    rw [hM]
    rfl
  rw [hG]

theorem homogeneous_multiplier_Schwartz_bound (m : E → ℝ) (hm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ) (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      eLpNorm (radianAction m f) (ENNReal.ofReal p) volume ≤ C * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨M,hM⟩ := mikhlin_bounded_symbol m hm hh
  obtain ⟨C,hC,bnd⟩ := homogeneous_multiplier_intersection_bound m hm hh M hM p hp
  refine ⟨C,hC,fun f => ?_⟩
  rw [← eLpNorm_congr_ae (mikhlin_action_test m M hM hh f)]
  exact bnd f (f.memLp 2 volume) (f.memLp _ volume)

end Burnett.A02.FrequencySplit
