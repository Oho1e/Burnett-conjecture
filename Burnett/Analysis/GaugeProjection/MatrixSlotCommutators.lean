import Burnett.Analysis.GaugeProjection.MatrixProjectionRealization
import Burnett.Analysis.GaugeProjection.HodgeL2Bound
import Burnett.Analysis.GaugeProjection.InfraredCommutatorBound

set_option autoImplicit false
set_option maxHeartbeats 3400000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open Burnett.Fourier
open scoped BigOperators ENNReal NNReal ContDiff

private theorem coordinateDerivative_enorm_le (f : SchwartzMap E ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L (f : E → ℂ)) (i : Fin 4) (x : E) :
    ‖coordinateDerivative i f x‖ₑ ≤ (L : ℝ≥0∞) := by
  have h := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  have hnorm : ‖coordinateDerivative i f x‖ ≤ (L : ℝ) := by
    simpa only [coordinateDerivative, SchwartzMap.pderivCLM_apply] using
      h.trans (norm_fderiv_le_of_lipschitz ℝ hL)
  exact ENNReal.coe_le_coe.mpr hnorm

private theorem hodgeL2Mass_toReal (w : HodgeSchwartzField) :
    (hodgeL2Mass w).toReal = ∑ j, ‖(w j).toLp 2 volume‖ := by
  rw [hodgeL2Mass, ENNReal.toReal_sum (fun j _ => ((w j).memLp 2 volume).2.ne)]
  exact Finset.sum_congr rfl fun j _ => (Lp.norm_toLp _ ((w j).memLp 2 volume)).symm

/-- The already-checked Hodge commutator bound in the exact \(L^2\) action,
with the maximum of the four component norms as the vector norm. -/
theorem exists_hodgeVectorL2_commutator_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : Fin 4) (f : SchwartzMap E ℂ) (w A : HodgeSchwartzField),
      (∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) →
      ∀ (L : ℝ≥0), LipschitzWith L (f : E → ℂ) →
        ∀ i,
          ‖hodgeVectorL2Action
            (fun j => projectionMultiplyL2Scalar f ((coordinateDerivative b (w j)).toLp 2 volume)) i -
            projectionMultiplyL2Scalar f (hodgeVectorL2Action
              (fun j => (coordinateDerivative b (w j)).toLp 2 volume) i)‖ ≤
            D * (L : ℝ) * ‖fun j => (w j).toLp 2 volume‖ := by
  obtain ⟨C, hC, bound⟩ := exists_hodgeCommutator_action_l2_bound
  refine ⟨4 * C.toReal, by positivity, fun b f w A hA L hL i => ?_⟩
  let dw : HodgeSchwartzField := fun j => coordinateDerivative b (w j)
  let fv : HodgeSchwartzField := fun j => hodgeProduct f (dw j)
  let T := hodgeVectorL2Action (fun j => (fv j).toLp 2 volume) i
  let P := hodgeVectorL2Action (fun j => (dw j).toLp 2 volume) i
  let Z := T - projectionMultiplyL2Scalar f P
  have hT := hodgeVectorL2Action_schwartz_ae fv i
  have hP := hodgeVectorL2Action_schwartz_ae dw i
  have hfa := projectionMultiplyL2Scalar_ae f P
  have hcoe : (Z : E → ℂ) =ᵐ[volume] fun x => hodgeTransverseAction fv i x -
      f x * hodgeTransverseAction dw i x := by
    filter_upwards [Lp.coeFn_sub T (projectionMultiplyL2Scalar f P), hT, hP, hfa] with x hx ht hp hf
    change T x = _ at ht
    change P x = _ at hp
    simp only [Pi.sub_apply] at hx
    exact hx.trans (by rw [ht, hf, hp])
  have hfinite : hodgeL2Mass w < ⊤ :=
    ENNReal.sum_lt_top.mpr fun j _ => ((w j).memLp 2 volume).2
  have hb := (eLpNorm_congr_ae hcoe).trans_le
    (bound b f w A hA L (coordinateDerivative_enorm_le f L hL) i)
  have hnorm := ENNReal.toReal_mono
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC ENNReal.coe_lt_top) hfinite).ne hb
  rw [← Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, hodgeL2Mass_toReal] at hnorm
  simp_rw [projectionMultiplyL2Scalar_schwartz]
  change ‖Z‖ ≤ _
  calc
    _ ≤ C.toReal * (L : ℝ) * ∑ j, ‖(w j).toLp 2 volume‖ := hnorm
    _ ≤ C.toReal * (L : ℝ) * (4 * ‖fun j => (w j).toLp 2 volume‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [nsmul_eq_mul] using (Pi.sum_norm_apply_le_norm (fun j => (w j).toLp 2 volume))
    _ = _ := by ring

/-- The infrared contribution acts on the same differentiated Schwartz field
and the same physical coefficient in \(L^2\). -/
theorem projectionInfraredL2_commutator_bound (b : Fin 4) (f w : SchwartzMap E ℂ)
    (L : ℝ≥0) (hL : LipschitzWith L (f : E → ℂ)) :
    ‖projectionInfraredL2Scalar (projectionMultiplyL2Scalar f ((coordinateDerivative b w).toLp 2 volume)) -
      projectionMultiplyL2Scalar f (projectionInfraredL2Scalar ((coordinateDerivative b w).toLp 2 volume))‖ ≤
      projectionInfraredCommutatorConstant * (L : ℝ) * ‖w.toLp 2 volume‖ := by
  let d := coordinateDerivative b w
  let g := projectionInfraredAction (hodgeProduct f d)
  let h := hodgeProduct f (projectionInfraredAction d)
  have hf : ContDiff ℝ 1 (f : E → ℂ) := f.smooth 1
  obtain ⟨hv, hvb⟩ := projectionInfraredKernelAction_commutator_l2 b f L hf hL w
  let v : E → ℂ := fun x =>
    projectionInfraredKernelAction (fun y => f y * coordinateDerivative b w y) x -
      f x * projectionInfraredKernelAction (coordinateDerivative b w) x
  have e : g.toLp 2 volume - h.toLp 2 volume = hv.toLp v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (g.toLp 2 volume) (h.toLp 2 volume),
      g.coeFn_toLp 2 volume, h.coeFn_toLp 2 volume, hv.coeFn_toLp] with x hx hg hh hxv
    rw [hx, Pi.sub_apply, hg, hh, hxv]
    simp only [g, h, d, hodgeProduct_apply, projectionInfraredAction_eq_kernel]
    rfl
  rw [projectionMultiplyL2Scalar_schwartz, projectionInfraredL2Scalar_schwartz,
    projectionInfraredL2Scalar_schwartz, projectionMultiplyL2Scalar_schwartz]
  change ‖g.toLp 2 volume - h.toLp 2 volume‖ ≤ _
  rw [e, mul_comm projectionInfraredCommutatorConstant]
  exact hvb

end Burnett.P01
