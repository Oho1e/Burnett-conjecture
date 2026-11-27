import Burnett.Analysis.PrincipalEnergy.Freezing.SymmetrizationCoordinate
import Burnett.Analysis.PrincipalEnergy.Freezing.PatchLpDuality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators Topology ENNReal Burnett.A03

private theorem patch_lp_sum_ae {I : Type*} (t : Finset I) (u : I → PatchLp3)
    (f : I → E → ℂ) (h : ∀ k, (u k : E → ℂ) =ᵐ[volume] f k) :
    ((∑ k ∈ t, u k : PatchLp3) : E → ℂ) =ᵐ[volume] fun x => ∑ k ∈ t, f k x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ (ENNReal.ofReal 3) (volume : Measure E))
  | @insert k t hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (u k) (∑ i ∈ t, u i), h k, ih] with x he ha hb
    simp only [he, Pi.add_apply, ha, hb]

private theorem patch_lp_hasSum_ae_eq {I : Type*} [Countable I]
    (u : I → PatchLp3) (f : I → E → ℂ) (U : PatchLp3) (F : E → ℂ)
    (hU : HasSum u U) (hf : ∀ k, (u k : E → ℂ) =ᵐ[volume] f k)
    (hF : ∀ x, HasSum (fun k => f k x) (F x)) : (U : E → ℂ) =ᵐ[volume] F := by
  let atFinsets : Filter (Finset I) := (SummationFilter.unconditional I).filter
  have hT : Tendsto (fun t : Finset I => ∑ k ∈ t, u k) atFinsets (𝓝 U) := hU
  have hMeasure := tendstoInMeasure_of_tendsto_Lp hT
  obtain ⟨s, hs, hsub⟩ := hMeasure.exists_seq_tendsto_ae'
  have hAll : ∀ᵐ x : E, ∀ t : Finset I,
      ((∑ k ∈ t, u k : PatchLp3) : E → ℂ) x = ∑ k ∈ t, f k x :=
    ae_all_iff.mpr fun t => patch_lp_sum_ae t u f hf
  filter_upwards [hsub, hAll] with x h₁ h₂
  have hPoint : Tendsto (fun t : Finset I => ∑ k ∈ t, f k x) atFinsets (𝓝 (F x)) := hF x
  have h₂' := hPoint.comp hs
  have seqEq : (fun n : ℕ => ((∑ k ∈ s n, u k : PatchLp3) : E → ℂ) x) =
      (fun t : Finset I => ∑ k ∈ t, f k x) ∘ s :=
    funext fun n => h₂ (s n)
  rw [seqEq] at h₁
  exact tendsto_nhds_unique h₁ h₂'

/-- The difference of the actual symmetric series and its order-zero
remainder represents the genuine left Fourier action in physical L³. -/
theorem actual_left_series_L3_eq_sub_symmetrization_remainder {I : Type*} [Countable I]
    (f : I → Fin 2 → SchwartzMap E ℂ) (b : I → Fin 2 → E → ℝ)
    (u : SchwartzMap E ℂ) (symbol : E → E → ℝ)
    (S R : I → Fin 2 → PatchLp3) (U V : PatchLp3)
    (hS : HasSum (fun k => ∑ j, S k j) U)
    (hR : HasSum (fun k => ∑ j, R k j) V)
    (hSAe : ∀ k j, (S k j : E → ℂ) =ᵐ[volume] separatedSkewAction (f k j) (b k j) u)
    (hRAe : ∀ k j, (R k j : E → ℂ) =ᵐ[volume] separatedSkewLeftRemainder (f k j) (b k j) u)
    (hSymbol : ∀ x, HasSum (fun k => ∑ j, f k j x * radianSkewAction (b k j) u x)
      (radianSkewAction (symbol x) u x)) :
    ((U - V : PatchLp3) : E → ℂ) =ᵐ[volume] fun x => radianSkewAction (symbol x) u x := by
  let mode (k : I) (j : Fin 2) := S k j - R k j
  let value (k : I) := ∑ j, mode k j
  let left (k : I) (j : Fin 2) (x : E) := f k j x * radianSkewAction (b k j) u x
  have hMode (k : I) (j : Fin 2) : (mode k j : E → ℂ) =ᵐ[volume] left k j := by
    filter_upwards [Lp.coeFn_sub (S k j) (R k j), hSAe k j, hRAe k j] with x h a b'
    rw [h, Pi.sub_apply, a, b']
    dsimp only [separatedSkewLeftRemainder, left]
    ring
  have hValue (k : I) : (value k : E → ℂ) =ᵐ[volume] fun x => ∑ j, left k j x :=
    patch_lp_sum_ae Finset.univ (mode k) (left k) (hMode k)
  have hSum : HasSum value (U - V) := by
    simpa only [value, mode, Finset.sum_sub_distrib] using hS.sub hR
  exact patch_lp_hasSum_ae_eq value (fun k x => ∑ j, left k j x) _ _ hSum hValue hSymbol

/-- The derivative of the difference remains the distribution derivative
of the left action's L³ representative. -/
theorem left_weak_coordinate_of_symmetrization_remainder
    (U V dU dV : PatchLp3) (a : Index)
    (hU : HasWeakCoordinateDerivative3 U dU a)
    (hV : HasWeakCoordinateDerivative3 V dV a) :
    HasWeakCoordinateDerivative3 (U - V) (dU - dV) a := by
  intro φ
  rw [map_sub, map_sub, hU φ, hV φ]
  abel

end Burnett.A03
