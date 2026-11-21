import Burnett.Analysis.PrincipalEnergy.Localization.GlobalOrderOneH1Action
import Burnett.Analysis.PrincipalEnergy.Commutator.SchwartzCoordinateJet

set_option autoImplicit false
set_option maxHeartbeats 5600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Metric Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy
open scoped ContDiff Topology

theorem baseDirectionSymbol_joint_smooth {a : Space → Space → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry a)) (e : Space) :
    ContDiff ℝ ∞ (uncurry (baseDirectionSymbol a e)) := by
  let L := ContinuousLinearMap.inl ℝ Space Space
  have hEq (p : Space × Space) :
      baseDirectionSymbol a e p.1 p.2 = fderiv ℝ (uncurry a) p (e,0) := by
    have hLine : HasFDerivAt (fun y => (y,p.2)) L p.1 := by
      exact (L.hasFDerivAt.add_const (0,p.2)).congr_of_eventuallyEq
        (.of_forall fun y => by simp [L])
    have hd := ((hs.differentiable (by simp)) p).hasFDerivAt.comp p.1 hLine
    change fderiv ℝ (uncurry a ∘ fun y => (y,p.2)) p.1 e = _
    rw [hd.fderiv]
    rfl
  rw [show uncurry (baseDirectionSymbol a e) = (fun p => fderiv ℝ (uncurry a) p (e,0)) from funext hEq]
  have hD : ContDiff ℝ ∞ (fderiv ℝ (uncurry a)) := by
    rw [contDiff_iff_forall_nat_le]
    intro n _
    exact hs.fderiv_right (by exact_mod_cast (le_top : (n : ℕ∞) + 1 ≤ ⊤))
  exact hD.clm_apply contDiff_const

/-- Properness of the original operator suffices here. The actual
localization of its derivative commutator follows from the original action
on the input and on its directional derivative. -/
theorem baseDirectionAction_hasCompactSupport_of_properSupport {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hProper : ProperKernelRelation (firstOrderKernelRelation a))
    (e : Space) (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) :
    HasCompactSupport (firstOrderAction (baseDirectionSymbol a e) f) := by
  let d := SchwartzMap.pderivCLM ℂ e f
  have hsupp : tsupport (d : Space → ℂ) ⊆ tsupport (f : Space → ℂ) := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    apply support_fderiv_subset ℝ
    intro hz
    apply hx
    change fderiv ℝ (f : Space → ℂ) x e = 0
    rw [hz, ContinuousLinearMap.zero_apply]
  have hd : HasCompactSupport (d : Space → ℂ) := hf.of_isClosed_subset isClosed_closure hsupp
  obtain ⟨K, hK, _, hB⟩ := exists_firstOrderAction_support_of_properSupport ha.frequency hProper f hf
  obtain ⟨J, hJ, _, hD⟩ := exists_firstOrderAction_support_of_properSupport ha.frequency hProper d hd
  refine (hK.union hJ).of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => ?_) (hK.union hJ).isClosed)
  by_contra hOut
  have hxK : x ∉ K := fun h => hOut (mem_union_left _ h)
  have hxJ : x ∉ J := fun h => hOut (mem_union_right _ h)
  have hZeroJ : firstOrderAction a d x = 0 := by
    by_contra hne
    exact hxJ (hD (subset_closure hne))
  have hNear : ∀ᶠ y in 𝓝 x, firstOrderAction a f y = 0 := by
    have hF : ∀ᶠ y in 𝓝 x, y ∈ Kᶜ := hK.isClosed.isOpen_compl.mem_nhds hxK
    filter_upwards [hF] with y hy
    by_contra hne
    exact hy (hB (subset_closure hne))
  have hLine : Tendsto (fun t : ℝ => x+t • e) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • e) := continuous_const.add (continuous_id.smul continuous_const)
    have ht : Tendsto (fun t : ℝ => x+t • e) (𝓝 0) (𝓝 (x+(0 : ℝ) • e)) := hc.continuousAt
    simpa only [zero_smul, add_zero] using ht
  have hDer : deriv (fun t : ℝ => firstOrderAction a f (x+t • e)) 0 = 0 := by
    have hEq : (fun t : ℝ => firstOrderAction a f (x+t • e)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
      hLine.eventually hNear
    rw [hEq.deriv_eq, deriv_const]
  apply hx
  rw [← firstOrderAction_direction_commutator_of_jointSmooth ha hs f x e, hDer, show
    firstOrderAction a (SchwartzMap.pderivCLM ℂ e f) x = 0 from hZeroJ, sub_self]

/-- The four actual coordinate derivative commutators inherit global H¹
bounds from the corresponding order-one mixed and pure symbol bounds. -/
theorem exists_global_coordinate_direction_action_h1_bounds {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hFrequency : ∀ b : Fin 4, FirstBaseFrequencyOrderOne (baseDirectionSymbol a (coordinateDirection b)))
    (hBase : ∀ (b : Fin 4) (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => baseDirectionSymbol a (coordinateDirection b) y ξ) x‖ ≤
        C * (1 + ‖ξ‖))
    (hProper : ProperKernelRelation (firstOrderKernelRelation a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Fin 4) (f : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
      let D (x : Space) :=
        deriv (fun t : ℝ => firstOrderAction a f (x+t • coordinateDirection b)) 0 -
          firstOrderAction a (SchwartzMap.pderivCLM ℂ (coordinateDirection b) f) x
      ∃ hD : MemLp D 2 volume, ‖hD.toLp D‖ ≤ C * coordinateH1 f := by
  choose C hC bounded using fun b =>
    exists_firstOrderAction_global_h1_action_bound (hFrequency b)
      (baseDirectionSymbol_joint_smooth hs (coordinateDirection b)) (hBase b)
  refine ⟨∑ b, C b, Finset.sum_nonneg (fun b _ => hC b), ?_⟩
  intro b f hf D
  have hEq : D = firstOrderAction (baseDirectionSymbol a (coordinateDirection b)) f :=
    funext fun x => firstOrderAction_direction_commutator_of_jointSmooth ha hs f x _
  rw [hEq]
  obtain ⟨hM, hBound⟩ := bounded b f
    (baseDirectionAction_hasCompactSupport_of_properSupport ha hs hProper _ f hf)
  exact ⟨hM, hBound.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ b)) (Real.sqrt_nonneg _))⟩

end Burnett.Analysis.CarlesonEmbedding
