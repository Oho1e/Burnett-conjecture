import Burnett.Analysis.PrincipalEnergy.Quantization.CompactQuantization
import Burnett.Analysis.PrincipalEnergy.Quantization.CompactBaseDerivative

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Function MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse
open scoped ContDiff BigOperators

def actualDirectionCommutator (a : E → E → ℂ) (e : E) (f : SchwartzMap E ℂ) (x : E) : ℂ :=
  deriv (fun t : ℝ => firstOrderAction a f (x+t • e)) 0 -
    firstOrderAction a (SchwartzMap.pderivCLM ℂ e f) x

/-- On the original scalar Schwartz domain, one constant controls the actual
compact-base quantization and all four actual coordinate commutators. -/
theorem exists_compactBase_action_and_coordinate_commutator_bounds {a : E → E → ℂ}
    (hFirst : FirstBaseFrequencyOrderOne a) (hCompact : CompactBaseOrderOne a)
    (hSmooth : ContDiff ℝ ∞ (uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ f : SchwartzMap E ℂ, ∃ hB : MemLp (firstOrderAction a f) 2 (volume : Measure E),
        ‖hB.toLp (firstOrderAction a f)‖ ^ 2 ≤ C ^ 2 * schwartzH1Energy f) ∧
      ∀ (i : Fin 4) (f : SchwartzMap E ℂ),
        ∃ hD : MemLp (actualDirectionCommutator a (EuclideanSpace.single i 1) f) 2 (volume : Measure E),
          ‖hD.toLp (actualDirectionCommutator a (EuclideanSpace.single i 1) f)‖ ^ 2 ≤
            C ^ 2 * schwartzH1Energy f := by
  obtain ⟨B,hB,hBoundB⟩ := exists_compactBase_firstOrderAction_h1_to_l2 hCompact hSmooth.continuous
  let e (i : Fin 4) : E := EuclideanSpace.single i 1
  have hD (i : Fin 4) := exists_compactBase_firstOrderAction_h1_to_l2
    (compactBaseOrderOne_baseDirection hCompact (e i)) (baseDirectionSymbol_joint_continuous hSmooth (e i))
  choose D hDn hBoundD using hD
  let C := B + ∑ i, D i
  have hDsum : 0 ≤ ∑ i, D i := Finset.sum_nonneg (fun i _ => hDn i)
  have hnC : 0 ≤ C := add_nonneg hB hDsum
  have hEnergy (f : SchwartzMap E ℂ) : 0 ≤ schwartzH1Energy f :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hPromote (f : SchwartzMap E ℂ) (c : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) :
      c^2 * schwartzH1Energy f ≤ C^2 * schwartzH1Energy f :=
    mul_le_mul_of_nonneg_right ((sq_le_sq₀ hc hnC).mpr hcC) (hEnergy f)
  refine ⟨C,hnC,?_,?_⟩
  · intro f
    obtain ⟨hB₂,hBnd⟩ := hBoundB f
    exact ⟨hB₂,hBnd.trans (hPromote f B hB (le_add_of_nonneg_right hDsum))⟩
  · intro i f
    have hEq : actualDirectionCommutator a (e i) f =
        firstOrderAction (baseDirectionSymbol a (e i)) f :=
      funext fun x => firstOrderAction_direction_commutator_of_jointSmooth hFirst hSmooth f x (e i)
    change ∃ h : MemLp (actualDirectionCommutator a (e i) f) 2 (volume : Measure E),
      ‖h.toLp (actualDirectionCommutator a (e i) f)‖^2 ≤ C^2 * schwartzH1Energy f
    rw [hEq]
    have hdC : D i ≤ C :=
      (Finset.single_le_sum (fun j _ => hDn j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hB)
    obtain ⟨hD₂,hDnd⟩ := hBoundD i f
    exact ⟨hD₂,hDnd.trans (hPromote f (D i) (hDn i) hdC)⟩

end Burnett.Analysis.FirstOrderDyadic
