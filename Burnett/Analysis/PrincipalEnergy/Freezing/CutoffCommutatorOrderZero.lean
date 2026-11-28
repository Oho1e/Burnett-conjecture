import Burnett.Analysis.PrincipalEnergy.Freezing.LeftCommutatorModeSum
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped BigOperators ENNReal

/-- The same first-jet order-zero estimate after multiplication of the
actual input by a fixed Schwartz cutoff. -/
theorem schwartz_order_zero_jet_bound_input_product (θ : SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (A B P T : ℝ≥0∞)
    (hQ : SchwartzOrderZeroJetBound Q A B)
    (hθ : eLpNorm (θ : E → ℂ) ⊤ volume ≤ P)
    (hθJet : ∀ j : Index, eLpNorm (energyPartial j θ : E → ℂ) ⊤ volume ≤ T) :
    SchwartzOrderZeroJetBound (fun u => Q (energyProduct θ u)) (A*P) (A*T+B*P) := by
  intro u
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (u : E → ℂ) p volume
  let v := energyProduct θ u
  have mulBound (f g : SchwartzMap E ℂ) :
      eLpNorm (energyProduct f g : E → ℂ) p volume ≤
        eLpNorm (f : E → ℂ) ⊤ volume * eLpNorm (g : E → ℂ) p volume := by
    simpa only [energyProduct_apply, smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm (φ := (f : E → ℂ)) (f := (g : E → ℂ))
        (p := ⊤) (q := p) (r := p) (g.memLp p volume).1 f.continuous.aestronglyMeasurable)
  have hV : eLpNorm (v : E → ℂ) p volume ≤ P*Y :=
    (mulBound θ u).trans (mul_le_mul_right' hθ _)
  obtain ⟨hv, hVal, hDiff, hJet⟩ := hQ v
  refine ⟨hv, hVal.trans ((mul_le_mul_left' hV A).trans_eq (mul_assoc _ _ _).symm), hDiff, ?_⟩
  intro j
  let X := eLpNorm (energyPartial j u : E → ℂ) p volume
  let left := energyProduct (energyPartial j θ) u
  let right := energyProduct θ (energyPartial j u)
  have hD : (energyPartial j v : E → ℂ) = (left : E → ℂ) + (right : E → ℂ) := by
    funext x
    exact energyPartial_product j θ u x
  have hDerivative : eLpNorm (energyPartial j v : E → ℂ) p volume ≤ T*Y + P*X := by
    rw [hD]
    refine (eLpNorm_add_le (left.memLp p volume).1 (right.memLp p volume).1 (by norm_num [p])).trans ?_
    exact add_le_add ((mulBound _ _).trans (mul_le_mul_right' (hθJet j) _))
      ((mulBound _ _).trans (mul_le_mul_right' hθ _))
  refine ⟨(hJet j).1, (hJet j).2.trans ?_⟩
  calc
    _ ≤ A*(T*Y+P*X) + B*(P*Y) :=
      add_le_add (mul_le_mul_left' hDerivative _) (mul_le_mul_left' hV _)
    _ = (A*P)*X + (A*T+B*P)*Y := by ring

/-- The actual chart Weyl cutoff commutator inherits the order-zero
first-jet bounds of its homogeneous left action and actual correction. -/
theorem exists_cutoff_commutator_W13_of_left_order_zero
    (B L Q : SchwartzMap E ℂ → E → ℂ) (ident : ∀ u, B u = L u + Q u)
    (θ : SchwartzMap E ℂ) (A D C F : ℝ≥0∞)
    (hA : A < ⊤) (hD : D < ⊤) (hC : C < ⊤) (hF : F < ⊤)
    (hQ : SchwartzOrderZeroJetBound Q A D)
    (hL : SchwartzOrderZeroJetBound
      (fun u x => L (energyProduct θ u) x - θ x * L u x) C F) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ SchwartzOrderZeroJetBound
      (fun u x => B (energyProduct θ u) x - θ x * B u x) K K := by
  let P := eLpNorm (θ : E → ℂ) ⊤ volume
  let T := ∑ j : Index, eLpNorm (energyPartial j θ : E → ℂ) ⊤ volume
  have hP : P < ⊤ := (θ.memLp ⊤ volume).2
  have hT : T < ⊤ := ENNReal.sum_lt_top.mpr fun j _ => ((energyPartial j θ).memLp ⊤ volume).2
  have hJet (j : Index) : eLpNorm (energyPartial j θ : E → ℂ) ⊤ volume ≤ T :=
    Finset.single_le_sum (f := fun k : Index => eLpNorm (energyPartial k θ : E → ℂ) ⊤ volume)
      (fun _ _ => bot_le) (Finset.mem_univ j)
  let left (u : SchwartzMap E ℂ) (x : E) := L (energyProduct θ u) x - θ x * L u x
  let inside (u : SchwartzMap E ℂ) := Q (energyProduct θ u)
  let outside (u : SchwartzMap E ℂ) (x : E) := θ x * Q u x
  have hin : SchwartzOrderZeroJetBound inside (A*P) (A*T+D*P) :=
    schwartz_order_zero_jet_bound_input_product θ Q A D P T hQ le_rfl hJet
  have hout : SchwartzOrderZeroJetBound outside (P*A) (T*A+P*D) :=
    schwartz_order_zero_jet_bound_output_product θ Q A D P T hQ le_rfl hJet
  have hdiff := schwartz_order_zero_jet_bound_sub inside outside _ _ _ _ hin hout
  have hsum := schwartz_order_zero_jet_bound_add left (fun u => inside u - outside u) _ _ _ _ hL hdiff
  let K₁ := C + (A*P + P*A)
  let K₂ := F + ((A*T+D*P) + (T*A+P*D))
  have hK₁ : K₁ < ⊤ := ENNReal.add_lt_top.mpr ⟨hC, ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top hA hP, ENNReal.mul_lt_top hP hA⟩⟩
  have hK₂ : K₂ < ⊤ := ENNReal.add_lt_top.mpr ⟨hF, ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hA hT, ENNReal.mul_lt_top hD hP⟩,
      ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hT hA, ENNReal.mul_lt_top hP hD⟩⟩⟩
  have eq : (fun u x => B (energyProduct θ u) x - θ x * B u x) =
      fun u => left u + (inside u - outside u) := by
    funext u x
    rw [ident, ident]
    simp only [left, inside, outside, Pi.add_apply, Pi.sub_apply]
    ring
  refine ⟨max K₁ K₂, max_lt hK₁ hK₂, ?_⟩
  rw [eq]
  exact schwartz_order_zero_jet_bound_mono _ K₁ K₂ _ _ hsum (le_max_left _ _) (le_max_right _ _)

end Burnett.A03
