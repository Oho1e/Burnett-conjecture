import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights
import Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction
import Burnett.Analysis.PrincipalEnergy.Quantization.CompactBaseFourier

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (CompactBaseOrderOne)
open scoped ContDiff BigOperators

local notation "P" => RadianParameter

/-- Pure spatial derivatives with a common weight in the original frequency. -/
structure BaseDerivativeBounds (a : E → E → ℂ) (w : E → ℝ) : Prop where
  smooth : ∀ ξ, ContDiff ℝ ∞ (fun x => a x ξ)
  bound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * w ξ

theorem pureBase_iteratedFDeriv_norm_le_joint {a : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry a)) (n : ℕ) (x ξ : E) :
    ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ ‖iteratedFDeriv ℝ n (uncurry a) (x,ξ)‖ := by
  let L : E →L[ℝ] P := ContinuousLinearMap.inl ℝ E E
  let G (q : P) := uncurry a (q+(0,ξ))
  have hsG : ContDiff ℝ ∞ G := hs.comp (contDiff_id.add contDiff_const)
  have he : (fun y => a y ξ) = G ∘ L := by
    funext y
    change _ = a (y+0) (0+ξ)
    simp
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => by
    change ‖(y, (0 : E))‖ ≤ 1*‖y‖
    simp [Prod.norm_def, norm_nonneg])
  rw [he,L.iteratedFDeriv_comp_right hsG x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  have eq : iteratedFDeriv ℝ n G (L x) = iteratedFDeriv ℝ n (uncurry a) (x,ξ) := by
    unfold G
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    change (x+0,0+ξ) = (x,ξ)
    simp
  rw [eq]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (uncurry a) (x,ξ)‖ * ‖L‖^n := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (iteratedFDeriv ℝ n (uncurry a) (x,ξ)).norm_compContinuousLinearMap_le (fun _ : Fin n => L)
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

namespace BaseDerivativeBounds

theorem of_joint {a : E → E → ℂ} {w : E → ℝ}
    (hs : ContDiff ℝ ∞ (uncurry a))
    (h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ‖iteratedFDeriv ℝ n (uncurry a) p‖ ≤ C * w p.2) :
    BaseDerivativeBounds a w where
  smooth ξ := hs.comp (contDiff_id.prodMk contDiff_const)
  bound n := by
    obtain ⟨C,hC,hB⟩ := h n
    exact ⟨C,hC,fun x ξ => (pureBase_iteratedFDeriv_norm_le_joint hs n x ξ).trans (hB (x,ξ))⟩

theorem weight_congr {a : E → E → ℂ} {w v : E → ℝ} (ha : BaseDerivativeBounds a w)
    (h : ∀ ξ, w ξ = v ξ) : BaseDerivativeBounds a v := by
  rwa [show v = w from (funext h).symm]

theorem frequency_multiplier (k : E → ℂ) (w : E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ ξ, 0 ≤ w ξ) (hk : ∀ ξ, ‖k ξ‖ ≤ C * w ξ) :
    BaseDerivativeBounds (fun _ ξ => k ξ) w where
  smooth _ := contDiff_const
  bound n := by
    refine ⟨C,hC,fun x ξ => ?_⟩
    by_cases hn : n = 0
    · rw [hn,norm_iteratedFDeriv_zero]
      exact hk ξ
    · rw [iteratedFDeriv_const_of_ne hn,Pi.zero_apply,norm_zero]
      exact mul_nonneg hC (hw ξ)

theorem schwartz_coefficient (c : SchwartzMap E ℂ) :
    BaseDerivativeBounds (fun x _ => c x) (fun _ => 1) where
  smooth _ := c.smooth'
  bound n := by
    let C := SchwartzMap.seminorm ℝ 0 n c
    refine ⟨C,(norm_nonneg _).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ c n 0),?_⟩
    intro x ξ
    simpa only [mul_one] using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ c n x

protected theorem mul {a b : E → E → ℂ} {w v : E → ℝ}
    (ha : BaseDerivativeBounds a w) (hb : BaseDerivativeBounds b v)
    (hw : ∀ ξ, 0 ≤ w ξ) :
    BaseDerivativeBounds (fun x ξ => a x ξ * b x ξ) (w*v) := by
  choose A hA hA' using ha.bound
  choose B hB hB' using hb.bound
  refine ⟨fun ξ => (ha.smooth ξ).mul (hb.smooth ξ), fun n => ?_⟩
  let C := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*A j*B (n-j)
  refine ⟨C,Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB (n-j))),fun x ξ => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (ha.smooth ξ) (hb.smooth ξ) x
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).trans
  change _ ≤ C * (w ξ * v ξ)
  dsimp only [C]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc
    _ ≤ (n.choose j : ℝ) * (A j * w ξ) * (B (n-j) * v ξ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hA' j x ξ) (Nat.cast_nonneg _)) (hB' (n-j) x ξ)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA j) (hw ξ)))
    _ = _ := by ring

protected theorem add {a b : E → E → ℂ} {w : E → ℝ}
    (ha : BaseDerivativeBounds a w) (hb : BaseDerivativeBounds b w) :
    BaseDerivativeBounds (fun x ξ => a x ξ + b x ξ) w := by
  refine ⟨fun ξ => (ha.smooth ξ).add (hb.smooth ξ), fun n => ?_⟩
  obtain ⟨A,hA,hA'⟩ := ha.bound n
  obtain ⟨B,hB,hB'⟩ := hb.bound n
  refine ⟨A+B,add_nonneg hA hB,fun x ξ => ?_⟩
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  change ‖iteratedFDeriv ℝ n ((fun y => a y ξ) + (fun y => b y ξ)) x‖ ≤ _
  rw [iteratedFDeriv_add_apply ((ha.smooth ξ).contDiffAt.of_le hn) ((hb.smooth ξ).contDiffAt.of_le hn)]
  exact (norm_add_le _ _).trans ((add_le_add (hA' x ξ) (hB' x ξ)).trans_eq (add_mul _ _ _).symm)

theorem sum {ι : Type*} [Fintype ι] (a : ι → E → E → ℂ) {w : E → ℝ}
    (ha : ∀ i, BaseDerivativeBounds (a i) w) : BaseDerivativeBounds (fun x ξ => ∑ i, a i x ξ) w := by
  refine ⟨fun ξ => ContDiff.sum fun i _ => (ha i).smooth ξ, fun n => ?_⟩
  choose C hC hB using fun i => (ha i).bound n
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun x ξ => ?_⟩
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have he := iteratedFDeriv_sum (u := Finset.univ) (f := fun i x => a i x ξ)
    (i := n) (fun i _ => ((ha i).smooth ξ).of_le hn)
  rw [he,Finset.sum_apply,Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hB i x ξ)

theorem compactBaseOrderOne {a : E → E → ℂ} (ha : BaseDerivativeBounds a radianFrequencyWeight)
    {K : Set E} (hK : IsCompact K) (hA : ∀ x ∉ K, ∀ ξ, a x ξ = 0) :
    CompactBaseOrderOne a where
  support := ⟨K,hK,fun ξ => closure_minimal (fun x hx => by
    by_contra h; exact hx (hA x h ξ)) hK.isClosed⟩
  smooth := ha.smooth
  order := ha.bound

end BaseDerivativeBounds
end Burnett.V03
