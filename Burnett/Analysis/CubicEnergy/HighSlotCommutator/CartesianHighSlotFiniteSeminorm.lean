import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianSymbolReconstruction
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneSymbolTopology
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneSymbolPairing

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option synthInstance.maxHeartbeats 350000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.A07 (integrable_radianHighPairWeight_of_orderOne)
open MeasureTheory
open scoped ContDiff ENNReal NNReal

private theorem exists_schwartzPair_symbolSize_bound (f g h : SchwartzMap E ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (b : Joint → ℂ), Measurable b → ∀ (B : ℝ), 0≤B →
      (∀ x : Joint, ‖b x‖≤B*(1+‖x.1‖+‖x.2‖)) → ‖radianHighPair b f g h‖≤C*B := by
  let w : Joint → ℂ := fun x => (1+‖x.1‖+‖x.2‖ : ℝ)
  have hw : Continuous w := Complex.continuous_ofReal.comp
    ((continuous_const.add continuous_fst.norm).add continuous_snd.norm)
  have hW (x : Joint) : ‖w x‖=1+‖x.1‖+‖x.2‖ := by
    simp only [w,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤1+‖x.1‖+‖x.2‖)]
  have iW := integrable_radianHighPairWeight_of_orderOne w hw.measurable 1 zero_le_one
    (fun x => by rw [hW,one_mul]) f g h
  let c := ‖(tau^8)⁻¹‖
  let m := ∫ p, ‖radianHighPairWeight w f g h p‖
  have hm : 0≤m := integral_nonneg fun _ => norm_nonneg _
  refine ⟨c*m,mul_nonneg (norm_nonneg _) hm,?_⟩
  intro b hb B hB0 hB
  have ib := integrable_radianHighPairWeight_of_orderOne b hb B hB0 hB f g h
  have pt (x : Joint) : ‖radianHighPairWeight b f g h x‖ ≤ B*‖radianHighPairWeight w f g h x‖ := by
    simp only [radianHighPairWeight,norm_mul,hW]
    calc
      _ ≤ (B*(1+‖x.1‖+‖x.2‖))*‖radianFourier f x.1‖*‖radianFourier g x.2‖*
          ‖(starRingEnd ℂ) (radianFourier h (x.2+x.1))‖ := by gcongr; exact hB x
      _ = _ := by ring
  have integ := integral_mono ib.norm (iW.norm.const_mul B) pt
  rw [integral_const_mul] at integ
  change ‖(tau^8)⁻¹ • (∫ x, radianHighPairWeight b f g h x)‖≤_
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans integ) (norm_nonneg _)).trans_eq
    (by unfold c m; ring)

private theorem exists_schwartzCommutator_symbolSize_bound (D f g h : SchwartzMap E ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (b : Joint → ℂ), Measurable b → ∀ (B : ℝ), 0≤B →
      (∀ x : Joint, ‖b x‖≤B*(1+‖x.1‖+‖x.2‖)) →
      ‖radianHighCommutatorPair b (fun x => (D x).re) f g h‖≤C*B := by
  let product v := gapSchwartzProduct (coefficientRealPart D) v
  obtain ⟨A,hA,first⟩ := exists_schwartzPair_symbolSize_bound f (product g) h
  obtain ⟨C,hC,second⟩ := exists_schwartzPair_symbolSize_bound f g (product h)
  refine ⟨A+C,add_nonneg hA hC,?_⟩
  intro b hb B hB0 hB
  have eq (v : SchwartzMap E ℂ) :
      (fun x : E => ((D x).re : ℂ)*v x) = (product v : E → ℂ) := by
    funext x
    change ((D x).re : ℂ)*v x = gapSchwartzProduct (coefficientRealPart D) v x
    rw [gapSchwartzProduct_apply,coefficientRealPart_apply]
  simp only [radianHighCommutatorPair,eq]
  exact ((norm_sub_le _ _).trans (add_le_add (first b hb B hB0 hB) (second b hb B hB0 hB))).trans_eq
    ((add_mul A C B).symm)

private structure CartesianCommutatorTest where
  D : SchwartzMap E ℂ
  L : ℝ≥0
  lipschitz : LipschitzWith L D
  f : SchwartzMap E ℂ
  g : SchwartzMap E ℂ
  h : SchwartzMap E ℂ

private def CartesianCommutatorTest.mass (t : CartesianCommutatorTest) (inputL2 : Bool) : ℝ≥0∞ :=
  (t.L : ℝ≥0∞)*triLpMass t.f t.g t.h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2)

private theorem CartesianCommutatorTest.mass_lt_top (t : CartesianCommutatorTest) (inputL2 : Bool) : (t.mass inputL2)<⊤ := by
  unfold CartesianCommutatorTest.mass triLpMass
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top <|
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (t.f.eLpNorm_lt_top _ volume) (t.g.eLpNorm_lt_top _ volume))
      (t.h.eLpNorm_lt_top _ volume)

private def CartesianCommutatorTest.pair (t : CartesianCommutatorTest) (b : Joint → ℂ) : ℂ :=
  radianHighCommutatorPair b (fun x => (t.D x).re) t.f t.g t.h

private def cartesianCommutatorLinearMap (ρ R A : ℝ) (hA : 0≤A)
    (hSize : ∀ B : OrderOneSymbol ℂ, Measurable (cartesianReconstruction ρ R B) ∧
      ∀ x : Joint, ‖cartesianReconstruction ρ R B x‖≤
        A*orderOneWeightedSeminorm ℂ 0 B*(1+‖x.1‖+‖x.2‖))
    (t : CartesianCommutatorTest) : OrderOneSymbol ℂ →ₗ[ℝ] ℂ where
  toFun B := t.pair (cartesianReconstruction ρ R B)
  map_add' B C := by
    change t.pair (cartesianReconstruction ρ R ((B : Joint → ℂ)+(C : Joint → ℂ))) = _
    rw [map_add]
    exact radianHighCommutatorPair_add_schwartz_symbols _ _ _ _ (hSize B).1 (hSize C).1
      (mul_nonneg hA (apply_nonneg _ _)) (mul_nonneg hA (apply_nonneg _ _))
      (hSize B).2 (hSize C).2 t.D t.f t.g t.h
  map_smul' a B := by
    change t.pair (cartesianReconstruction ρ R (a • (B : Joint → ℂ))) = _
    rw [map_smul]
    exact radianHighCommutatorPair_real_smul_symbol a _ _ _ _ _

private def cartesianNormalizedFunctional (inputL2 : Bool) (ρ R A : ℝ) (hA : 0≤A)
    (hSize : ∀ B : OrderOneSymbol ℂ, Measurable (cartesianReconstruction ρ R B) ∧
      ∀ x : Joint, ‖cartesianReconstruction ρ R B x‖≤
        A*orderOneWeightedSeminorm ℂ 0 B*(1+‖x.1‖+‖x.2‖))
    (t : CartesianCommutatorTest) : OrderOneSymbolFrechet →L[ℝ] ℂ := by
  let T := (cartesianCommutatorLinearMap ρ R A hA hSize t).comp orderOneSymbolFrechetEquiv.symm.toLinearMap
  let m := (t.mass inputL2).toReal
  let S := m⁻¹ • T
  refine ⟨S,?_⟩
  obtain ⟨C,hC,bound⟩ := exists_schwartzCommutator_symbolSize_bound t.D t.f t.g t.h
  refine continuous_orderOneSymbolFrechet_of_orderZero S ⟨m⁻¹*C*A,by positivity⟩ ?_
  intro B
  have app : S (orderOneSymbolFrechetEquiv B) =
      m⁻¹ • t.pair (cartesianReconstruction ρ R B) := by
    simp only [S,T,LinearMap.smul_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    rfl
  have hB0 : 0≤orderOneWeightedSeminorm ℂ 0 B := apply_nonneg _ _
  have h := bound (cartesianReconstruction ρ R B) (hSize B).1 _ (mul_nonneg hA hB0) (hSize B).2
  rw [app,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans_eq (by simp; ring)

private theorem cartesianNormalizedFunctional_apply (inputL2 : Bool) (ρ R A : ℝ) (hA : 0≤A)
    (hSize : ∀ B : OrderOneSymbol ℂ, Measurable (cartesianReconstruction ρ R B) ∧
      ∀ x : Joint, ‖cartesianReconstruction ρ R B x‖≤
        A*orderOneWeightedSeminorm ℂ 0 B*(1+‖x.1‖+‖x.2‖))
    (t : CartesianCommutatorTest) (B : OrderOneSymbol ℂ) :
    cartesianNormalizedFunctional inputL2 ρ R A hA hSize t (orderOneSymbolFrechetEquiv B) =
      (t.mass inputL2).toReal⁻¹ • t.pair (cartesianReconstruction ρ R B) := by
  change (t.mass inputL2).toReal⁻¹ •
    cartesianCommutatorLinearMap ρ R A hA hSize t
      (orderOneSymbolFrechetEquiv.symm (orderOneSymbolFrechetEquiv B))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- A common finite weighted derivative threshold suffices for the
actual reconstructed multiplier, with the original Lipschitz and test norms. -/
theorem exists_cartesianReconstruction_finiteSeminorm_bound_paper (inputL2 : Bool) {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ (B : OrderOneSymbol ℂ)
      (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (cartesianReconstruction ρ R B) (fun x => (D x).re) f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*realOrderOneSymbolSeminorm ℂ K B)*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨A,hA,ctrl⟩ := exists_cartesianReconstruction_size hρ hρ' hR
  have hSize (B : OrderOneSymbol ℂ) : Measurable (cartesianReconstruction ρ R B) ∧
      ∀ x : Joint, ‖cartesianReconstruction ρ R B x‖≤
        A*orderOneWeightedSeminorm ℂ 0 B*(1+‖x.1‖+‖x.2‖) :=
    ⟨(ctrl B B.contDiff).1,(ctrl B B.contDiff).2 _ (apply_nonneg _ _) B.norm_apply_le_weightedSeminorm_zero⟩
  have qualitative (B : OrderOneSymbol ℂ) : ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ t : CartesianCommutatorTest,
      ‖t.pair (cartesianReconstruction ρ R B)‖ₑ≤M*(t.mass inputL2) := by
    obtain ⟨M,hM,bound⟩ := exists_cartesianReconstruction_highSlot_bound_paper inputL2 hρ hρ' hR B B.contDiff
      _ (apply_nonneg _ _) B.norm_apply_le_weightedSeminorm_zero
    exact ⟨M,hM,fun t => (bound t.D t.L t.lipschitz t.f t.g t.h).trans_eq (by
      unfold CartesianCommutatorTest.mass
      ac_rfl)⟩
  let T := cartesianNormalizedFunctional inputL2 ρ R A hA hSize
  have pointBound : ∀ u : OrderOneSymbolFrechet, ∃ M : ℝ, ∀ t : CartesianCommutatorTest, ‖T t u‖≤M := by
    intro u
    obtain ⟨B,rfl⟩ := orderOneSymbolFrechetEquiv.surjective u
    obtain ⟨M,hM,H⟩ := qualitative B
    refine ⟨M.toReal,fun t => ?_⟩
    have h := ENNReal.toReal_mono (ENNReal.mul_lt_top hM (t.mass_lt_top inputL2)).ne (H t)
    rw [toReal_enorm,ENNReal.toReal_mul] at h
    dsimp only [T]
    rw [cartesianNormalizedFunctional_apply,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
    by_cases hm : (t.mass inputL2).toReal=0
    · simp only [hm,inv_zero,zero_mul,ENNReal.toReal_nonneg]
    · exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans_eq (by
        rw [mul_comm M.toReal,← mul_assoc,inv_mul_cancel₀ hm,one_mul])
  obtain ⟨K,C,hC,budget⟩ := exists_finite_orderOneSymbol_bound T pointBound
  refine ⟨K,C,hC,?_⟩
  intro B D L hD f g h
  let t : CartesianCommutatorTest := ⟨D,L,hD,f,g,h⟩
  have main : ‖t.pair (cartesianReconstruction ρ R B)‖ₑ ≤
      ENNReal.ofReal (C*realOrderOneSymbolSeminorm ℂ K B)*(t.mass inputL2) := by
    by_cases hm : (t.mass inputL2)=0
    · obtain ⟨_,_,bound⟩ := qualitative B
      simpa only [hm,mul_zero] using bound t
    · have mp := ENNReal.toReal_pos hm (t.mass_lt_top inputL2).ne
      have bnd := budget B t
      dsimp only [T] at bnd
      rw [cartesianNormalizedFunctional_apply,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr mp.le)] at bnd
      have H := mul_le_mul_of_nonneg_left bnd mp.le
      rw [← mul_assoc,mul_inv_cancel₀ mp.ne',one_mul] at H
      have hR' := ENNReal.ofReal_le_ofReal H
      rwa [ofReal_norm_eq_enorm,mul_comm (t.mass inputL2).toReal,
        ENNReal.ofReal_mul (mul_nonneg hC (apply_nonneg _ _)),ENNReal.ofReal_toReal (t.mass_lt_top inputL2).ne] at hR'
  exact main.trans_eq (by unfold CartesianCommutatorTest.mass; dsimp only [t]; ac_rfl)

theorem exists_cartesianReconstruction_finiteSeminorm_bound {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ (B : OrderOneSymbol ℂ)
      (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (cartesianReconstruction ρ R B) (fun x => (D x).re) f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*realOrderOneSymbolSeminorm ℂ K B)*triLpMass f g h 4 4 2 :=
  exists_cartesianReconstruction_finiteSeminorm_bound_paper false hρ hρ' hR

/-- The original angular-mode Cartesian symbol is unchanged by the linear
reconstruction, so its physical weighted seminorm gives the tested bound. -/
theorem exists_regularizedLowCartesian_highSlot_finiteSeminorm_bound_paper (inputL2 : Bool) {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ (η χ : ℝ → ℝ) (b : Joint → ℂ),
      (∀ z≥R, η z=1) → (∀ z≥ρ^2, χ z=0) →
      ∀ (hb : regularizedLowCartesianSymbol η χ b ∈ orderOneSymbolSubmodule ℂ)
      (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) (fun x => (D x).re) f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*realOrderOneSymbolSeminorm ℂ K ⟨_,hb⟩)*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨K,C,hC,bound⟩ := exists_cartesianReconstruction_finiteSeminorm_bound_paper inputL2 hρ hρ' hR
  refine ⟨K,C,hC,?_⟩
  intro η χ b hηone hcut hb D L hD f g h
  have H := bound ⟨regularizedLowCartesianSymbol η χ b,hb⟩ D L hD f g h
  change ‖radianHighCommutatorPair (cartesianReconstruction ρ R (regularizedLowCartesianSymbol η χ b))
    (fun x => (D x).re) f g h‖ₑ≤_ at H
  rwa [cartesianReconstruction_eq_regularizedLowCartesianSymbol hρ hρ' hR η χ b hηone hcut] at H

theorem exists_regularizedLowCartesian_highSlot_finiteSeminorm_bound {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ (η χ : ℝ → ℝ) (b : Joint → ℂ),
      (∀ z≥R, η z=1) → (∀ z≥ρ^2, χ z=0) →
      ∀ (hb : regularizedLowCartesianSymbol η χ b ∈ orderOneSymbolSubmodule ℂ)
      (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) (fun x => (D x).re) f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*realOrderOneSymbolSeminorm ℂ K ⟨_,hb⟩)*triLpMass f g h 4 4 2 :=
  exists_regularizedLowCartesian_highSlot_finiteSeminorm_bound_paper false hρ hρ' hR

end Burnett.A06
