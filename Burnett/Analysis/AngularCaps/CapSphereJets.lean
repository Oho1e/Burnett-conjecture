import Burnett.Analysis.AngularCaps.CapFrequencyCoordinates
import Burnett.Analysis.AngularCaps.UniformNullCapCharts
import Burnett.Analysis.AngularCaps.ActualBaseCapJets
import Burnett.Analysis.AngularCaps.SmoothCapFamily

set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.Analysis.CapFourier

open Set Metric
open scoped ContDiff BigOperators
open Burnett.Analysis.ProjectiveNullCaps

private def coordinateNormProduct : ℝ :=
  ‖frequencyCoordinates.symm.toContinuousLinearMap‖ * ‖frequencyCoordinates.toContinuousLinearMap‖

private theorem sphereJet_of_weighted {b : NullFrequencyCoordinates → ℝ} {D : ℝ}
    {j : ℕ} (h : ∀ u : NullFrequencyCoordinates, u ≠ 0 →
      ‖u‖^j * ‖iteratedFDeriv ℝ j b u‖ ≤ D)
    {x : Space} (hx : x ∈ sphere (0 : Space) 1) :
    ‖iteratedFDeriv ℝ j (b ∘ frequencyCoordinates) x‖ ≤ D * coordinateNormProduct^j := by
  let J := frequencyCoordinates
  let U : Set NullFrequencyCoordinates := {u | u ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hJU : IsOpen (J ⁻¹' U) := hU.preimage J.continuous
  have hx1 : ‖x‖ = 1 := by simpa [mem_sphere,dist_zero_right] using hx
  have hx0 : x ≠ 0 := by intro e; simp [e] at hx1
  have hxJ : J x ∈ U := by
    intro e
    exact hx0 (J.injective (e.trans J.map_zero.symm))
  have hd := J.iteratedFDerivWithin_comp_right b hU.uniqueDiffOn hxJ j
  rw [iteratedFDerivWithin_of_isOpen j hJU (x := x) hxJ,
    iteratedFDerivWithin_of_isOpen j hU (x := J x) hxJ] at hd
  have hchain :
      ‖iteratedFDeriv ℝ j (b ∘ J) x‖ ≤
        ‖iteratedFDeriv ℝ j b (J x)‖ * ‖J.toContinuousLinearMap‖^j := by
    rw [hd]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ j b (J x)) (fun _ : Fin j => J.toContinuousLinearMap))
  have hnorm := J.symm.toContinuousLinearMap.le_opNorm (J x)
  change ‖J.symm (J x)‖ ≤ _ at hnorm
  rw [J.symm_apply_apply,hx1] at hnorm
  have hpow := pow_le_pow_left₀ zero_le_one hnorm j
  rw [one_pow,mul_pow] at hpow
  have hweighted :
      ‖iteratedFDeriv ℝ j b (J x)‖ ≤ ‖J.symm.toContinuousLinearMap‖^j * D := by
    calc
      _ = 1 * ‖iteratedFDeriv ℝ j b (J x)‖ := (one_mul _).symm
      _ ≤ (‖J.symm.toContinuousLinearMap‖^j * ‖J x‖^j) * ‖iteratedFDeriv ℝ j b (J x)‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = ‖J.symm.toContinuousLinearMap‖^j * (‖J x‖^j * ‖iteratedFDeriv ℝ j b (J x)‖) :=
        mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (h (J x) hxJ) (by positivity)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j b (J x)‖ * ‖J.toContinuousLinearMap‖^j := hchain
    _ ≤ (‖J.symm.toContinuousLinearMap‖^j * D) * ‖J.toContinuousLinearMap‖^j :=
      mul_le_mul_of_nonneg_right hweighted (by positivity)
    _ = _ := by
      change (‖J.symm.toContinuousLinearMap‖^j * D) * ‖J.toContinuousLinearMap‖^j =
        D * (‖J.symm.toContinuousLinearMap‖ * ‖J.toContinuousLinearMap‖)^j
      rw [mul_pow]
      ring

/-- The same selected caps and chart at each center give all orders required
by the four-dimensional Mikhlin theorem for both actual cap multipliers. -/
theorem exists_uniform_capMultiplier_sphere_jets {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (hND : ∀ m ∈ K, Nondegenerate m)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ D c₀ δ₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ J₀ : ℝ, 0 ≤ J₀ ∧ ∀ m ∈ K, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
        ∃ S : SmoothThinConeCaps m δ (c*κ*δ^2) inner outer enlarged D,
          ∀ w ∈ S.centers, ∃ F : NullCapChart m w,
            ∀ j : ℕ, j ≤ 6 → ∀ x ∈ sphere (0 : Space) 1,
              ‖iteratedFDeriv ℝ j
                (capMultiplier S.centers m δ (c*κ*δ^2) inner outer w ∘ capFrequencyEquiv F hδ.ne') x‖ ≤ J₀ ∧
              ‖iteratedFDeriv ℝ j
                (enlargedCapMultiplier m δ (c*κ*δ^2) outer enlarged w ∘ capFrequencyEquiv F hδ.ne') x‖ ≤ J₀ := by
  have hSym (m : Form) (hm : m ∈ K) : Symmetric m := (hFrame m hm).elim lorentzFrame_symm
  obtain ⟨B,hB,hCharts⟩ := exists_uniform_nullCapCharts hK hFrame hND
  obtain ⟨D,c₀,hD,hc₀,hFamily⟩ := exists_smooth_thinCone_capMultipliers hK hSym hND hIn hIO hOE
  let δ₀ := min 1 (1/(20*B))
  have h20 : 0 < 20*B := mul_pos (by norm_num) hB
  refine ⟨D,c₀,δ₀,hD,hc₀,lt_min zero_lt_one (one_div_pos.mpr h20),min_le_left _ _,?_⟩
  intro κ hκ hκsmall c hc hcSmall
  have hA : 0 < c*κ := mul_pos hc hκ
  choose Cbase hCb hBase using fun j : Fin 7 =>
    actual_capMultiplier_parabolic_jets B inner outer hA hIn hIO j.val
  choose Cplus hCp hPlus using fun j : Fin 7 =>
    actual_enlargedCapMultiplier_parabolic_jets B outer enlarged hA (hIn.trans hIO.le) hOE j.val
  let term (j : Fin 7) := max (Cbase j) (Cplus j) * coordinateNormProduct^j.val
  have hW₀ : 0 ≤ coordinateNormProduct := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hterm (j : Fin 7) : 0 ≤ term j :=
    mul_nonneg ((hCb j).le.trans (le_max_left _ _)) (pow_nonneg hW₀ _)
  refine ⟨∑ j : Fin 7, term j,Finset.sum_nonneg (fun j _ => hterm j),?_⟩
  intro m hm δ hδ hδSmall
  have hδone := hδSmall.trans (min_le_left _ _)
  have hScaled : δ*(20*B) ≤ 1 :=
    (le_div_iff₀ h20).mp (hδSmall.trans (min_le_right _ _))
  have hSmallPlus : 4*B*(5*δ) ≤ 1 := by linarith only [hScaled]
  have hSmallBase : 4*B*(4*δ) ≤ 1 := by
    linarith only [hScaled,mul_nonneg hB.le hδ.le]
  obtain ⟨S⟩ := hFamily m hm κ hκ hκsmall δ hδ hδone c hc hcSmall
  refine ⟨S,?_⟩
  intro w hw
  have hW := S.centers_null hw
  obtain ⟨F,hF,hI⟩ := hCharts m hm w hW
  refine ⟨F,fun j hj x hx => ?_⟩
  let i : Fin 7 := ⟨j,Nat.lt_succ_of_le hj⟩
  have bound := Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 7))) => hterm v)
    (Finset.mem_univ i)
  change term i ≤ ∑ v : Fin 7, term v at bound
  have hbase := sphereJet_of_weighted (j := j) (x := x)
    (hBase i m w F hW.1 hF hI δ hδ hδone hSmallBase S.centers S.centers_null S.centers_separated) hx
  have hplus := sphereJet_of_weighted (j := j) (x := x)
    (hPlus i m w F hW.1 hF hI δ hδ hδone hSmallPlus) hx
  exact ⟨hbase.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hW₀ _)).trans bound),
    hplus.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hW₀ _)).trans bound)⟩

end Burnett.Analysis.CapFourier
