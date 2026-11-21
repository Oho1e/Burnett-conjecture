import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauH1Pair
import Burnett.Analysis.PrincipalEnergy.Localization.OrderOneCutoffH1Energy
import Burnett.Analysis.PrincipalEnergy.Localization.OrderOneRawFarPair

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Metric Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy
open scoped BigOperators ComplexConjugate ContDiff

private theorem tested_firstOrderAction_integrable {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hc : Continuous (uncurry a)) (f g : SchwartzMap Space ℂ) :
    Integrable (fun x => conj (g x) * firstOrderAction a f x) := by
  obtain ⟨hC, M, _, hM⟩ := firstOrderAction_continuous_and_bounded ha hc f
  refine (g.integrable.norm.const_mul M).mono'
    (((Complex.continuous_conj.comp g.continuous).mul hC).aestronglyMeasurable) (.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_conj, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)

/-- The actual original full order-one action tested by arbitrary compact
Schwartz fields, with a single global coordinate H¹-to-L² bound. -/
theorem exists_firstOrderAction_global_h1_pair_bound {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (g : Space → ℂ) →
      ‖∫ x, conj (g x) * firstOrderAction a f x‖ ≤
        C * coordinateH1 f * ‖g.toLp 2 volume‖ := by
  classical
  obtain ⟨α, hαSupp, hαReal, hαPos, hαFinite⟩ := exists_lattice_schwartz_subpartition
  obtain ⟨χ, _, hχSupp, hχVal, hχOne⟩ := exists_radialSchwartzCutoff 4 5 (by norm_num) (by norm_num)
  obtain ⟨ψ, hψ, _, _, hψOne⟩ := exists_radialSchwartzCutoff 5 6 (by norm_num) (by norm_num)
  have hχNorm (x : Space) : ‖χ x‖ ≤ 1 := by
    rw [(hχVal x).1, Complex.norm_real, Real.norm_of_nonneg (hχVal x).2.1]
    exact (hχVal x).2.2
  have hχDiff (x : Space) : ‖χ x-1‖ ≤ 1 := by
    rw [(hχVal x).1, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hχVal x).2.2)]
    linarith only [(hχVal x).2.1]
  obtain ⟨Cnear, hN, near⟩ := exists_movingPlateau_h1_physical_pair_bound ha hs hb ψ hψ
  obtain ⟨Ccut, hC, cut⟩ := exists_latticeCutoff_coordinateH1_square_sum_bound hχSupp hχNorm
  obtain ⟨Cfar, hF, far⟩ := exists_firstOrderAction_latticeFar_pair_bound ha.frequency
  refine ⟨Cnear*Ccut+Cfar, by positivity, fun f g hg => ?_⟩
  obtain ⟨s, hSub, hOne⟩ := hαFinite (tsupport (g : Space → ℂ)) hg
  let β (i : ↥s) := α i.val
  let Q (i : ↥s) := translateSchwartz (-latticeCenter i.val) χ
  let F (i : ↥s) := scalarSchwartzProduct (Q i) f
  let G (i : ↥s) := scalarSchwartzProduct (β i) g
  let R (i : ↥s) := f - F i
  let A (i : ↥s) : ℂ := ∫ x, conj (G i x)*firstOrderAction a (F i) x
  let B (i : ↥s) : ℂ := ∫ x, conj (G i x)*firstOrderAction a (R i) x
  have sumSub (x : Space) : (∑ i, (β i x).re) ≤ 1 := by
    change (∑ i ∈ s.attach, (α i.val x).re) ≤ 1
    rw [Finset.sum_attach s (fun i => (α i x).re)]
    exact hSub x
  have sumOne (x : Space) (hx : g x ≠ 0) : (∑ i, β i x) = 1 := by
    change (∑ i ∈ s.attach, α i.val x) = 1
    rw [Finset.sum_attach s (fun i => α i x)]
    exact hOne x (subset_closure hx)
  have hFsupport (i : ↥s) : tsupport (F i : Space → ℂ) ⊆ closedBall (latticeCenter i.val) 5 :=
    tsupport_mul_subset_left.trans (translateSchwartz_tsupport_subset_closedBall χ _ _ hχSupp)
  have hGsupport (i : ↥s) : tsupport (G i : Space → ℂ) ⊆ closedBall (latticeCenter i.val) 3 :=
    tsupport_mul_subset_left.trans (hαSupp _)
  have hχGap (i : ↥s) (x y : Space) (hx : β i x ≠ 0) (hy : Q i y ≠ 1) : 1 ≤ ‖x-y‖ := by
    have hx' : dist x (latticeCenter i.val) ≤ 3 := mem_closedBall.mp (hαSupp _ (subset_closure hx))
    have hy' : 4 < dist y (latticeCenter i.val) := by
      apply lt_of_not_ge
      intro h
      apply hy
      change χ (y + -latticeCenter i.val) = 1
      apply hχOne
      simpa only [dist_eq_norm, sub_eq_add_neg] using h
    have hd := dist_triangle y x (latticeCenter i.val)
    rw [dist_comm y x, dist_eq_norm x y] at hd
    linarith only [hd, hy', hx']
  have hA (i : ↥s) : ‖A i‖ ≤ Cnear*coordinateH1 (F i)*‖(G i).toLp 2 volume‖ := by
    apply near (latticeCenter i.val) (F i) (G i)
    · intro x hx
      change ψ (x+-latticeCenter i.val) = 1
      apply hψOne
      simpa only [mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hFsupport i hx
    · intro x hx
      change ψ (x+-latticeCenter i.val) = 1
      apply hψOne
      have hg := (closedBall_subset_closedBall (by norm_num : (3:ℝ) ≤ 5)) (hGsupport i hx)
      simpa only [mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hg
  have hNear : ‖∑ i, A i‖ ≤ (Cnear*Ccut)*coordinateH1 f*‖g.toLp 2 volume‖ := by
    have h1 : Real.sqrt (∑ i, coordinateH1 (F i)^2) ≤ Ccut*coordinateH1 f := by
      refine (Real.sqrt_le_sqrt (cut s f)).trans_eq ?_
      have hH : 0 ≤ coordinateH1 f := Real.sqrt_nonneg _
      rw [← mul_pow, Real.sqrt_sq (mul_nonneg hC hH)]
    have h2 : Real.sqrt (∑ i, ‖(G i).toLp 2 volume‖^2) ≤ ‖g.toLp 2 volume‖ :=
      (Real.sqrt_le_sqrt (scalarCutoff_sum_norm_sq_le β (fun i => hαReal i.val)
        (fun i => hαPos i.val) sumSub g)).trans_eq (Real.sqrt_sq (norm_nonneg _))
    calc
      _ ≤ ∑ i, ‖A i‖ := norm_sum_le _ _
      _ ≤ Cnear*(∑ i, coordinateH1 (F i) * ‖(G i).toLp 2 volume‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => (hA i).trans_eq (by ring)
      _ ≤ Cnear*(Real.sqrt (∑ i, coordinateH1 (F i)^2)*Real.sqrt (∑ i, ‖(G i).toLp 2 volume‖^2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun i => coordinateH1 (F i)) (fun i => ‖(G i).toLp 2 volume‖)) hN
      _ ≤ Cnear*((Ccut*coordinateH1 f)*‖g.toLp 2 volume‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.sqrt_nonneg _)
          (mul_nonneg hC (Real.sqrt_nonneg _))) hN
      _ = _ := by ring
  have hFar : ‖∑ i, B i‖ ≤ Cfar*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
    refine far β Q f g (fun i x => hχDiff _) (fun x => ?_) hχGap
    have hNorm (i : ↥s) : ‖β i x‖ = (β i x).re := by
      calc
        _ = ‖((β i x).re : ℂ)‖ := congrArg norm (hαReal i.val x)
        _ = _ := by rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ (β i x).re from hαPos i.val x)]
    simp only [hNorm]
    exact sumSub x
  have hDecomp : (∫ x, conj (g x)*firstOrderAction a f x) = (∑ i, A i)+(∑ i, B i) := by
    calc
      _ = ∑ i, ∫ x, conj (G i x)*firstOrderAction a f x := by
        rw [← integral_finset_sum Finset.univ (fun i _ =>
          tested_firstOrderAction_integrable ha.frequency hs.continuous f (G i))]
        apply integral_congr_ae
        filter_upwards with x
        simp only [G, scalarSchwartzProduct_apply, map_mul]
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← map_sum]
        by_cases hx : g x = 0
        · simp only [hx, map_zero, mul_zero, zero_mul]
        · rw [sumOne x hx, map_one, one_mul]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [A,B]
        rw [← integral_add (tested_firstOrderAction_integrable ha.frequency hs.continuous (F i) (G i))
          (tested_firstOrderAction_integrable ha.frequency hs.continuous (R i) (G i))]
        have hR (x : Space) : firstOrderAction a (R i) x =
            firstOrderAction a f x - firstOrderAction a (F i) x := by
          simpa only [R, one_smul, one_mul] using firstOrderAction_sub_smul a ha.frequency x f (F i) 1
        apply integral_congr_ae
        filter_upwards with x
        rw [hR]
        ring
  have hfH : ‖f.toLp 2 volume‖ ≤ coordinateH1 f := by
    rw [← schwartzCoordinateJet_norm, ← schwartzCoordinateJet_zero_component]
    exact PiLp.norm_apply_le _ _
  rw [hDecomp]
  calc
    _ ≤ ‖∑ i, A i‖+‖∑ i, B i‖ := norm_add_le _ _
    _ ≤ Cnear*Ccut*coordinateH1 f*‖g.toLp 2 volume‖+ Cfar*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ :=
      add_le_add hNear hFar
    _ ≤ Cnear*Ccut*coordinateH1 f*‖g.toLp 2 volume‖+ Cfar*coordinateH1 f*‖g.toLp 2 volume‖ :=
      add_le_add_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfH hF) (norm_nonneg _)) _
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
