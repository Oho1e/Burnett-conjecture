import Burnett.Analysis.AllScaleTransfer.FiniteRatioIntegral
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.Analysis.LowRatio

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Interval

private theorem iteratedFDeriv_comp_linear_open {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {D : Set F} (hD : IsOpen D)
    {f : F → G} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f D)
    (L : E →L[ℝ] F) {x : E} (hx : L x ∈ D) {j : ℕ} (hj : j ≤ n) :
    iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hpre := hD.preimage L.continuous
  rw [← iteratedFDerivWithin_of_isOpen j hpre hx,
    L.iteratedFDerivWithin_comp_right hf hD.uniqueDiffOn hpre.uniqueDiffOn hx hj,
    iteratedFDerivWithin_of_isOpen j hD hx]

private theorem norm_iteratedFDeriv_comp_linear_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {D : Set F} (hD : IsOpen D)
    {f : F → G} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f D)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {x : E} (hx : L x ∈ D) {j : ℕ} (hj : j ≤ n) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [iteratedFDeriv_comp_linear_open hD hf L hx hj]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

private theorem continuousOn_open_jet {D : Set Point} (hD : IsOpen D)
    {f : Point → ℂ} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f D) {j : ℕ} (hj : j ≤ n) :
    ContinuousOn (iteratedFDeriv ℝ j f) D :=
  (hf.continuousOn_iteratedFDerivWithin hj hD.uniqueDiffOn).congr fun _ hz =>
    (iteratedFDerivWithin_of_isOpen j hD hz).symm

theorem remainder_jets_of_numerator {U : Set Angles} {a b : ℝ}
    (hU : IsOpen U) (ha : a < 0) (hb : 0 < b)
    (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    (hN : ContDiffOn ℝ 100 (numerator M χ) (Window U a b))
    (B : ℝ) (hB : ∀ j ≤ 100, ∀ z ∈ Window U a b,
      ‖iteratedFDeriv ℝ j (numerator M χ) z‖ ≤ B) :
    ContDiffOn ℝ 99 (remainder M χ) (Window U a b) ∧
      ∀ j ≤ 99, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j (remainder M χ) z‖ ≤ B := by
  let D := Window U a b
  let N := numerator M χ
  let F := ratioDerivative N
  let u (t : ℝ) : Point → ℂ := F ∘ ratioScale t
  have hD : IsOpen D := hU.prod isOpen_Ioo
  have hd : ContDiffOn ℝ 99 (fderiv ℝ N) D := hN.fderiv_of_isOpen hD (by norm_num)
  have hF : ContDiffOn ℝ 99 F D := hd.clm_apply contDiffOn_const
  have hfBound (j : ℕ) (hj : j ≤ 99) (z : Point) (hz : z ∈ D) :
      ‖iteratedFDeriv ℝ j F z‖ ≤ B := by
    have h₁ := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ N) (c := ((0 : Angles), (1 : ℝ))) (hd.contDiffAt (hD.mem_nhds hz))
      (show (j : WithTop ℕ∞) ≤ 99 by exact_mod_cast hj)
    have hDir : ‖((0 : Angles), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [hDir, one_mul, norm_iteratedFDeriv_fderiv] at h₁
    exact h₁.trans (hB (j + 1) (by omega) z hz)
  have hSmooth (t : ℝ) (ht : t ∈ Time) : ContDiffOn ℝ 99 (u t) D :=
    (hF.comp_continuousLinearMap (ratioScale t)).mono (ratioScale_mapsTo ha hb ht)
  have hMeas (j : ℕ) (hj : j ≤ 99) (z : Point) (hz : z ∈ D) :
      ContinuousOn (fun t => iteratedFDeriv ℝ j (u t) z) Time := by
    let A := ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) ℂ
    let L := Point →L[ℝ] Point
    let comp (p : (Fin j → L) × A) := p.2.compContinuousLinearMap p.1
    have hc : Continuous comp :=
      continuousOn_univ.mp (ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap
        (𝕜 := ℝ) (t := univ)).continuousOn
    have hS : Continuous (fun t : ℝ => ratioScale t z) :=
      ratioScale_continuous.clm_apply continuous_const
    have hJ : ContinuousOn (fun t => iteratedFDeriv ℝ j F (ratioScale t z)) Time :=
      (continuousOn_open_jet hD hF (by exact_mod_cast hj)).comp hS.continuousOn
        (fun t ht => ratioScale_mapsTo ha hb ht hz)
    have hP : Continuous (fun t : ℝ => (fun _ : Fin j => ratioScale t)) :=
      continuous_pi fun _ => ratioScale_continuous
    refine (hc.continuousOn.comp (hP.continuousOn.prodMk hJ) (mapsTo_univ _ _)).congr ?_
    intro t ht
    exact iteratedFDeriv_comp_linear_open hD hF (ratioScale t) (ratioScale_mapsTo ha hb ht hz)
      (by exact_mod_cast hj)
  have hUniform (j : ℕ) (hj : j ≤ 99) (t : ℝ) (ht : t ∈ Time) (z : Point) (hz : z ∈ D) :
      ‖iteratedFDeriv ℝ j (u t) z‖ ≤ B :=
    (norm_iteratedFDeriv_comp_linear_le hD hF (ratioScale t) (ratioScale_norm_le ht)
      (ratioScale_mapsTo ha hb ht hz) (show (j : WithTop ℕ∞) ≤ 99 by exact_mod_cast hj)).trans
      (hfBound j hj _ (ratioScale_mapsTo ha hb ht hz))
  obtain ⟨hAvg, _, hAvgBound⟩ := timeAverage_contDiffOn_and_jets hD 99 u (fun _ => B)
    hSmooth hMeas hUniform
  have hEq : EqOn (remainder M χ) (timeAverage u) D := by
    intro z hz
    rw [remainder_eq_integral hU ha hb M χ hχ (hN.of_le (by norm_num)) hz, timeAverage,
      intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    rfl
  refine ⟨hAvg.congr hEq, ?_⟩
  intro j hj z hz
  rw [← iteratedFDerivWithin_of_isOpen j hD hz, iteratedFDerivWithin_congr hEq hz j,
    iteratedFDerivWithin_of_isOpen j hD hz]
  exact hAvgBound j hj z hz

private theorem cutoff_uniform_bound (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (a b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 100, ∀ r ∈ Icc a b, ‖iteratedFDeriv ℝ j χ r‖ ≤ K := by
  have bounded (j : Fin 101) :
      ∃ K : ℝ, ∀ r ∈ Icc a b, ‖iteratedFDeriv ℝ j.val χ r‖ ≤ K := by
    have hc : Continuous (iteratedFDeriv ℝ j.val χ) :=
      hχ.continuous_iteratedFDeriv (by exact_mod_cast (show j.val ≤ (⊤ : ℕ∞) from le_top))
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).bddAbove_image hc.norm.continuousOn
    exact ⟨K, fun r hr => hK (mem_image_of_mem _ hr)⟩
  choose K hK using bounded
  refine ⟨∑ j : Fin 101, max (K j) 0, Finset.sum_nonneg fun j _ => le_max_right _ _, ?_⟩
  intro j hj r hr
  let k : Fin 101 := ⟨j, by omega⟩
  exact (hK k r hr).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => le_max_right (K i) 0) (Finset.mem_univ k)))

private theorem numerator_jets {U : Set Angles} {a b : ℝ}
    (hU : IsOpen U) (ha : a < 0) (hb : 0 < b) (M : Point → ℂ) (χ : ℝ → ℝ)
    (hM : ContDiffOn ℝ 100 M (Window U a b)) (hχ : ContDiff ℝ ∞ χ)
    (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (boundM : ∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j M z‖ ≤ A)
    (boundχ : ∀ j ≤ 100, ∀ r ∈ Icc a b, ‖iteratedFDeriv ℝ j χ r‖ ≤ K) :
    ContDiffOn ℝ 100 (numerator M χ) (Window U a b) ∧
      ∀ j ≤ 100, ∀ z ∈ Window U a b,
        ‖iteratedFDeriv ℝ j (numerator M χ) z‖ ≤ (1 + 2^100 * K) * A := by
  let D := Window U a b
  let R := ContinuousLinearMap.snd ℝ Angles ℝ
  let f : Point → ℝ := χ ∘ R
  let g : Point → ℂ := M ∘ ratioScale 0
  let p (z : Point) := f z • g z
  have hD : IsOpen D := hU.prod isOpen_Ioo
  have hzMap : MapsTo (ratioScale 0) D D := ratioScale_mapsTo ha hb ⟨le_rfl, zero_le_one⟩
  have finiteOrder (i : ℕ) : (i : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (i : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  have hf : ContDiffOn ℝ 100 f D :=
    ((hχ.of_le (finiteOrder 100)).comp_continuousLinearMap (g := R)).contDiffOn
  have hg : ContDiffOn ℝ 100 g D := (hM.comp_continuousLinearMap (ratioScale 0)).mono hzMap
  have hp : ContDiffOn ℝ 100 p D := hf.smul hg
  have hN : numerator M χ = fun z => M z - p z := by
    funext z
    simp [numerator, endpoint, p, f, g, R, Function.comp_def]
  refine ⟨by rw [hN]; exact hM.sub hp, ?_⟩
  intro j hj z hz
  have hj' : (j : WithTop ℕ∞) ≤ 100 := by exact_mod_cast hj
  have hR : ‖R‖ ≤ 1 := R.opNorm_le_bound zero_le_one fun w => by
    change ‖w.2‖ ≤ 1 * ‖w‖
    simpa only [one_mul] using norm_snd_le w
  have hF (i : ℕ) (hi : i ≤ j) : ‖iteratedFDerivWithin ℝ i f D z‖ ≤ K := by
    rw [iteratedFDerivWithin_of_isOpen i hD hz]
    exact (norm_iteratedFDeriv_comp_linear_le isOpen_univ hχ.contDiffOn R
      hR (mem_univ _) (finiteOrder i)).trans
        (boundχ i (hi.trans hj) z.2 ⟨hz.2.1.le, hz.2.2.le⟩)
  have hG (i : ℕ) (hi : i ≤ j) : ‖iteratedFDerivWithin ℝ i g D z‖ ≤ A := by
    rw [iteratedFDerivWithin_of_isOpen i hD hz]
    exact (norm_iteratedFDeriv_comp_linear_le hD hM (ratioScale 0)
      (ratioScale_norm_le ⟨le_rfl, zero_le_one⟩) (hzMap hz) (by exact_mod_cast (hi.trans hj))).trans
        (boundM i (hi.trans hj) _ (hzMap hz))
  have hP : ‖iteratedFDeriv ℝ j p z‖ ≤ (2 : ℝ)^j * K * A := by
    rw [← iteratedFDerivWithin_of_isOpen j hD hz]
    refine (norm_iteratedFDerivWithin_smul_le hf hg hD.uniqueDiffOn hz hj').trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * K * A := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hF i hi') (by positivity))
          (hG (j - i) (Nat.sub_le j i)) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
  have hSum : iteratedFDeriv ℝ j (numerator M χ) z =
      iteratedFDeriv ℝ j M z - iteratedFDeriv ℝ j p z := by
    have hNeg : ContDiffAt ℝ j (-p) z := ((hp.of_le hj').contDiffAt (hD.mem_nhds hz)).neg
    rw [hN, show (fun w => M w - p w) = M + -p from rfl,
      iteratedFDeriv_add_apply ((hM.of_le hj').contDiffAt (hD.mem_nhds hz)) hNeg,
      iteratedFDeriv_neg_apply, sub_eq_add_neg]
  rw [hSum]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j M z‖ + ‖iteratedFDeriv ℝ j p z‖ := norm_sub_le _ _
    _ ≤ A + (2 : ℝ)^j * K * A := add_le_add (boundM j hj z hz) hP
    _ ≤ A + (2 : ℝ)^100 * K * A := add_le_add_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hj) hK) hA) _
    _ = _ := by ring

/-- One derivative is spent at the nonzero low/high endpoint. The common
operator-norm jet budget depends only on the fixed cutoff and ratio window. -/
theorem exists_remainder_budget (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hone : χ 0 = 1)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Set Angles}, IsOpen U → ∀ (M : Point → ℂ) (A : ℝ),
      0 ≤ A → ContDiffOn ℝ 100 M (Window U a b) →
      (∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j M z‖ ≤ A) →
      ContDiffOn ℝ 99 (remainder M χ) (Window U a b) ∧
        ∀ j ≤ 99, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j (remainder M χ) z‖ ≤ C * A := by
  obtain ⟨K, hK, bound⟩ := cutoff_uniform_bound χ hχ a b
  refine ⟨1 + 2^100 * K, by positivity, ?_⟩
  intro U hU M A hA hM boundM
  obtain ⟨hN, boundN⟩ := numerator_jets hU ha hb M χ hM hχ A K hA hK boundM bound
  exact remainder_jets_of_numerator hU ha hb M χ hone hN _ boundN

/-- Fixed real cutoffs that are one near the ratio axis and supported in
the prescribed low/high ratio window. -/
theorem exists_fixed_ratio_cutoff {R : ℝ} (hR : 0 < R) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ χ =ᶠ[𝓝 (0 : ℝ)] 1 ∧
      tsupport χ ⊆ Icc (-R) R := by
  let χ : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.eventuallyEq_one, ?_⟩
  rw [χ.tsupport_eq]
  intro r hr
  have h := Metric.mem_closedBall.mp hr
  simpa [Real.dist_eq, abs_le, χ] using h

theorem remainder_fixed_ratio_support (M : Point → ℂ) (χ : ℝ → ℝ) (hχ : χ 0 = 1)
    {S : Set ℝ} (hM : tsupport M ⊆ Prod.snd ⁻¹' S) (hs : tsupport χ ⊆ S) :
    tsupport (remainder M χ) ⊆ Prod.snd ⁻¹' S :=
  (remainder_tsupport_subset M χ hχ).trans (union_subset hM fun _ h => hs h.1)

end Burnett.Analysis.LowRatio
