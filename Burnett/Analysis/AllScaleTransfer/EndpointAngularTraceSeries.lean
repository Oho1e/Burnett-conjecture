import Burnett.Analysis.AllScaleTransfer.EndpointAngularMultiplier
import Burnett.Analysis.AllScaleTransfer.GapBoxSeries
import Burnett.Analysis.AllScaleTransfer.LowRatioSplit

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory
open Burnett.A05.BoxFourier
open Burnett.Analysis.LowRatio (Angles Point Window endpoint)
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff BigOperators Topology ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

abbrev EndpointAngle := EuclideanSpace ℝ (Fin 3)

/-- In either fixed signed hemisphere, the last three coordinates are the angular chart. -/
def endpointTail : E →L[ℝ] EndpointAngle :=
  ({toFun := fun x => WithLp.toLp 2 (fun i : Fin 3 => x i.succ)
    map_add' := fun _ _ => by ext i; rfl
    map_smul' := fun _ _ => by ext i; rfl} : E →ₗ[ℝ] EndpointAngle).toContinuousLinearMap

@[simp] theorem endpointTail_apply (x : E) (i : Fin 3) : endpointTail x i = x i.succ := rfl

theorem endpointTail_norm_sq (x : E) :
    ‖endpointTail x‖ ^ 2 + (x 0) ^ 2 = ‖x‖ ^ 2 := by
  have split : (∑ i : Fin 4, ‖x i‖^2) = ‖x 0‖^2 + ∑ i : Fin 3, ‖x i.succ‖^2 :=
    Fin.sum_univ_succ (fun i : Fin 4 => ‖x i‖^2)
  rw [EuclideanSpace.norm_sq_eq (endpointTail x), EuclideanSpace.norm_sq_eq x, split]
  simp only [endpointTail_apply, Real.norm_eq_abs, sq_abs]
  ring

/-- The tail determines the magnitude of the missing coordinate. The chart
uses the sign of that coordinate rather than identifying opposite directions. -/
theorem endpointTail_head_abs {x : E} (hx : x ∈ sphere (0 : E) 1) :
    |x 0| = Real.sqrt (1 - ‖endpointTail x‖ ^ 2) := by
  have ht : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  have h := endpointTail_norm_sq x
  rw [ht, one_pow] at h
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  linarith only [h]

theorem endpointTail_axial_bound {x : E} (hx : x ∈ sphere (0 : E) 1)
    {α : ℝ} (hα : 0 ≤ α) (hAxis : α ≤ |x 0|) :
    ‖endpointTail x‖ ^ 2 ≤ 1 - α ^ 2 := by
  have ht : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  have h := endpointTail_norm_sq x
  rw [ht, one_pow] at h
  have hc := pow_le_pow_left₀ hα hAxis 2
  rw [sq_abs] at hc
  linarith only [h,hc]

/-- A uniform axial margin gives two fixed radii strictly inside either
hemisphere chart. -/
theorem exists_endpointTail_radii {α : ℝ} (hα : 0 < α) (hαone : α ≤ 1) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ R < 1 ∧
      ∀ x ∈ sphere (0 : E) 1, α ≤ |x 0| → ‖endpointTail x‖ ≤ r := by
  let t := Real.sqrt (1 - α ^ 2)
  have hrad : 0 ≤ 1 - α ^ 2 := sub_nonneg.mpr (pow_le_one₀ hα.le hαone)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htKey : t ^ 2 = 1 - α ^ 2 := Real.sq_sqrt hrad
  have ht : t < 1 := by
    apply (sq_lt_sq₀ ht0 zero_le_one).mp
    rw [htKey, one_pow]
    exact sub_lt_self _ (pow_pos hα _)
  let r := (t+1)/2
  let R := (r+1)/2
  have hr : t < r := by dsimp only [r]; linarith only [ht]
  have hr1 : r < 1 := by dsimp only [r]; linarith only [ht]
  refine ⟨r,R,ht0.trans_lt hr,by dsimp only [R]; linarith only [hr1],
    by dsimp only [R]; linarith only [hr1],?_⟩
  intro x hx hAxis
  have h : ‖endpointTail x‖ ≤ t :=
    (sq_le_sq₀ (norm_nonneg _) ht0).mp (htKey.symm ▸ endpointTail_axial_bound hx hα.le hAxis)
  exact h.trans hr.le

private def firstBoxCLM : BoxSpace →L[ℝ] E :=
  ({toFun := firstInput
    map_add' := fun _ _ => by ext i; rfl
    map_smul' := fun _ _ => by ext i; rfl} : BoxSpace →ₗ[ℝ] E).toContinuousLinearMap

private def secondBoxCLM : BoxSpace →L[ℝ] E :=
  ({toFun := secondInput
    map_add' := fun _ _ => by ext i; rfl
    map_smul' := fun _ _ => by ext i; rfl} : BoxSpace →ₗ[ℝ] E).toContinuousLinearMap

private def endpointBoxAngles : BoxSpace →L[ℝ] Angles :=
  (endpointTail.comp firstBoxCLM).prod (endpointTail.comp secondBoxCLM)

def endpointBoxTraceMap : BoxSpace →L[ℝ] Point := endpointBoxAngles.prod 0

theorem endpointBoxTraceMap_joined (u v : E) :
    endpointBoxTraceMap (joinedInputs u v) = ((endpointTail u, endpointTail v), 0) := by
  change ((endpointTail (firstInput (joinedInputs u v)), endpointTail (secondInput (joinedInputs u v))), 0) = _
  rw [firstInput_joined, secondInput_joined]

def endpointTraceCutoff {r R : ℝ} (hr : 0 < r) (hR : r < R) (z : BoxSpace) : ℝ :=
  let bump : ContDiffBump (0 : EndpointAngle) := ⟨r,R,hr,hR⟩
  bump (endpointTail (firstInput z)) * bump (endpointTail (secondInput z))

private theorem endpointTraceCutoff_contDiff {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ContDiff ℝ ∞ (endpointTraceCutoff hr hR) := by
  let bump : ContDiffBump (0 : EndpointAngle) := ⟨r,R,hr,hR⟩
  exact (bump.contDiff.comp (endpointTail.comp firstBoxCLM).contDiff).mul
    (bump.contDiff.comp (endpointTail.comp secondBoxCLM).contDiff)

private theorem endpointTraceCutoff_support {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    tsupport (endpointTraceCutoff hr hR) ⊆
      endpointBoxAngles ⁻¹' (closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R) := by
  let bump : ContDiffBump (0 : EndpointAngle) := ⟨r,R,hr,hR⟩
  apply closure_minimal ?_ ((isClosed_closedBall.prod isClosed_closedBall).preimage endpointBoxAngles.continuous)
  intro z hz
  change bump (endpointTail (firstInput z)) * bump (endpointTail (secondInput z)) ≠ 0 at hz
  have h₁ := left_ne_zero_of_mul hz
  have h₂ := right_ne_zero_of_mul hz
  have hs (u : EndpointAngle) (hu : bump u ≠ 0) : u ∈ closedBall (0 : EndpointAngle) R := by
    have ht : u ∈ tsupport (bump : EndpointAngle → ℝ) := subset_closure hu
    rwa [bump.tsupport_eq] at ht
  exact ⟨hs _ h₁, hs _ h₂⟩

private theorem endpointTraceCutoff_one {r R : ℝ} (hr : 0 < r) (hR : r < R) {u v : E}
    (hu : ‖endpointTail u‖ ≤ r) (hv : ‖endpointTail v‖ ≤ r) :
    endpointTraceCutoff hr hR (joinedInputs u v) = 1 := by
  let bump : ContDiffBump (0 : EndpointAngle) := ⟨r,R,hr,hR⟩
  change bump (endpointTail (firstInput (joinedInputs u v))) *
    bump (endpointTail (secondInput (joinedInputs u v))) = 1
  rw [firstInput_joined, secondInput_joined, bump.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hu),
    bump.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hv), mul_one]

def endpointBoxProfile {r R : ℝ} (hr : 0 < r) (hR : r < R) (M : Point → ℂ) (z : BoxSpace) : ℂ :=
  endpointTraceCutoff hr hR z • M (endpointBoxTraceMap z)

private theorem endpointBoxProfile_jets {U : Set Angles} (hU : IsOpen U) {a b r R P : ℝ}
    (ha : a < 0) (hb : 0 < b) (hr : 0 < r) (hR : r < R)
    (hChart : closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Point → ℂ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 100 M (Window U a b) →
      (∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j M z‖ ≤ A) →
      ContDiff ℝ 100 (endpointBoxProfile hr hR M) ∧
      ∀ j ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P,
        ‖iteratedFDeriv ℝ j (endpointBoxProfile hr hR M) z‖ ≤ C * A := by
  let χ := endpointTraceCutoff hr hR
  let L := endpointBoxTraceMap
  let Q := Window U a b
  let D := L ⁻¹' Q
  have hQ : IsOpen Q := hU.prod isOpen_Ioo
  have hD : IsOpen D := hQ.preimage L.continuous
  have hSupp : tsupport χ ⊆ D := by
    intro z hz
    exact ⟨hChart (endpointTraceCutoff_support hr hR hz),ha,hb⟩
  have hχ : ContDiff ℝ ∞ χ := endpointTraceCutoff_contDiff hr hR
  have Kbound (j : Fin 41) :
      ∃ K : ℝ, ∀ z ∈ closedBall (0 : BoxSpace) P, ‖iteratedFDeriv ℝ j.val χ z‖ ≤ K := by
    have hc := hχ.continuous_iteratedFDeriv (m := j.val) (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨K,hK⟩ := (isCompact_closedBall (0 : BoxSpace) P).bddAbove_image hc.norm.continuousOn
    exact ⟨K,fun z hz => hK (mem_image_of_mem _ hz)⟩
  choose K hK using Kbound
  let B := ∑ j : Fin 41, max (K j) 0
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => le_max_right _ _
  have bχ (j : ℕ) (hj : j ≤ 40) (z : BoxSpace) (hz : z ∈ closedBall (0 : BoxSpace) P) :
      ‖iteratedFDeriv ℝ j χ z‖ ≤ B := by
    let i : Fin 41 := ⟨j,by omega⟩
    exact (hK i z hz).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => le_max_right (K l) 0) (Finset.mem_univ i)))
  let W := max 1 ‖L‖
  have hW : 1 ≤ W := le_max_left _ _
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  refine ⟨(2 : ℝ)^40 * B * W^40,by positivity,?_⟩
  intro M A hA hM budget
  let f := endpointBoxProfile hr hR M
  let g := M ∘ L
  have hχ100 : ContDiffOn ℝ 100 χ D :=
    (hχ.of_le (show (100 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hG : ContDiffOn ℝ 100 g D := hM.comp_continuousLinearMap L
  have hF : ContDiffOn ℝ 100 f D := hχ100.smul hG
  have zeroOutside (z : BoxSpace) (hz : z ∉ D) : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hSupp h))] with x hx
    change χ x = 0 at hx
    change χ x • M (L x) = 0
    rw [hx,zero_smul]
  refine ⟨contDiff_iff_contDiffAt.mpr (fun z => ?_),?_⟩
  · by_cases hz : z ∈ D
    · exact hF.contDiffAt (hD.mem_nhds hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (zeroOutside z hz)
  intro n hn z hz
  by_cases hzD : z ∈ D
  · have hGjet (i : ℕ) (hi : i ≤ 40) :
        ‖iteratedFDerivWithin ℝ i g D z‖ ≤ W ^ 40 * A := by
      have hi' : (i : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (show i ≤ 100 by omega)
      rw [L.iteratedFDerivWithin_comp_right hM hQ.uniqueDiffOn hD.uniqueDiffOn (show L z ∈ Q from hzD) hi',
        iteratedFDerivWithin_of_isOpen i hQ (show L z ∈ Q from hzD)]
      calc
        _ ≤ ‖iteratedFDeriv ℝ i M (L z)‖ * ‖L‖ ^ i := by
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ i M (L z))
              (fun _ : Fin i => L))
        _ ≤ A * W^40 := mul_le_mul (budget i (by omega) (L z) hzD)
          ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ hW hi))
          (by positivity) hA
        _ = _ := mul_comm _ _
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (show n ≤ 100 by omega)
    rw [← iteratedFDerivWithin_of_isOpen n hD hzD]
    change ‖iteratedFDerivWithin ℝ n (fun x => χ x • g x) D z‖ ≤ _
    refine (norm_iteratedFDerivWithin_smul_le hχ100 hG hD.uniqueDiffOn hzD hn').trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * (W^40 * A) := by
        apply Finset.sum_le_sum
        intro i hi
        have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [iteratedFDerivWithin_of_isOpen i hD hzD]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (bχ i (hile.trans hn) z (ball_subset_closedBall hz))
            (by positivity)) (hGjet (n-i) ((Nat.sub_le _ _).trans hn)) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^n * B * (W^40 * A) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
      _ ≤ (2 : ℝ)^40 * B * (W^40 * A) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hB) (by positivity)
      _ = _ := by ring
  · have hf : z ∉ tsupport f := notMem_tsupport_iff_eventuallyEq.mpr (zeroOutside z hzD)
    have hz0 : iteratedFDeriv ℝ n f z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hf (tsupport_iteratedFDeriv_subset n h))
    change ‖iteratedFDeriv ℝ n f z‖ ≤ _
    rw [hz0,norm_zero]
    positivity

theorem norm_joinedInputs_sq (u v : E) : ‖joinedInputs u v‖^2 = ‖u‖^2 + ‖v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq (joinedInputs u v), EuclideanSpace.norm_sq_eq u,
    EuclideanSpace.norm_sq_eq v, Fintype.sum_sum_type]
  rfl

theorem separatedBoxMode_endpoint (P : ℝ) (ab : FourierModePair) (p q : E) :
    separatedBoxMode P ab (joinedInputs (endpointDirection p) (endpointDirection q)) =
      endpointModeSymbol P ab.1 p * endpointModeSymbol P ab.2 q := by
  simp only [separatedBoxMode,firstInput_joined,secondInput_joined,endpointModeSymbol,endpointModePhase]

/-- A fixed signed angular chart pair gives the actual M₀ trace expansion in
the same two physical angular modes, together with the weighted coefficient sum. -/
theorem exists_endpointTrace_angular_series {U : Set Angles} (hU : IsOpen U)
    {a b r R P : ℝ} (ha : a < 0) (hb : 0 < b) (hr : 0 < r) (hR : r < R) (hP : 2 < P)
    (hChart : closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U) :
    ∃ (χ : BoxSpace → ℝ) (C : ℝ), 0 ≤ C ∧ ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ ball (0 : BoxSpace) P ∧
      ∀ (M : Point → ℂ) (A : ℝ), 0 ≤ A → ContDiffOn ℝ 100 M (Window U a b) →
        (∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j M z‖ ≤ A) →
        let c (ab : FourierModePair) := boxCubeFourierCoefficient P (modeIndex ab)
          (fun z => χ z • endpointBoxProfile hr hR M z)
        (∀ ab, ‖c ab‖ ≤ C * A * modePairDecay ab) ∧
        Summable (weightedModeCoefficient c) ∧
        (∑' ab, weightedModeCoefficient c ab) ≤ C * A * modePairSummationConstant ∧
        ∀ (p q : E), p ≠ 0 → q ≠ 0 → ‖endpointTail (endpointDirection p)‖ ≤ r →
          ‖endpointTail (endpointDirection q)‖ ≤ r →
          HasSum (fun ab => c ab * (endpointModeSymbol P ab.1 p * endpointModeSymbol P ab.2 q))
            (endpoint M (endpointTail (endpointDirection p), endpointTail (endpointDirection q))) := by
  obtain ⟨χ,C₀,hχ,hSupport,_,hC₀,series⟩ := exists_normalized_gap_box_series 2 P (by norm_num) hP
  obtain ⟨B,hB,profile⟩ := endpointBoxProfile_jets (P := P) hU ha hb hr hR hChart
  refine ⟨χ,C₀*B,by positivity,hχ,hSupport,?_⟩
  intro M A hA hM budget c
  let f := endpointBoxProfile hr hR M
  obtain ⟨smooth, bound⟩ := profile M A hA hM budget
  let F (s : ℕ) : BoxSpace → ℂ := if s = 0 then f else 0
  have hF (s : ℕ) : ContDiffOn ℝ 99 (F s) (ball (0 : BoxSpace) P) := by
    by_cases hs : s = 0
    · simpa only [F, hs, if_true] using (smooth.of_le (by norm_num : (99 : WithTop ℕ∞) ≤ 100)).contDiffOn
    · simpa only [F, hs, if_false] using (contDiffOn_const : ContDiffOn ℝ 99 (0 : BoxSpace → ℂ) (ball 0 P))
  have hJet (s j : ℕ) (hj : j ≤ 40) (z : BoxSpace) (hz : z ∈ ball (0 : BoxSpace) P) :
      ‖iteratedFDeriv ℝ j (F s) z‖ ≤ (B * A) * radialGapDecay s := by
    by_cases hs : s = 0
    · simpa only [F, hs, if_true, radialGapDecay, pow_zero, mul_one] using bound j hj z hz
    · have hzF : F s = fun _ : BoxSpace => (0 : ℂ) := if_neg hs
      rw [hzF, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
      unfold radialGapDecay
      positivity
  obtain ⟨coeff, values⟩ := series F (B*A) (by positivity) hF hJet 0
  have hc (ab : FourierModePair) : ‖c ab‖ ≤ C₀ * B * A * modePairDecay ab := by
    simpa only [c,F,if_true,radialGapDecay,pow_zero,mul_one,mul_assoc] using coeff ab
  have hc0 (ab : FourierModePair) : ‖c ab‖ ≤ (C₀*B*A) * radialGapDecay 0 * modePairDecay ab := by
    simpa only [radialGapDecay,pow_zero,mul_one] using hc ab
  obtain ⟨weighted, hWeighted, _⟩ :=
    weighted_fourier_modes_at_gap c (C₀*B*A) (by positivity) 0 hc0
  refine ⟨hc,weighted,by simpa only [radialGapDecay,pow_zero,mul_one] using hWeighted,?_⟩
  intro p q hp hq hpAngle hqAngle
  let u := endpointDirection p
  let v := endpointDirection q
  let z := joinedInputs u v
  have hu : ‖u‖ = 1 := by simpa only [u,mem_sphere,dist_zero_right] using endpointDirection_mem_sphere hp
  have hv : ‖v‖ = 1 := by simpa only [v,mem_sphere,dist_zero_right] using endpointDirection_mem_sphere hq
  have hz : z ∈ closedBall (0 : BoxSpace) 2 := by
    apply mem_closedBall_zero_iff.mpr
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp
    change ‖joinedInputs u v‖ ^ 2 ≤ 2 ^ 2
    rw [norm_joinedInputs_sq, hu, hv]
    norm_num
  have htrace : F 0 z = endpoint M (endpointTail u,endpointTail v) := by
    change endpointTraceCutoff hr hR (joinedInputs u v) • M (endpointBoxTraceMap (joinedInputs u v)) = _
    rw [endpointTraceCutoff_one hr hR hpAngle hqAngle,one_smul,endpointBoxTraceMap_joined]
    rfl
  have hs := (values z hz).2
  rw [htrace] at hs
  simpa only [F, c, if_true, z, u, v, separatedBoxMode_endpoint] using hs

/-- The weighted coefficients control the sum of the two actual angular
operator norms. The same multiplier family works for every coefficient family. -/
theorem exists_endpointMode_pairOperator_summation (P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ R : FourierMode → (EndpointLp3 →L[ℂ] EndpointLp3),
      (∀ (a : FourierMode) (f : SchwartzMap E ℂ),
        (R a (f.toLp (ENNReal.ofReal 3) volume) : E → ℂ) =ᵐ[volume] endpointModeRadianAction P a f) ∧
      ∀ (c : FourierModePair → ℂ), Summable (weightedModeCoefficient c) →
        let term (ab : FourierModePair) := ‖c ab‖ * ‖R ab.1‖ * ‖R ab.2‖
        Summable term ∧ (∑' ab, term ab) ≤ C * ∑' ab, weightedModeCoefficient c ab := by
  obtain ⟨C,hC,operators⟩ := exists_endpointMode_L3_bound P
  choose R bound _checkL2 checkPaper using operators
  have opBound (a : FourierMode) : ‖R a‖ ≤ C * Burnett.A03.spatialLatticeWeight a ^ 6 :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (bound a)
  refine ⟨C^2, by positivity, R, checkPaper, ?_⟩
  intro c hs term
  have major (ab : FourierModePair) : term ab ≤ C^2 * weightedModeCoefficient c ab := by
    unfold term weightedModeCoefficient modePairLoss
    have h := mul_le_mul (opBound ab.1) (opBound ab.2) (norm_nonneg _)
      (by positivity : 0 ≤ C * Burnett.A03.spatialLatticeWeight ab.1 ^ 6)
    calc
      _ = ‖c ab‖ * (‖R ab.1‖ * ‖R ab.2‖) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring
  have ht := Summable.of_nonneg_of_le (fun ab => by unfold term; positivity) major (hs.mul_left (C^2))
  exact ⟨ht,(ht.tsum_le_tsum major (hs.mul_left (C^2))).trans_eq (hs.tsum_mul_left (C^2))⟩

end Burnett.A05
