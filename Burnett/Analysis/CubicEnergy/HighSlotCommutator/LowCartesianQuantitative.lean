import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianSeminorm

set_option autoImplicit false
set_option maxHeartbeats 7800000

noncomputable section

open Set Metric Filter
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Topology

namespace Burnett.A06

private def highNonzero : Set Joint := {x | x.2 ≠ 0}

private theorem isOpen_highNonzero : IsOpen highNonzero :=
  isOpen_ne_fun continuous_snd continuous_const

private theorem normalizedHighPair_contDiffOn (n : WithTop ℕ∞) :
    ContDiffOn ℝ n normalizedHighPair highNonzero := by
  intro x hx
  have hs : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖) x := contDiffAt_snd.norm ℝ hx
  have hi : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖⁻¹) x := hs.inv (norm_ne_zero_iff.mpr hx)
  exact ((hi.smul contDiffAt_fst).prodMk (hi.smul contDiffAt_snd)).contDiffWithinAt

private def cartesianAmplitude (η χ : ℝ → ℝ) (x : Joint) : ℝ :=
  η ‖x.2‖ * ‖x.2‖ * χ (‖(normalizedHighPair x).1‖ ^ 2)

private theorem cartesianAmplitude_contDiffOn (n : ℕ) (η χ : ℝ → ℝ)
    (hη : ContDiff ℝ n η) (hχ : ContDiff ℝ n χ) :
    ContDiffOn ℝ n (cartesianAmplitude η χ) highNonzero := by
  intro x hx
  have hs : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖) x := contDiffAt_snd.norm ℝ hx
  have hp := ((normalizedHighPair_contDiffOn n) x hx).contDiffAt (isOpen_highNonzero.mem_nhds hx)
  have hz : ContDiffAt ℝ n (fun y : Joint => ‖(normalizedHighPair y).1‖^2) x :=
    (contDiffAt_fst.comp x hp).norm_sq ℝ
  exact (((hη.contDiffAt.comp x hs).mul hs).mul (hχ.contDiffAt.comp x hz)).contDiffWithinAt

/-- The chart and fixed multipliers have bounded jets on the same compact window. -/
private theorem exists_fixed_window_jet_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {K : Set Joint} (hK : IsCompact K) (hKU : K ⊆ highNonzero)
    (g : Joint → F) (hg : ContDiffOn ℝ n g highNonzero) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ A := by
  have oneOrder (i : ℕ) (hi : i ≤ n) :
      ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    have hi' : (i : WithTop ℕ∞) ≤ n := by exact_mod_cast hi
    have con : ContinuousOn (iteratedFDeriv ℝ i g) highNonzero :=
      (hg.continuousOn_iteratedFDerivWithin hi' isOpen_highNonzero.uniqueDiffOn).congr
        (iteratedFDerivWithin_of_isOpen i isOpen_highNonzero).symm
    obtain ⟨C,hC⟩ := hK.bddAbove_image (con.norm.mono hKU)
    exact ⟨C, fun x hx => hC (mem_image_of_mem _ hx)⟩
  choose C hC using fun i : Fin (n+1) => oneOrder i.val (Nat.le_of_lt_succ i.isLt)
  let A := ∑ i : Fin (n+1), max (C i) 0
  refine ⟨max 1 A, le_max_left _ _, ?_⟩
  intro i hi x hx
  let j : Fin (n+1) := ⟨i, Nat.lt_succ_of_le hi⟩
  have lin : max (C j) 0 ≤ A := by
    classical
    exact Finset.single_le_sum (f := fun k : Fin (n+1) => max (C k) 0)
      (fun k _ => le_max_right _ _) (Finset.mem_univ j)
  exact ((hC j x hx).trans (le_max_left _ _)).trans (lin.trans (le_max_right _ _))

private theorem exists_cartesian_amplitude_comp_window_bound
    (n : ℕ) {K : Set Joint} (hK : IsCompact K) (hKU : K ⊆ highNonzero)
    (w : Joint → ℝ) (hw : ContDiffOn ℝ n w highNonzero)
    {ρ : ℝ} (himage : MapsTo normalizedHighPair K (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ n c V →
      (∀ i ≤ n, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ i c z‖ ≤ B) →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ n (fun y => w y • c (normalizedHighPair y)) x‖ ≤ C*B := by
  have hp := normalizedHighPair_contDiffOn n
  obtain ⟨A,hA,ja⟩ := exists_fixed_window_jet_bound n hK hKU w hw
  obtain ⟨D,hD,jp⟩ := exists_fixed_window_jet_bound n hK hKU normalizedHighPair hp
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let C : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * A * ((n-i).factorial * D^(n-i))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro V hV hContains c B hB hc cb x hx
  let S := highNonzero ∩ normalizedHighPair ⁻¹' V
  have hS : IsOpen S := hp.continuousOn.isOpen_inter_preimage isOpen_highNonzero hV
  have hz := himage hx
  have hzV := hContains hz
  have hxS : x ∈ S := ⟨hKU hx, hzV⟩
  have hmap : MapsTo normalizedHighPair S V := fun _ hy => hy.2
  have haS : ContDiffOn ℝ n w S := hw.mono inter_subset_left
  have hpS : ContDiffOn ℝ n normalizedHighPair S := hp.mono inter_subset_left
  have hbS : ContDiffOn ℝ n (c ∘ normalizedHighPair) S := hc.comp hpS hmap
  have dcomp (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDerivWithin ℝ j (c ∘ normalizedHighPair) S x‖ ≤ j.factorial * B * D^j := by
    have hj' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
    refine norm_iteratedFDerivWithin_comp_le hc hpS hj' hV.uniqueDiffOn hS.uniqueDiffOn hmap hxS ?_ ?_
    · intro i hi
      rw [iteratedFDerivWithin_of_isOpen i hV hzV]
      exact cb i (hi.trans hj) _ hz
    · intro i hi hij
      rw [iteratedFDerivWithin_of_isOpen i hS hxS]
      exact (jp i (hij.trans hj) x hx).trans (le_self_pow₀ hD (Nat.ne_of_gt hi))
  rw [← iteratedFDerivWithin_of_isOpen n hS hxS]
  have prodBound := norm_iteratedFDerivWithin_smul_le haS hbS hS.uniqueDiffOn hxS
    (le_rfl : (n : WithTop ℕ∞) ≤ n)
  refine prodBound.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * A * ((n-i).factorial * B * D^(n-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [iteratedFDerivWithin_of_isOpen i hS hxS]
      refine mul_le_mul ?_ (dcomp (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (ja i hi' x hx) (by positivity)
    _ = C*B := by
      dsimp [C]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem regularized_eq_amplitude (η χ : ℝ → ℝ) (c : Joint → ℂ) :
    regularizedLowCartesianSymbol η χ c = fun x => cartesianAmplitude η χ x • c (normalizedHighPair x) := by
  funext x
  simp only [regularizedLowCartesianSymbol, lowCartesianSymbol, cartesianAmplitude, mul_smul]

private theorem unregularized_eq_amplitude (χ : ℝ → ℝ) (c : Joint → ℂ) :
    lowCartesianSymbol χ c = fun x => cartesianAmplitude (fun _ => 1) χ x • c (normalizedHighPair x) := by
  funext x
  simp only [lowCartesianSymbol, cartesianAmplitude, one_mul, mul_smul]

/-- With fixed radial cutoffs, the order-one seminorm is linear in the
finite jet budget on the actual normalized independent-variable window. -/
theorem exists_regularizedLowCartesianSymbol_quantitative_orderOne_bound
    (n : ℕ) (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ n η) (hηzero : ∀ s ≤ r, η s = 0) (hηone : ∀ s ≥ R, η s = 1)
    (hχ : ContDiff ℝ n χ) (hcut : ∀ s ≥ ρ^2, χ s = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ n c V →
      (∀ i ≤ n, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ i c z‖ ≤ B) →
      ∀ x : Joint, ‖iteratedFDeriv ℝ n (regularizedLowCartesianSymbol η χ c) x‖ *
        (1 + ‖x.1‖ + ‖x.2‖)^n ≤ C * B * (1 + ‖x.1‖ + ‖x.2‖) := by
  let r₀ := min r 1
  let K : Set Joint := {x | r₀ ≤ ‖x.2‖ ∧ ‖x.2‖ ≤ R ∧ ‖x.1‖ ≤ ρ * ‖x.2‖}
  let L := closedBall (0 : E) (ρ*R) ×ˢ closedBall (0 : E) R
  have hr₀ : 0 < r₀ := lt_min hr zero_lt_one
  have hKL : K ⊆ L := fun x hx =>
    ⟨mem_closedBall_zero_iff.mpr (hx.2.2.trans (mul_le_mul_of_nonneg_left hx.2.1 hρ)),
      mem_closedBall_zero_iff.mpr hx.2.1⟩
  have clK : IsClosed K :=
    (isClosed_le continuous_const continuous_snd.norm).inter
      ((isClosed_le continuous_snd.norm continuous_const).inter
        (isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd.norm)))
  have compactL : IsCompact L :=
    (isCompact_closedBall (0 : E) (ρ*R)).prod (isCompact_closedBall (0 : E) R)
  have compactK := compactL.of_isClosed_subset clK hKL
  have subU : K ⊆ highNonzero := fun _ hx => norm_pos_iff.mp (hr₀.trans_le hx.1)
  have mapK : MapsTo normalizedHighPair K (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) := by
    intro x hx
    have hq := hr₀.trans_le hx.1
    refine ⟨mem_closedBall_zero_iff.mpr ?_,
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) (subU hx))⟩
    change ‖‖x.2‖⁻¹ • x.1‖ ≤ ρ
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hq.le), mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hq).mpr hx.2.2
  obtain ⟨A,hA,unit⟩ := exists_cartesian_amplitude_comp_window_bound n compactK subU
    (cartesianAmplitude (fun _ => 1) χ) (cartesianAmplitude_contDiffOn n _ _ contDiff_const hχ) mapK
  obtain ⟨D,hD,transition⟩ := exists_cartesian_amplitude_comp_window_bound n compactK subU
    (cartesianAmplitude η χ) (cartesianAmplitude_contDiffOn n _ _ hη hχ) mapK
  let C := A*(2+ρ)^n + D*(1+(ρ+1)*R)^n
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro V hV hContains c B hB hc cb x
  have hu (y : Joint) (hy : y ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ n (lowCartesianSymbol χ c) y‖ ≤ A*B := by
    have one : ‖y.2‖ = 1 := mem_sphere_zero_iff_norm.mp hy.2
    have low : ‖y.1‖ ≤ ρ := mem_closedBall_zero_iff.mp hy.1
    have hyK : y ∈ K := by
      exact ⟨(min_le_right r 1).trans_eq one.symm, one.trans_le hR, by simpa only [one, mul_one] using low⟩
    rw [unregularized_eq_amplitude]
    exact unit hV hContains c B hB hc cb y hyK
  have hf (y : Joint) (hy : y ∈ L) :
      ‖iteratedFDeriv ℝ n (regularizedLowCartesianSymbol η χ c) y‖ ≤ D*B := by
    by_cases hlow : ‖y.1‖ ≤ ρ*‖y.2‖
    · by_cases hradius : r ≤ ‖y.2‖
      · have hyK : y ∈ K :=
          ⟨(min_le_left r 1).trans hradius, mem_closedBall_zero_iff.mp hy.2, hlow⟩
        rw [regularized_eq_amplitude]
        exact transition hV hContains c B hB hc cb y hyK
      · have near : ∀ᶠ z : Joint in 𝓝 y, ‖z.2‖ < r :=
          (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (lt_of_not_ge hradius)
        have zero : regularizedLowCartesianSymbol η χ c =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [near] with z hz
          simp only [regularizedLowCartesianSymbol, hηzero _ hz.le, zero_smul]
        rw [(zero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
        positivity
    · have near : ∀ᶠ z : Joint in 𝓝 y, ρ * ‖z.2‖ < ‖z.1‖ :=
        (isOpen_lt (continuous_const.mul continuous_snd.norm) continuous_fst.norm).mem_nhds
          (lt_of_not_ge hlow)
      have zero : regularizedLowCartesianSymbol η χ c =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [near] with z hz
        simp only [regularizedLowCartesianSymbol,
          lowCartesianSymbol_eq_zero_outside χ c hρ hcut hz.le, smul_zero]
      rw [(zero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
      positivity
  refine (regularizedLowCartesianSymbol_seminorm_of_windows n η χ c hρ hR hηone hχ hcut
    hV hContains hc (mul_nonneg hA hB) (mul_nonneg hD hB) hu hf x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply max_le
  · exact (show A * B * (2+ρ)^n = (A*(2+ρ)^n)*B by ring).le.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ D*(1+(ρ+1)*R)^n)) hB)
  · exact (show D * B * (1+(ρ+1)*R)^n = (D*(1+(ρ+1)*R)^n)*B by ring).le.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity : 0 ≤ A*(2+ρ)^n)) hB)

end Burnett.A06
