import Burnett.Analysis.PrincipalEnergy.Freezing.SummedFourierAction
import Burnett.Analysis.SignedFourierWindow.SignedWindowAllLp
import Burnett.Analysis.PrincipalEnergy.Freezing.ModulatedAngularAction

set_option autoImplicit false
set_option maxHeartbeats 2650000
noncomputable section

namespace Burnett.A03

open Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.ShiftedFourierWindow (shiftedWindowOperator shifted_window_physical)

open Filter MeasureTheory Finset Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform RealInnerProductSpace BigOperators

/-- This form uses the normalized mathlib Fourier variable for a complex
symbol, as do the finite window estimates from the signed multiplier. -/
def normalizedComplexFourierAction (m : E → ℂ) (u : SchwartzMap E ℂ) : E → ℂ :=
  𝓕⁻ (fun ξ => m ξ * 𝓕 (u : E → ℂ) ξ)

theorem normalized_complex_fourier_action_integral (m : E → ℂ) (u : SchwartzMap E ℂ) (x : E) :
    normalizedComplexFourierAction m u x =
      ∫ ξ, patchFourierPhase ξ x * (m ξ * 𝓕 (u : E → ℂ) ξ) := by
  rw [normalizedComplexFourierAction, Real.fourierIntegralInv_eq']
  rfl

private theorem normalized_complex_spectrum_integrable (m : E → ℂ) (hm : Measurable m) (A : ℝ)
    (sup : ∀ ξ, ‖m ξ‖ ≤ A) (u : SchwartzMap E ℂ) :
    Integrable (fun ξ => m ξ * 𝓕 (u : E → ℂ) ξ) := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  refine (U.integrable.norm.const_mul A).mono' (hm.mul U.continuous.measurable).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (sup ξ) (norm_nonneg _)

theorem normalized_complex_fourier_action_continuous (m : E → ℂ) (hm : Measurable m) (A : ℝ)
    (sup : ∀ ξ, ‖m ξ‖ ≤ A) (u : SchwartzMap E ℂ) :
    Continuous (normalizedComplexFourierAction m u) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd).neg (normalized_complex_spectrum_integrable m hm A sup u)

/-- One fixed annular window and one fixed lattice phase allow arbitrary
bounded coefficients across the dyadic scales. -/
def groupedAnnularSymbol (a : SchwartzMap E ℂ) (t : ℝ) (q : E) (I : Finset ℕ) (c : ℕ → ℂ) (ξ : E) : ℂ :=
  ∑ j ∈ I, c j * patchFourierPhase (((2 : ℝ)^j * t) • ξ) q * a (((2 : ℝ)^j * t) • ξ)

private theorem group_symbol_continuous (a : SchwartzMap E ℂ) (t : ℝ) (q : E) (I : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (groupedAnnularSymbol a t q I c) := by
  unfold groupedAnnularSymbol patchFourierPhase Burnett.Microlocal.Overlap.baseFourierPhase
  exact continuous_finset_sum _ fun j _ => by fun_prop

private theorem group_symbol_bound (a : SchwartzMap E ℂ) (t : ℝ) (q : E) (I : Finset ℕ) (c : ℕ → ℂ)
    (D : ℝ) (hD : ∀ j, ‖c j‖ ≤ D) (ξ : E) :
    ‖groupedAnnularSymbol a t q I c ξ‖ ≤ D * (I.card * SchwartzMap.seminorm ℝ 0 0 a) := by
  calc
    _ ≤ ∑ j ∈ I, ‖c j * patchFourierPhase (((2 : ℝ)^j * t) • ξ) q * a (((2 : ℝ)^j * t) • ξ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ I, D * SchwartzMap.seminorm ℝ 0 0 a := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, patch_fourier_phase_norm, mul_one]
      exact mul_le_mul (hD j) (SchwartzMap.norm_le_seminorm ℝ a _) (norm_nonneg _) ((norm_nonneg _).trans (hD j))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private theorem group_fourier_action_eq_kernel (a u : SchwartzMap E ℂ) (t : ℝ) (ht : 0 < t)
    (q x : E) (I : Finset ℕ) (c : ℕ → ℂ) :
    normalizedComplexFourierAction (groupedAnnularSymbol a t q I c) u x =
      kernelApply (finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c) u x := by
  let s (j : ℕ) := (2 : ℝ)^j * t
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let K (j : ℕ) := shiftedSpatialKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) (s j) q
  let F (j : ℕ) (ξ : E) := (patchFourierPhase ξ x * patchFourierPhase (s j • ξ) q * a (s j • ξ)) * U ξ
  have ip (j : ℕ) : Integrable (F j) := by
    have cm : Continuous (F j) := by unfold F patchFourierPhase Burnett.Microlocal.Overlap.baseFourierPhase; fun_prop
    refine (U.integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 a)).mono' cm.aestronglyMeasurable ?_
    filter_upwards with ξ
    simp only [F, norm_mul, patch_fourier_phase_norm, one_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ a _) (norm_nonneg _)
  have h (j : ℕ) : (∫ ξ, F j ξ) = ∫ y, K j (x - y) * u y := by
    change shiftedWindowOperator a u (s j) q x = _
    exact shifted_window_physical a u (s j) (mul_pos (by positivity) ht) q x
  have v (j : ℕ) : Integrable (fun y => K j (x - y) * u y) := by
    let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
    let D := |(s j ^ 4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ
    refine (u.integrable.norm.const_mul D).mono' (by unfold K shiftedSpatialKernel; fun_prop) ?_
    filter_upwards with y
    simp only [K, shiftedSpatialKernel, norm_smul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (abs_nonneg _)) (norm_nonneg _)
  rw [normalized_complex_fourier_action_integral]
  have eq (ξ : E) :
      patchFourierPhase ξ x * (groupedAnnularSymbol a t q I c ξ * 𝓕 (u : E → ℂ) ξ) =
        ∑ j ∈ I, c j * F j ξ := by
    simp only [groupedAnnularSymbol, F, s, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change _ * (_ * U ξ) = _
    ring
  simp_rw [eq]
  rw [integral_finset_sum _ (fun j _ => (ip j).const_mul (c j))]
  simp_rw [integral_const_mul, h]
  simp_rw [← integral_const_mul]
  change (∑ j ∈ I, ∫ y, c j * (K j (x - y) * u y)) = _
  rw [← integral_finset_sum _ (fun j _ => (v j).const_mul (c j))]
  apply integral_congr_ae
  filter_upwards with y
  simp only [finiteWindowKernel, K, s, Finset.sum_mul, mul_assoc]

private theorem grouped_window_norm_bound (a : SchwartzMap E ℂ) (t : ℝ) (q : E) (I : Finset ℕ) (c : ℕ → ℂ)
    (D : ℝ) (hD : ∀ j, ‖c j‖ ≤ D) (u : SchwartzMap E ℂ) :
    ∀ x, ‖normalizedComplexFourierAction (groupedAnnularSymbol a t q I c) u x‖ ≤
      D * ((I.card * SchwartzMap.seminorm ℝ 0 0 a) * ∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) := by
  intro x
  let U := SchwartzMap.fourierTransformCLM ℂ u
  have iU : Integrable (U : E → ℂ) (volume : Measure E) := U.integrable
  rw [normalized_complex_fourier_action_integral]
  have e := norm_integral_le_of_norm_le
    (iU.norm.const_mul (D * (I.card * SchwartzMap.seminorm ℝ 0 0 a)))
    (f := fun ξ => patchFourierPhase ξ x * (groupedAnnularSymbol a t q I c ξ * U ξ)) (by
      filter_upwards with ξ
      simp only [norm_mul, patch_fourier_phase_norm, one_mul]
      exact mul_le_mul_of_nonneg_right (group_symbol_bound a t q I c D hD ξ) (norm_nonneg _))
  rw [integral_const_mul] at e
  exact e.trans_eq (by change _ = D * ((I.card * SchwartzMap.seminorm ℝ 0 0 a) * ∫ ξ, ‖U ξ‖); ring)

/-- The signed window theorem controls the same finite frequency action
for coefficients bounded by any nonnegative real budget. -/
theorem exists_grouped_annular_action_L3_bound (a : SchwartzMap E ℂ) (ac : HasCompactSupport (a : E → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ (t : ℝ), 0 < t → ∀ (q : E) (I : Finset ℕ) (c : ℕ → ℂ) (D : ℝ), 0 ≤ D →
        (∀ j, ‖c j‖ ≤ D) → ∀ u : SchwartzMap E ℂ,
        let G := normalizedComplexFourierAction (groupedAnnularSymbol a t q I c) u
        MemLp G (ENNReal.ofReal 3) volume ∧ eLpNorm G (ENNReal.ofReal 3) volume ≤
          (K * ENNReal.ofReal (D * (1 + ‖q‖))) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨K, Kfin, bound⟩ := signed_window_all_Lp a ac cut 3 (by norm_num)
  refine ⟨K, Kfin, ?_⟩
  intro t ht q I c D D0 hD u G
  let p := ENNReal.ofReal 3
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  have asm : AEStronglyMeasurable G volume :=
    (normalized_complex_fourier_action_continuous _ (group_symbol_continuous a t q I c).measurable _
      (group_symbol_bound a t q I c D hD) u).aestronglyMeasurable
  have est : eLpNorm G p volume ≤ (K * ENNReal.ofReal (D * (1 + ‖q‖))) *
      eLpNorm (u : E → ℂ) p volume := by
    by_cases zero : D = 0
    · have eq (j : ℕ) : c j = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [zero] using hD j) (norm_nonneg _))
      have ga : G = 0 := by
        funext x
        simp only [G, normalized_complex_fourier_action_integral, groupedAnnularSymbol, eq, zero_mul,
          Finset.sum_const_zero, mul_zero, integral_zero, Pi.zero_apply]
      simp only [ga, eLpNorm_zero, zero_le]
    · let d (j : ℕ) := (D : ℂ)⁻¹ * c j
      have dn (j : ℕ) : ‖d j‖ ≤ 1 := by
        change ‖((D : ℂ)⁻¹ * c j)‖ ≤ 1
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg D0, ← div_eq_inv_mul]
        exact (div_le_one (lt_of_le_of_ne D0 (Ne.symm zero))).mpr (hD j)
      have same (j : ℕ) : (D : ℂ) * d j = c j := by
        dsimp only [d]
        rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast zero), one_mul]
      have eq : G = (D : ℂ) • normalizedComplexFourierAction (groupedAnnularSymbol a t q I d) u := by
        funext x
        change normalizedComplexFourierAction (groupedAnnularSymbol a t q I c) u x =
          (D : ℂ) * normalizedComplexFourierAction (groupedAnnularSymbol a t q I d) u x
        simp only [normalized_complex_fourier_action_integral, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        rw [show groupedAnnularSymbol a t q I c ξ = (D : ℂ) * groupedAnnularSymbol a t q I d ξ by
          simp only [groupedAnnularSymbol, Finset.mul_sum, ← mul_assoc, same]]
        ring
      have eq' : normalizedComplexFourierAction (groupedAnnularSymbol a t q I d) u =
          kernelApply (finiteWindowKernel φ t q I d) u := funext fun x => group_fourier_action_eq_kernel a u t ht q x I d
      rw [eq, eq', eLpNorm_const_smul]
      refine (mul_le_mul_left' (bound t ht q I d dn (u : E → ℂ) (u.memLp p volume)) _).trans_eq ?_
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg D0, ENNReal.ofReal_mul D0]
      ac_rfl
  exact ⟨⟨asm, est.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top Kfin ENNReal.ofReal_lt_top)
    (u.memLp p volume).eLpNorm_lt_top)⟩, est⟩

/-- Group by the fixed spatial Fourier phase before applying the signed
annular bound. The finite number of scales enters the integrable
pointwise majorant, while the L³ constant is independent of that number. -/
theorem exists_grouped_annular_family_L3_bound (a : SchwartzMap E ℂ) (ac : HasCompactSupport (a : E → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ {ι : Type} [Countable ι]
      (t : ℝ), 0 < t → ∀ (I : Finset ℕ) (q : ι → E) (c : ι → ℕ → ℂ) (D : ι → ℝ),
      (∀ k, 0 ≤ D k) → (∀ k j, ‖c k j‖ ≤ D k) →
      let W (k : ι) := D k * (1 + ‖q k‖)
      Summable W →
      ∀ (m : E → ℂ), Measurable m → ∀ B : ℝ, (∀ ξ, ‖m ξ‖ ≤ B) →
        (∀ ξ, HasSum (fun k => groupedAnnularSymbol a t (q k) I (c k) ξ) (m ξ)) →
        ∀ u : SchwartzMap E ℂ,
        let Q := normalizedComplexFourierAction m u
        MemLp Q (ENNReal.ofReal 3) volume ∧ eLpNorm Q (ENNReal.ofReal 3) volume ≤
          (K * ENNReal.ofReal (∑' k, W k)) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨K,Kfin,groupBound⟩ := exists_grouped_annular_action_L3_bound a ac cut
  refine ⟨K,Kfin,?_⟩
  intro ι count t ht I q c D D0 cdom W weight m hm B mB hsum u Q
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let p := ENNReal.ofReal 3
  let N := eLpNorm (u : E → ℂ) p volume
  let S (k : ι) := groupedAnnularSymbol a t (q k) I (c k)
  let G (k : ι) := normalizedComplexFourierAction (S k) u
  let C : ℝ := I.card * SchwartzMap.seminorm ℝ 0 0 a
  let M := C * ∫ ξ, ‖U ξ‖
  have C0 : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  have M0 : 0 ≤ M := mul_nonneg C0 (integral_nonneg (fun _ => norm_nonneg _))
  have w0 (k : ι) : 0 ≤ W k := mul_nonneg (D0 k) (by positivity)
  have dw (k : ι) : D k ≤ W k := le_mul_of_one_le_right (D0 k)
    (le_add_of_nonneg_right (norm_nonneg _))
  have point (k : ι) (x : E) : ‖G k x‖ ≤ W k * M :=
    (grouped_window_norm_bound a t (q k) I (c k) (D k) (cdom k) u x).trans
      (mul_le_mul_of_nonneg_right (dw k) M0)
  have actual (x : E) : Q x = ∑' k, G k x := by
    let F (k : ι) (ξ : E) := patchFourierPhase ξ x * (S k ξ * U ξ)
    have iU : Integrable (U : E → ℂ) (volume : Measure E) := U.integrable
    have Bnd (k : ι) (ξ : E) : ‖F k ξ‖ ≤ (D k * C) * ‖U ξ‖ := by
      simp only [F, norm_mul, patch_fourier_phase_norm, one_mul]
      exact mul_le_mul_of_nonneg_right (group_symbol_bound a t (q k) I (c k) (D k) (cdom k) ξ) (norm_nonneg _)
    have ints (k : ι) : Integrable (F k) := by
      let args : E → E × E := fun ξ => (ξ, x)
      have argsC : Continuous args := continuous_id.prodMk continuous_const
      have phaseC : Continuous (fun ξ : E => patchFourierPhase ξ x) := by
        change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ args)
        exact patch_fourier_phase_continuous.comp argsC
      have hS : Continuous (S k) := group_symbol_continuous _ _ _ _ _
      have hF : Continuous (F k) := phaseC.mul (hS.mul U.continuous)
      exact (iU.norm.const_mul (D k * C)).mono' hF.aestronglyMeasurable (Eventually.of_forall (Bnd k))
    have norms (k : ι) : (∫ ξ, ‖F k ξ‖) ≤ W k * M := by
      have h := integral_mono (ints k).norm (iU.norm.const_mul (D k * C)) (Bnd k)
      rw [integral_const_mul, mul_assoc] at h
      exact h.trans (mul_le_mul_of_nonneg_right (dw k) M0)
    have ns : Summable (fun k => ∫ ξ, ‖F k ξ‖) := Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun ξ => norm_nonneg (F k ξ))) norms (weight.mul_right M)
    have rep (k : ι) : G k x = ∫ ξ, F k ξ := normalized_complex_fourier_action_integral _ _ _
    change normalizedComplexFourierAction m u x = _
    rw [normalized_complex_fourier_action_integral]
    simp_rw [rep]
    rw [integral_tsum_of_summable_integral_norm ints ns]
    apply integral_congr_ae
    filter_upwards with ξ
    have sum : HasSum (fun k => F k ξ) (patchFourierPhase ξ x * (m ξ * U ξ)) :=
      (((hsum ξ).mul_right (U ξ)).mul_left (patchFourierPhase ξ x))
    exact sum.tsum_eq.symm
  have cont : Continuous Q := normalized_complex_fourier_action_continuous m hm B mB u
  have est (k : ι) :
      MemLp (G k) p volume ∧ eLpNorm (G k) p volume ≤ ENNReal.ofReal (W k) * (K * N) := by
    have h := groupBound t ht (q k) I (c k) (D k) (D0 k) (cdom k) u
    exact ⟨h.1, h.2.trans_eq (by
      change (K * ENNReal.ofReal (W k)) * N = ENNReal.ofReal (W k) * (K * N)
      ac_rfl)⟩
  have fin : K * N < ⊤ := ENNReal.mul_lt_top Kfin (u.memLp p volume).eLpNorm_lt_top
  have out := patch_summed_L3_bound G Q cont actual W weight w0 M point (K * N) fin est
  exact ⟨out.1, out.2.trans_eq (by
    change ENNReal.ofReal (∑' k, W k) * (K * N) = (K * ENNReal.ofReal (∑' k, W k)) * N
    ac_rfl)⟩

end Burnett.A03
