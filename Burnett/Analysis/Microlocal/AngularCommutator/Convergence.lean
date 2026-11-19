import Burnett.Analysis.Microlocal.AngularCommutator.FourierRepresentation
import Burnett.Analysis.LocalHminusFourier

/-!
# Strong convergence of the angular commutator

High input frequencies are controlled by the Schur bound. Vanishing
low-frequency energy gives strong convergence to zero, in particular
for the localized distributionally null sequence.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Burnett.Fourier
open scoped ENNReal FourierTransform ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem complexL2_energy_eq_enorm_sq (u : ComplexL2 V) :
    (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ)) = ‖u‖ₑ ^ (2 : ℕ) := by
  rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by norm_num) (by simp)]
  simpa only [ENNReal.rpow_two, ENNReal.toReal_ofNat] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := (volume : Measure V))
      (f := (u : V → ℂ)) (show (0 : ℝ) < 2 by norm_num))

/-- High input frequencies are small for the actual L² cutoff commutator.
The output and input energies are measured in the same Fourier isometry. -/
theorem cutoffCommutator_high_energy_le
    (m χ : BoundedSymbol V) (hsm : ContDiffOn ℝ ∞ (m : V → ℂ) ({0}ᶜ : Set V))
    (hh : DegreeZero (m : V → ℂ))
    (hsχ : ContDiff ℝ ∞ (χ : V → ℂ)) (hcχ : HasCompactSupport (χ : V → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ R : ℝ, 0 < R → ∀ F : V → ℂ, Measurable F →
        ∀ (_hF1 : Integrable F (volume : Measure V)) (hF2 : MemLp F 2 (volume : Measure V)),
        (∀ x, ‖x‖ < R → F x = 0) →
        ‖fourierL2Equiv (cutoffCommutator m χ (fourierL2Equiv.symm (hF2.toLp F)))‖ₑ ^ (2 : ℕ) ≤
          (ENNReal.ofReal (C / R) * A)^2 * ‖hF2.toLp F‖ₑ ^ (2 : ℕ) := by
  obtain ⟨C, hC, A, hA, _, hsq⟩ :=
    highCommutatorKernel_squared_integral_le m χ hsm hh m.bound m.norm_le hsχ hcχ
  refine ⟨C, hC, A, hA, ?_⟩
  intro R hR F hFm hF1 hF2 hz
  have hhyp := hsq R hR F hFm
  have hbase := fourierL2_cutoffCommutator_eq_kernel_ae m χ hsχ hcχ
    (measurable_of_angular_smooth m hsm) F hF1 hF2
  let u := fourierL2Equiv (cutoffCommutator m χ (fourierL2Equiv.symm (hF2.toLp F)))
  have hpoint (x : V) : (∫ y, ((m x - m y) * (𝓕 (χ : V → ℂ)) (x - y)) * F y) =
      ∫ y, highCommutatorKernel m χ R x y * F y := by
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : R ≤ ‖y‖
    · simp [highCommutatorKernel, hy]
    · simp [hz y (lt_of_not_ge hy)]
  have hu : (u : V → ℂ) =ᵐ[volume] (fun x => ∫ y, highCommutatorKernel m χ R x y * F y) := by
    filter_upwards [hbase] with x hx
    exact hx.trans (hpoint x)
  have hin := lintegral_congr_ae (hF2.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖ₑ ^ (2 : ℕ)))
  have hout := lintegral_congr_ae (hu.fun_comp (fun z : ℂ => ‖z‖ₑ ^ (2 : ℕ)))
  simp only [Function.comp_apply] at hin hout
  change ‖u‖ₑ ^ (2 : ℕ) ≤ _
  rw [← complexL2_energy_eq_enorm_sq u, hout,
    ← complexL2_energy_eq_enorm_sq (hF2.toLp F), hin]
  exact hhyp

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Burnett.Fourier
open scoped ENNReal FourierTransform ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem cutoffCommutator_high_norm_le
    (m χ : BoundedSymbol V) (hsm : ContDiffOn ℝ ∞ (m : V → ℂ) ({0}ᶜ : Set V))
    (hh : DegreeZero (m : V → ℂ))
    (hsχ : ContDiff ℝ ∞ (χ : V → ℂ)) (hcχ : HasCompactSupport (χ : V → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∀ F : V → ℂ, Measurable F →
        ∀ (_hF1 : Integrable F (volume : Measure V)) (hF2 : MemLp F 2 (volume : Measure V)),
        (∀ x, ‖x‖ < R → F x = 0) →
        ‖cutoffCommutator m χ (fourierL2Equiv.symm (hF2.toLp F))‖ ≤
          (C / R) * ‖hF2.toLp F‖ := by
  obtain ⟨C, hC, A, hA, h⟩ := cutoffCommutator_high_energy_le m χ hsm hh hsχ hcχ
  refine ⟨C * A.toReal, mul_nonneg hC ENNReal.toReal_nonneg, ?_⟩
  intro R hR F hFm hF1 hF2 hz
  have hE := h R hR F hFm hF1 hF2 hz
  have hA' : A ≠ ⊤ := hA.ne
  have hfin : (ENNReal.ofReal (C / R) * A)^2 * ‖hF2.toLp F‖ₑ ^ (2 : ℕ) ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hfin hE
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm,
    ENNReal.toReal_ofReal (div_nonneg hC hR.le), LinearIsometryEquiv.norm_map] at hreal
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [show ((C * A.toReal / R) * ‖hF2.toLp F‖)^2 =
    ((C / R) * A.toReal)^2 * ‖hF2.toLp F‖ ^ (2 : ℕ) by ring]
  exact hreal

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Filter Burnett.Fourier
open scoped ENNReal FourierTransform ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem cutoffCommutator_norm_le (m χ : BoundedSymbol V) (u : ComplexL2 V) :
    ‖cutoffCommutator m χ u‖ ≤ (2 * m.bound * χ.bound) * ‖u‖ := by
  change ‖fourierMultiplier m (symbolL2 χ u) - symbolL2 χ (fourierMultiplier m u)‖ ≤ _
  apply (norm_sub_le _ _).trans
  have h1 := (fourierMultiplier_norm_le m (symbolL2 χ u)).trans
    (mul_le_mul_of_nonneg_left (symbolL2_norm_le χ u) m.bound_nonneg)
  have h2 := (symbolL2_norm_le χ (fourierMultiplier m u)).trans
    (mul_le_mul_of_nonneg_left (fourierMultiplier_norm_le m u) χ.bound_nonneg)
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- The actual fixed Fourier-cutoff commutator tends strongly to zero when
the input energies are bounded and every fixed spectral ball has vanishing
energy. The spectral condition is proved for localized weak-zero inputs
by the project's low-frequency Fourier lemma. -/
theorem cutoffCommutator_tendsto_zero_of_low_energy
    (m χ : BoundedSymbol V) (hsm : ContDiffOn ℝ ∞ (m : V → ℂ) ({0}ᶜ : Set V))
    (hh : DegreeZero (m : V → ℂ))
    (hsχ : ContDiff ℝ ∞ (χ : V → ℂ)) (hcχ : HasCompactSupport (χ : V → ℂ))
    (F : ℕ → V → ℂ) (hFm : ∀ n, Measurable (F n))
    (hF1 : ∀ n, Integrable (F n) (volume : Measure V))
    (hF2 : ∀ n, MemLp (F n) 2 (volume : Measure V))
    (B : ℝ) (hB : 0 ≤ B) (hBd : ∀ n, ‖(hF2 n).toLp (F n)‖ ≤ B)
    (hlo : ∀ R : ℝ, 0 < R →
      Tendsto (fun n => ∫ x in Metric.closedBall (0 : V) R, ‖F n x‖^2)
        atTop (𝓝 0)) :
    Tendsto (fun n => cutoffCommutator m χ (fourierL2Equiv.symm ((hF2 n).toLp (F n))))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hhigh⟩ := cutoffCommutator_high_norm_le m χ hsm hh hsχ hcχ
  let L := 2 * m.bound * χ.bound
  have hL : 0 ≤ L := by
    exact mul_nonneg (mul_nonneg (by norm_num) m.bound_nonneg) χ.bound_nonneg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let R := 1 + 2 * (C * B) / ε
  have hR : 0 < R := by
    have h := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hC hB)) hε.le
    dsimp only [R]
    linarith
  have hRproduct : C / R * B < ε / 2 := by
    have h := (div_lt_iff₀ hR).mpr (show C * B < (ε / 2) * R by
      have he : ε / 2 * R = C * B + ε / 2 := by
        dsimp only [R]
        field_simp
        ring
      rw [he]
      linarith)
    simpa only [div_mul_eq_mul_div] using h
  let δ := ε / (2 * (L + 1))
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδL : L * δ < ε / 2 := by
    have h := (div_lt_iff₀ (show 0 < 2 * (L + 1) by linarith)).mpr
      (show L * ε < (ε / 2) * (2 * (L + 1)) by nlinarith)
    simpa only [δ, mul_div_assoc] using h
  let S := Metric.closedBall (0 : V) R
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  let Flo (n : ℕ) : V → ℂ := S.indicator (F n)
  let Fhi (n : ℕ) : V → ℂ := Sᶜ.indicator (F n)
  let hlo₂ (n : ℕ) : MemLp (Flo n) 2 volume := (hF2 n).indicator hS
  let hhi₂ (n : ℕ) : MemLp (Fhi n) 2 volume := (hF2 n).indicator hS.compl
  let low (n : ℕ) := (hlo₂ n).toLp (Flo n)
  let high (n : ℕ) := (hhi₂ n).toLp (Fhi n)
  have hsum (n : ℕ) : low n + high n = (hF2 n).toLp (F n) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (low n) (high n), (hlo₂ n).coeFn_toLp,
      (hhi₂ n).coeFn_toLp, (hF2 n).coeFn_toLp] with x ha hl hhx hf
    rw [ha, Pi.add_apply, hl, hhx, hf]
    by_cases hx : x ∈ S <;> simp [Flo, Fhi, hx]
  have hlonorm (n : ℕ) : ‖low n‖^2 = ∫ x in S, ‖F n x‖^2 := by
    rw [l2_norm_sq_integral]
    have heq : (∫ x, ‖low n x‖^2) = ∫ x, S.indicator (fun y => ‖F n y‖^2) x := by
      apply integral_congr_ae
      filter_upwards [(hlo₂ n).coeFn_toLp] with x hx
      rw [hx]
      by_cases h : x ∈ S <;> simp [Flo, h]
    rw [heq, integral_indicator hS]
  have hhinorm (n : ℕ) : ‖high n‖ ≤ B := by
    have hc := norm_toLp_le_of_norm_le (hhi₂ n) (hF2 n) (C := 1) (by norm_num)
      (fun x => by by_cases hx : x ∈ S <;> simp [Fhi, hx])
    exact (by simpa only [one_mul] using hc : ‖high n‖ ≤ ‖(hF2 n).toLp (F n)‖).trans (hBd n)
  have hhighnorm (n : ℕ) :
      ‖cutoffCommutator m χ (fourierL2Equiv.symm (high n))‖ ≤ (C / R) * B := by
    have hi := hhigh R hR (Fhi n) ((hFm n).indicator hS.compl)
      ((hF1 n).indicator hS.compl) (hhi₂ n)
      (fun x hx => by
        have hx' : x ∈ S := by
          change x ∈ Metric.closedBall (0 : V) R
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hx.le
        simp [Fhi, hx'])
    exact hi.trans (mul_le_mul_of_nonneg_left (hhinorm n) (div_nonneg hC hR.le))
  have ht := (Metric.tendsto_nhds.mp (hlo R hR)) (δ^2) (by positivity)
  filter_upwards [ht] with n hn
  have hnsmall : ‖low n‖^2 < δ^2 := by
    rw [hlonorm]
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hn)
  have hln : ‖low n‖ ≤ δ := (sq_le_sq₀ (norm_nonneg _) hδ.le).mp hnsmall.le
  have hlow : ‖cutoffCommutator m χ (fourierL2Equiv.symm (low n))‖ < ε / 2 := by
    have hi := cutoffCommutator_norm_le m χ (fourierL2Equiv.symm (low n))
    rw [LinearIsometryEquiv.norm_map] at hi
    exact hi.trans_lt ((mul_le_mul_of_nonneg_left hln hL).trans_lt hδL)
  rw [dist_zero_right, ← hsum n, map_add, map_add]
  exact (norm_add_le _ _).trans_lt (by linarith [hhighnorm n, hRproduct])

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Set Filter Burnett.Fourier Burnett.Analysis.LocalHminusFourier
open Burnett.X02.SobolevTestJet Burnett.X02.TestJetPairing
open scoped ENNReal FourierTransform ContDiff Topology

/-- Fixed angular multiplier and cutoff on the actual localized smooth,
bounded, distributionally null sequence. -/
theorem cutoffCommutator_tendsto_zero_of_localized_weak_zero
    (m χ : BoundedSymbol Space)
    (hsm : ContDiffOn ℝ ∞ (m : Space → ℂ) ({0}ᶜ : Set Space))
    (hh : DegreeZero (m : Space → ℂ))
    (hsχ : ContDiff ℝ ∞ (χ : Space → ℂ)) (hcχ : HasCompactSupport (χ : Space → ℂ))
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ n x, f n x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => cutoffCommutator m χ ((sourceSchwartz (hs n) χ0 (hχ0 n)).toLp 2 volume))
      atTop (𝓝 0) := by
  let u (n : ℕ) : SchwartzMap Space ℂ := sourceSchwartz (hs n) χ0 (hχ0 n)
  let g (n : ℕ) : SchwartzMap Space ℂ := SchwartzMap.fourierTransformCLM ℂ (u n)
  let h2 (n : ℕ) : MemLp (g n : Space → ℂ) 2 volume := (g n).memLp 2 volume
  have hg (n : ℕ) : (g n : Space → ℂ) = 𝓕 (fun x => (f n x : ℂ)) := rfl
  have hL2 (n : ℕ) : (g n).toLp 2 volume = fourierL2Equiv ((u n).toLp 2 volume) :=
    (fourierL2Equiv_schwartz (u n)).symm
  have hnorm (n : ℕ) : ‖(h2 n).toLp (g n : Space → ℂ)‖ = ‖(hf n).toLp (f n)‖ := by
    change ‖(g n).toLp 2 volume‖ = _
    rw [hL2, LinearIsometryEquiv.norm_map]
    simp only [SchwartzMap.toLp, Lp.norm_toLp]
    congr 1
    exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (fun x => Complex.norm_real (f n x)))
  have hlow (R : ℝ) (_hR : 0 < R) :
      Tendsto (fun n => ∫ x in Metric.closedBall (0 : Space) R, ‖g n x‖^2)
        atTop (𝓝 0) := by
    simp_rw [hg]
    exact low_frequency_energy_tendsto_zero hs hf χ0 hχ0 hB ht R
  have h := cutoffCommutator_tendsto_zero_of_low_energy m χ hsm hh hsχ hcχ
    (fun n => (g n : Space → ℂ)) (fun n => (g n).continuous.measurable)
    (fun n => (g n).integrable) h2 B ((norm_nonneg _).trans (hB 0))
    (fun n => (hnorm n).trans_le (hB n)) hlow
  apply h.congr
  intro n
  change cutoffCommutator m χ (fourierL2Equiv.symm ((g n).toLp 2 volume)) =
    cutoffCommutator m χ ((u n).toLp 2 volume)
  rw [hL2, fourierL2Equiv.symm_apply_apply]

end Burnett.Microlocal.AngularCommutator
