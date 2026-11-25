import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeRadianPair

set_option autoImplicit false
set_option maxHeartbeats 2900000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V08

open Set Metric Matrix MeasureTheory Burnett.P01
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight lowSlotWeight_nonzero_small)
open scoped ContDiff Matrix BigOperators

/-- Evaluate the frozen angular symbol on any constant elementary tensor before
multiplying it by its true, nonconstant low Fourier entry. -/
theorem gaugeBasisCoefficient_normalized
    (G : ComplexComponents) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ (s : ℝ), 0 < s → ∀ ξ, a (s • ξ) = s * a ξ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (hS : ∀ (s : ℝ), 0 < s → ∀ ξ, S (s • ξ) = S ξ)
    (lowDir ratio highDir : E) (pSize qSize : ℝ) (hp : 0 < pSize) (hq : 0 < qSize)
    (hLow : ‖lowDir‖ = 1) (hHigh : ‖highDir‖ = 1) (hRatio : ‖ratio‖ < 1/2)
    (hScale : ratio = (pSize / qSize) • lowDir) (i j : TensorSlot) :
    let p := pSize • lowDir
    let q := qSize • highDir
    lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential G) C S p q i j =
      (qSize : ℂ) * ((w / 3 * cyclicLowNormalizedPhase a lowDir ratio highDir : ℝ) : ℂ) *
        lowGaugeNormalizedHighDifference m G lowDir ratio highDir *
        (lowGaugeHighMatrix C S ratio highDir i j : ℂ) := by
  dsimp only
  let p := pSize • lowDir
  let q := qSize • highDir
  have hLen : ‖p‖ = pSize := by
    change ‖pSize • lowDir‖ = pSize
    rw [norm_smul, Real.norm_of_nonneg hp.le, hLow, mul_one]
  have hUnit : pSize⁻¹ • p = lowDir := by
    change pSize⁻¹ • (pSize • lowDir) = _
    rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  have hAngle :
      signedCyclicPhase a p q = pSize * cyclicLowNormalizedPhase a lowDir ratio highDir := by
    have h := (div_eq_iff hp.ne').mp
      (signedCyclicPhase_div_eq_lowNormalized a ha hOdd hHom lowDir ratio highDir
        pSize qSize hp hq hHigh hRatio hScale)
    exact h.trans (mul_comm _ _)
  have hScaleProduct : qSize * (pSize / qSize) = pSize := by field_simp
  have hSum : p + q = qSize • (ratio + highDir) := by
    change pSize • lowDir + qSize • highDir = _
    rw [hScale, smul_add, smul_smul, hScaleProduct]
  have hOut : lowGaugeHighMatrix C S p q = lowGaugeHighMatrix C S ratio highDir := by
    simp only [lowGaugeHighMatrix, hSum, q, hS qSize hq]
  have hDiff : q + (p + q) = qSize • (highDir + (ratio + highDir)) := by
    rw [hSum]
    exact (smul_add qSize highDir (ratio + highDir)).symm
  have hContract :
      lowGaugeHighDifference m (gaugeEntryPotential G p) p q =
        ((qSize / pSize : ℝ) : ℂ) *
          lowGaugeNormalizedHighDifference m G lowDir ratio highDir := by
    unfold lowGaugeNormalizedHighDifference lowGaugeHighDifference
    rw [hDiff]
    simp only [gaugeEntryPotential, hLen, hUnit, PiLp.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold lowGaugeCorrectionCoefficient
  rw [hAngle, hContract, hOut]
  have hpc : (pSize : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

theorem gaugeRawEntry_measurable (θ hi ho : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : GaugeScreen) (hθ : Measurable θ) (hhi : Measurable hi) (hho : Measurable ho)
    (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0})
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun q => S q i j) {x : E | x ≠ 0}) (k i j : TensorSlot) :
    Measurable (gaugeRawEntry θ hi ho κ m w a C S k i j) := by
  have ha' : Measurable a := measurable_of_continuousOn_compl_singleton 0 ha.continuousOn
  have hs' (i j : TensorSlot) : Measurable (fun p => S p i j) :=
    measurable_of_continuousOn_compl_singleton 0 (hS i j).continuousOn
  change Measurable (fun x : Joint => (gaugeTriadCutoff θ hi ho κ x.1 x.2 : ℂ) *
    lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential (gaugeEntryBasis k)) C S x.1 x.2 i j)
  simp only [gaugeTriadCutoff, lowSlotWeight, lowGaugeCorrectionCoefficient,
    signedCyclicPhase, lowGaugeHighMatrix, Matrix.mul_apply, Matrix.transpose_apply, lowGaugeHighDifference,
    gaugeEntryPotential, normalizedGaugePotential_apply]
  fun_prop (disch := assumption)

theorem exists_gaugeRawEntry_orderOne (θ hi ho : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16)
    (hCut : ∀ t : ℝ, 1 ≤ t → θ t = 0) (hHiZero : hi 0 = 0)
    (hθ : ∀ t, |θ t| ≤ 1) (hhi : ∀ t, |hi t| ≤ 1) (hho : ∀ t, |ho t| ≤ 1)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ)
    (S : GaugeScreen) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (hOdd : ∀ x, a (-x) = -a x)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (hSD : ∀ i j, ContDiffOn ℝ ∞ (fun x => S x i j) {x : E | x ≠ 0})
    (hS : ∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x) (i j : TensorSlot) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k (x : Joint), ‖gaugeRawEntry θ hi ho κ m w a C S k i j x‖ ≤ B*(1+‖x.1‖+‖x.2‖) := by
  classical
  let F (k : TensorSlot) := lowGaugeAngularExpansionProfile m w a (gaugeEntryBasis k) C S i j
  have hJets (k : TensorSlot) : ∃ A : ℝ, 0 ≤ A ∧ ∀ ratio high low : E,
      ‖ratio‖ ≤ 1/4 → ‖high‖=1 → ‖low‖=1 → ‖F k ((ratio, high), low)‖ ≤ A := by
    obtain ⟨_,M,_,_,_,hM,hJet⟩ := exists_lowGaugeAngularExpansionProfile_jet_bound m w a ha (gaugeEntryBasis k)
      C S hSD i j (1/4) (by norm_num) 0
    refine ⟨M,hM,?_⟩
    intro ratio high low hr hh hl
    have h := hJet 0 le_rfl ((ratio,high),low)
      ⟨⟨mem_closedBall_zero_iff.mpr hr, by simpa only [mem_sphere,dist_zero_right] using hh⟩,
        by simpa only [mem_sphere,dist_zero_right] using hl⟩
    simpa only [norm_iteratedFDeriv_zero] using h
  choose A hA bound using hJets
  let B := ∑ k, A k
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => hA k)
  refine ⟨B,hB,?_⟩
  intro k x
  obtain ⟨p,q⟩ := x
  have rhs : 0 ≤ B*(1+‖p‖+‖q‖) := by positivity
  by_cases hp : p = 0
  · subst p
    simpa [gaugeRawEntry, lowGaugeCorrectionCoefficient, lowGaugeHighDifference, gaugeEntryPotential] using rhs
  by_cases hq : q = 0
  · subst q
    simpa [gaugeRawEntry, gaugeTriadCutoff, hHiZero] using rhs
  by_cases hLow : lowSlotWeight θ κ p q (-(p+q)) = 0
  · simpa only [gaugeRawEntry,gaugeTriadCutoff,hLow,zero_mul,Complex.ofReal_zero,norm_zero] using rhs
  have hp' := norm_pos_iff.mpr hp
  have hq' := norm_pos_iff.mpr hq
  let lo := ‖p‖⁻¹ • p
  let head := ‖q‖⁻¹ • q
  let ratio := (‖p‖/‖q‖) • lo
  have hlo : ‖lo‖=1 := by simp [lo, norm_smul, hp'.ne']
  have hhead : ‖head‖=1 := by simp [head,norm_smul, hq'.ne']
  have hpback : ‖p‖ • lo = p := by simp [lo, smul_smul, hp'.ne']
  have hqback : ‖q‖ • head = q := by simp [head, smul_smul, hq'.ne']
  have hLowSize := lowSlotWeight_nonzero_small hCut hκ hSmall (add_neg_cancel (p+q)) hq hLow
  have hRat : ‖ratio‖ ≤ 1/4 := by
    rw [show ‖ratio‖ = ‖p‖/‖q‖ by simp [ratio,norm_smul,Real.norm_of_nonneg (div_nonneg hp'.le hq'.le),hlo]]
    apply (div_le_iff₀ hq').2
    nlinarith [mul_lt_mul_of_pos_right hSmall hq']
  have hFactor := gaugeBasisCoefficient_normalized (gaugeEntryBasis k) m w a ha hOdd hHom C S hS
    lo ratio head ‖p‖ ‖q‖ hp' hq' hlo hhead (hRat.trans_lt (by norm_num)) rfl i j
  dsimp only at hFactor
  rw [hpback,hqback] at hFactor
  have hCore : lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential (gaugeEntryBasis k)) C S p q i j =
      (‖q‖ : ℂ) * F k ((ratio,head),lo) := by simpa only [F,lowGaugeAngularExpansionProfile,lowGaugeJointProfile,mul_assoc] using hFactor
  have hMask : |gaugeTriadCutoff θ hi ho κ p q| ≤ 1 := by
    simp only [gaugeTriadCutoff,lowSlotWeight,abs_mul]
    exact (mul_le_mul (mul_le_mul (hθ _) (hhi _) (abs_nonneg _) zero_le_one) (hho _)
      (abs_nonneg _) (by positivity)).trans_eq (by norm_num)
  have hk : A k ≤ B := Finset.single_le_sum (fun l _ => hA l) (Finset.mem_univ k)
  change ‖(gaugeTriadCutoff θ hi ho κ p q : ℂ) * _‖ ≤ B*(1+‖p‖+‖q‖)
  rw [hCore,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_of_nonneg (norm_nonneg q)]
  calc
    _ ≤ 1 * (‖q‖ * B) := by gcongr; exact (bound k ratio head lo hRat hhead hlo).trans hk
    _ ≤ B*(1+‖p‖+‖q‖) := by nlinarith [mul_nonneg hB (norm_nonneg p)]

end Burnett.V08
