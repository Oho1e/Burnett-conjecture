import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotPaperExponents
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapSum
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapWindows

set_option autoImplicit false
set_option maxHeartbeats 5100000
noncomputable section
namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff FourierTransform BigOperators

private abbrev pairMeasure : Measure (Joint × E) :=
  (volume : Measure Joint).prod (volume : Measure E)

private def testedDensity (A : Joint → ℂ) (s : ℝ)
    (f g h : SchwartzMap E ℂ) (yx : Joint × E) : ℂ :=
  blockKernel A yx.1 * (f (yx.2-s • yx.1.1) * g (yx.2-s • yx.1.2) * h yx.2)

private theorem testedDensity_continuous {A : Joint → ℂ} (hK : Continuous (blockKernel A))
    (s : ℝ) (f g h : SchwartzMap E ℂ) : Continuous (testedDensity A s f g h) := by
  unfold testedDensity
  fun_prop

private theorem testedDensity_integrable {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    Integrable (testedDensity A s f g h) pairMeasure := by
  obtain ⟨hKI,hKC⟩ := blockKernel_integrable A ha hA
  have hC := testedDensity_continuous hKC s f g h
  refine ⟨hC.aestronglyMeasurable,?_⟩
  change (∫⁻ yx : Joint × E, ‖testedDensity A s f g h yx‖ₑ ∂pairMeasure) < ⊤
  rw [lintegral_prod _ hC.enorm.aemeasurable]
  letI : ENNReal.HolderTriple 4 4 2 := by
    have h : (4 : ℝ).HolderTriple 4 2 := ⟨by norm_num,by norm_num,by norm_num⟩
    simpa using h.ennrealOfReal
  exact (dilated_kernel_trilinear_bound
    (p := 4) (s := 4) (r := 2) (t := 2) (blockKernel A) hKC.measurable f g h s).trans_lt
      (ENNReal.mul_lt_top hKI.hasFiniteIntegral
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top (f.eLpNorm_lt_top 4 volume) (g.eLpNorm_lt_top 4 volume))
          (h.eLpNorm_lt_top 2 volume)))

private theorem testedBlock_eq_integral {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    testedBlock A s f g h = ∫ yx, testedDensity A s f g h yx ∂pairMeasure := by
  rw [integral_prod_symm _ (testedDensity_integrable ha hA s f g h)]
  unfold testedBlock
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  simp only [testedDensity,mul_assoc]

private theorem translate_second_coordinate (U : Joint × E → ℂ) (hU : Continuous U)
    (hi : Integrable U pairMeasure) (s : ℝ) :
    (∫ yx, U (yx.1,yx.2+s • yx.1.2) ∂pairMeasure) = ∫ yx, U yx ∂pairMeasure := by
  let V (yx : Joint × E) := U (yx.1,yx.2+s • yx.1.2)
  have hc : Continuous V := hU.comp (by fun_prop)
  have hint : Integrable V pairMeasure := by
    refine ⟨hc.aestronglyMeasurable,?_⟩
    change (∫⁻ yx, ‖V yx‖ₑ ∂pairMeasure) < ⊤
    have eq : (∫⁻ yx, ‖V yx‖ₑ ∂pairMeasure) = ∫⁻ yx, ‖U yx‖ₑ ∂pairMeasure := by
      rw [lintegral_prod _ hc.enorm.aemeasurable,lintegral_prod _ hU.enorm.aemeasurable]
      apply lintegral_congr
      intro y
      have hF : Measurable (fun x : E => ‖U (y,x)‖ₑ) := (hU.comp (by fun_prop)).enorm.measurable
      exact (measurePreserving_add_right (volume : Measure E) (s • y.2)).lintegral_comp hF
    exact eq.trans_lt hi.hasFiniteIntegral
  change (∫ yx, V yx ∂pairMeasure) = _
  rw [integral_prod _ hint,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with y
  exact (measurePreserving_add_right (volume : Measure E) (s • y.2)).integral_comp
    (Homeomorph.addRight (s • y.2)).measurableEmbedding (fun x => U (y,x))

private theorem highCoefficientGap_insertion_input {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (a b d : SchwartzMap E ℂ) (u v w r t : ℝ) (C f g h : SchwartzMap E ℂ) (j : ℕ) :
    highCoefficientGapBlock A a b d u v w r t (fun y => -y.2) (fun y => y.1-y.2) C g h f j =
      (dyadicScale t j)⁻¹ • testedBlock A (dyadicScale t j)
        (windowTest d f (w*dyadicScale t j))
        (gapSchwartzProduct C (windowTest a g ((u*r)*dyadicScale t j)))
        (windowTest b h (v*dyadicScale t j)) := by
  let s := dyadicScale t j
  let F := windowTest d f (w*s)
  let G := gapSchwartzProduct C (windowTest a g ((u*r)*s))
  let H := windowTest b h (v*s)
  change highCoefficientGapBlock A a b d u v w r t (fun y => -y.2) (fun y => y.1-y.2) C g h f j =
    s⁻¹ • testedBlock A s F G H
  rw [testedBlock_eq_integral ha hA,← translate_second_coordinate _ (testedDensity_continuous
    (blockKernel_integrable A ha hA).2 s F G H) (testedDensity_integrable ha hA s F G H) s,← integral_smul]
  unfold highCoefficientGapBlock
  apply integral_congr_ae
  filter_upwards with yx
  have hl : yx.2+s • yx.1.2-s • yx.1.1 = yx.2-s • (yx.1.1-yx.1.2) := by rw [smul_sub]; abel
  dsimp only [s] at hl
  simp only [highCoefficientGapDensity,testedDensity,shiftedTest,smul_zero,sub_zero,smul_neg,
    sub_neg_eq_add,F,G,H,s,hl,add_sub_cancel_right,gapSchwartzProduct_apply,Complex.real_smul]
  ring

private theorem highCoefficientGap_insertion_output {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (a b d : SchwartzMap E ℂ) (u v w r t : ℝ) (C f g h : SchwartzMap E ℂ) (j : ℕ) :
    highCoefficientGapBlock A a b d u v w r t Prod.snd Prod.fst C h g f j =
      (dyadicScale t j)⁻¹ • testedBlock A (dyadicScale t j)
        (windowTest d f (w*dyadicScale t j)) (windowTest b g (v*dyadicScale t j))
        (gapSchwartzProduct C (windowTest a h ((u*r)*dyadicScale t j))) := by
  rw [testedBlock_eq_integral ha hA,← integral_smul]
  unfold highCoefficientGapBlock
  apply integral_congr_ae
  filter_upwards with yx
  simp only [highCoefficientGapDensity,testedDensity,shiftedTest,smul_zero,sub_zero,
    gapSchwartzProduct_apply,Complex.real_smul]
  ring

/-- The two actual tested Fourier terms have a common summable frequency-gap
factor. The coefficient support and its amplitude may be supplied independently. -/
theorem exists_highCoefficientGap_tested_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ac bc r₀ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hgap : r₀*(1+ρ)*hi < ac)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (ha' : HasCompactSupport (a : E → ℂ))
    (hb' : HasCompactSupport (b : E → ℂ))
    (he' : HasCompactSupport (e : E → ℂ))
    (hAnnA : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hTop : ∀ z : E, ac-r₀*(1+ρ)*hi ≤ ‖z‖ → ‖z‖ ≤ bc+r₀*(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {r t : ℝ}, 0<r → r≤r₀ → 0<t →
      ∀ (n : ℕ) (L : ℝ≥0) (C : Fin n → SchwartzMap E ℂ),
      (∀ i z, 𝓕 (C i : E → ℂ) z ≠ 0 →
        ac ≤ ‖(r*dyadicScale t i) • z‖ ∧ ‖(r*dyadicScale t i) • z‖ ≤ bc) →
      (∀ i x, ‖C i x‖ ≤ (L : ℝ)*r*dyadicScale t i) →
      ∀ f g h : SchwartzMap E ℂ,
      (∑ i : Fin n, ‖(dyadicScale t i)⁻¹ •
        (testedBlock A (dyadicScale t i) f (gapSchwartzProduct (C i) g) h -
         testedBlock A (dyadicScale t i) f g (gapSchwartzProduct (C i) h))‖ₑ) ≤
        (L : ℝ≥0∞)*ENNReal.ofReal r*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨I,hI,BI⟩ := exists_highCoefficientGapBlock_sum_bound A ha hA a e d ha' he' hAnnA hAnnE
    (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) 4
    (one_lt_highSlotInputExponent inputL2) (one_lt_highSlotTestExponent inputL2) (by norm_num)
    (highSlotInputTestBalance inputL2) hu hw hl
  obtain ⟨O,hO,BO⟩ := exists_highCoefficientGapBlock_sum_bound A ha hA a b d ha' hb' hAnnA hAnnB
    (highSlotTestExponent inputL2) (highSlotInputExponent inputL2) 4
    (one_lt_highSlotTestExponent inputL2) (one_lt_highSlotInputExponent inputL2) (by norm_num)
    (highSlotTestInputBalance inputL2) hu hv hl
  refine ⟨I+O,ENNReal.add_lt_top.mpr ⟨hI,hO⟩,?_⟩
  intro r t hr hrr ht n L C hCF hCA f g h
  let first (i : Fin n) :=
    highCoefficientGapBlock A a e d u w l r t (fun y => -y.2) (fun y => y.1-y.2) (C i) g h f i
  let second (i : Fin n) :=
    highCoefficientGapBlock A a b d u v l r t Prod.snd Prod.fst (C i) h g f i
  have B₁ := BI hr ht (fun y => -y.2) (fun y => y.1-y.2) (by fun_prop) (by fun_prop)
    (fun y => by rw [norm_neg]) (fun y => norm_sub_le y.1 y.2) n L (fun i => C i)
    (fun i => (C i).continuous) hCA g h f
  have B₂ := BO hr ht Prod.snd Prod.fst continuous_snd continuous_fst
    (fun _ => le_rfl) (fun y => le_add_of_nonneg_right (norm_nonneg y.2)) n L (fun i => C i)
    (fun i => (C i).continuous) hCA h g f
  calc
    _ ≤ ∑ i : Fin n, (‖first i‖ₑ+‖second i‖ₑ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      obtain ⟨eqI,eqO⟩ := highCoefficientGap_insert_tested_windows A ha hA hρ hρ' hr hrr hgap
        hBand a b e d u v w l hTop hIn hOut hLow (dyadicScale t i) (C i) f g h (hCF i)
      rw [smul_sub,eqI,eqO,← highCoefficientGap_insertion_input ha hA,
        ← highCoefficientGap_insertion_output ha hA]
      simpa only [sub_eq_add_neg,enorm_neg] using enorm_add_le (first i) (-(second i))
    _ = (∑ i : Fin n, ‖first i‖ₑ) + ∑ i : Fin n, ‖second i‖ₑ := Finset.sum_add_distrib
    _ ≤ (L : ℝ≥0∞)*ENNReal.ofReal r*I*triLpMass g h f (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) 4 +
        (L : ℝ≥0∞)*ENNReal.ofReal r*O*triLpMass h g f (highSlotTestExponent inputL2) (highSlotInputExponent inputL2) 4 := add_le_add B₁ B₂
    _ = _ := by simp only [triLpMass,mul_add,add_mul]; ac_rfl

theorem exists_highCoefficientGap_tested_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ac bc r₀ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hgap : r₀*(1+ρ)*hi < ac)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (ha' : HasCompactSupport (a : E → ℂ))
    (hb' : HasCompactSupport (b : E → ℂ))
    (he' : HasCompactSupport (e : E → ℂ))
    (hAnnA : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hTop : ∀ z : E, ac-r₀*(1+ρ)*hi ≤ ‖z‖ → ‖z‖ ≤ bc+r₀*(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {r t : ℝ}, 0<r → r≤r₀ → 0<t →
      ∀ (n : ℕ) (L : ℝ≥0) (C : Fin n → SchwartzMap E ℂ),
      (∀ i z, 𝓕 (C i : E → ℂ) z ≠ 0 →
        ac ≤ ‖(r*dyadicScale t i) • z‖ ∧ ‖(r*dyadicScale t i) • z‖ ≤ bc) →
      (∀ i x, ‖C i x‖ ≤ (L : ℝ)*r*dyadicScale t i) →
      ∀ f g h : SchwartzMap E ℂ,
      (∑ i : Fin n, ‖(dyadicScale t i)⁻¹ •
        (testedBlock A (dyadicScale t i) f (gapSchwartzProduct (C i) g) h -
         testedBlock A (dyadicScale t i) f g (gapSchwartzProduct (C i) h))‖ₑ) ≤
        (L : ℝ≥0∞)*ENNReal.ofReal r*M*triLpMass f g h 4 4 2 :=
  exists_highCoefficientGap_tested_sum_bound_paper false A ha hA hρ hρ' hgap hBand
    a b e d hu hv hw hl ha' hb' he' hAnnA hAnnB hAnnE hTop hIn hOut hLow

end Burnett.A06
