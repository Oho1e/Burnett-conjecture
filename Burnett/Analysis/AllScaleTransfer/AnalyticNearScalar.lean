import Burnett.Analysis.AllScaleTransfer.ActualNearWithProfiles
import Burnett.Analysis.AllScaleTransfer.RadianFactorwiseTruncation

set_option autoImplicit false
set_option maxRecDepth 9300
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff ENNReal

open private schwartzFieldLp3_norm_le_sum from Burnett.Analysis.AllScaleTransfer.ActualFieldRadialLimit

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The scalar near-angle assertion of the all-scale estimate for an
actual adjacent cap realization. The order-100 budget includes the
zero-ratio trace and the fixed comparable boxes. The same constant
applies to every finite signed factorwise dyadic truncation. -/
theorem exists_adjacentNearTrilinearForm_full_truncated_bound
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube outer enlarged κ b : ℝ) (hB : 0 < B) (hTube : 0 < tube)
    (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b) :
    ∃ (R : ℝ) (N : ℕ) (Cκ : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ Cκ ∧
      ∀ {metric : Form} {δ inner D C₃ : ℝ},
      ∀ (S : SmoothThinConeCaps metric δ (tube*δ^2) inner outer enlarged D)
        (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
          (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ) C₃)
        (chart : ∀ γ : ↑S.centers, NullCapChart metric γ),
      (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) →
      (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) →
      ∀ {q A C : ℝ}, 3 < q → ∀ hδ : δ ∈ Ioc (0 : ℝ) 1,
      4*B*(5*δ) ≤ 1 → 0 < D → 0 ≤ A → 0 ≤ C →
      (∀ v : FieldLp Unit (ENNReal.ofReal 3),
        (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^(1/3 : ℝ) ≤
          C * (S.centers.card : ℝ)^(1/(3*(q-2))) * ‖v‖) →
      ∀ (m : Joint → ℂ) (H : ℝ), Measurable m →
      (∀ p, ‖m p‖ ≤ H) → (∀ (t : ℝ), 0 < t → ∀ p : Joint, m (t • p) = m p) →
      (∀ (p : Joint), m p ≠ 0 → p.1 ≠ 0 → p.2 ≠ 0 → -(p.1+p.2) ≠ 0 →
        |quadratic metric p.1| ≤ inner*(tube*δ^2)*‖p.1‖^2 ∧
        ∀ γ : ↑S.centers, capMultiplier S.centers metric δ (tube*δ^2) inner outer γ p.1 ≠ 0 →
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ p.1 = 1 ∧
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ p.2 = 1 ∧
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ (-(p.1+p.2)) = 1) →
      (∀ γ : ↑S.centers,
        let a := capFrequencyEquiv (chart γ) hδ.1.ne'
        let K := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ)
        let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
        let bases : Fin 3 → Joint → ℂ := ![μ,μ ∘ radianCycle.symm,μ ∘ radianCycle]
        let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (bases i) 0 ∘ pairedFrequencyEquiv a
        let comparable := radianFourBranchSymbol ϑ κ μ 3 ∘ pairedFrequencyEquiv a
        let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
        (∃ (M : Fin 3 → E → E → ℝ → ℂ) (B₀ : ℝ),
          (∀ i, Measurable (fun p : Joint => M i p.1 p.2 0)) ∧
          (∀ i (p : Joint), ‖M i p.1 p.2 0‖ ≤ B₀) ∧
          (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
          (∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
            ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
              (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
          ∀ (i : Fin 3) (p : Joint), a p.1 ∈ K → a p.2 ∈ K → a (-(p.1+p.2)) ∈ K →
            ‖a p.1‖/‖a p.2‖ ∈ Ioo (0 : ℝ) b →
            low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖a p.1‖/‖a p.2‖)) ∧
        (∃ G : ℤ → BoxSpace → ℂ,
          (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) 5)) ∧
          (∀ k ∈ I, ∀ n ≤ 100, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ A) ∧
          ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
            G k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ))) →
      let L := Cκ*C^3*D^(1/(q-2))*A*δ^(2*(q-3)/(q-2))
      (∀ f g h : SchwartzMap E ℂ, ‖radianTrilinearForm m f g h‖ ≤ L*(triLpMass f g h 3 3 3).toReal) ∧
      ∀ (I J L' : Finset ℤ) (a b' c : ℤ → ℂ),
        (∀ j ∈ I, ‖a j‖ ≤ 1) → (∀ j ∈ J, ‖b' j‖ ≤ 1) → (∀ j ∈ L', ‖c j‖ ≤ 1) →
        ∀ f g h : SchwartzMap E ℂ,
          ‖radianTrilinearForm m (finiteIntegerRadialTruncation I a f)
            (finiteIntegerRadialTruncation J b' g) (finiteIntegerRadialTruncation L' c h)‖ ≤
              L*(triLpMass f g h 3 3 3).toReal := by
  let χ := descendingProfile κ (7*κ/4)
  have hχGap : κ < 7*κ/4 := by linarith only [hκ]
  have hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1 := by
    intro t _
    have h := descendingProfile_range κ (7*κ/4) t
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  obtain ⟨R,N,Cκ,hR,hR₁,hCκ,full⟩ := exists_actual_radian_near_field_bound (ι := Unit) (ξ := Unit)
    ϑ hϑ.continuous.measurable hRange hCut hFlat B tube outer enlarged κ κ b
    hB hTube hOut hOE hκ hκsmall hκ hb χ (descendingProfile_contDiff _ _) hχRange
    (fun t _ ht => descendingProfile_eq_one hχGap ht) (fun t ht => descendingProfile_eq_zero hχGap ht)
  obtain ⟨T,hT,trunc⟩ := exists_radianTrilinearForm_factorwise_truncation_bound
  refine ⟨R,N,(1+T)*Cκ,hR,hR₁,by positivity,?_⟩
  intro metric δ inner D C₃ S Pplus chart hfwd hinv q A C hq hδ hSmall hD hA hC angular
    m H hm hMag hHom hSupp hProfiles L
  let K := Cκ*C^3*D^(1/(q-2))*A*δ^(2*(q-3)/(q-2))
  have hδ₀ : 0 ≤ δ := hδ.1.le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hThree : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
  have hScalarNorm (f : SchwartzMap E ℂ) :
      ‖schwartzFieldLp3 (fun _ : Unit => f)‖ ≤ (eLpNorm (f : E → ℂ) 3 volume).toReal := by
    simpa [SchwartzMap.norm_toLp] using schwartzFieldLp3_norm_le_sum (fun _ : Unit => f)
  have estimate (f g h : SchwartzMap E ℂ) :
      ‖radianTrilinearForm m f g h‖ ≤ K*(triLpMass f g h 3 3 3).toReal := by
    let arguments (i : Fin 3) (_ : Unit) : SchwartzMap E ℂ := ![f,g,h] i
    have e := full S Pplus chart hfwd hinv hq hδ hSmall hD hA hC (by simpa using angular)
      (fun _ => m) H (fun _ => hm) (fun _ => hMag) (fun _ => hHom) (fun _ => hSupp) (by
        intro γ _
        obtain ⟨low, G,hSmooth,hBound,hSource⟩ := hProfiles γ
        exact ⟨low,G,hSmooth,(fun k hk n hn => hBound k hk n (hn.trans (by decide))),hSource⟩)
      arguments (fun _ => ()) (fun _ => ()) (fun _ => ())
    have hField : ‖radianTrilinearForm m f g h‖ ≤
        K * ‖schwartzFieldLp3 (fun _ : Unit => f)‖ * ‖schwartzFieldLp3 (fun _ : Unit => g)‖ *
          ‖schwartzFieldLp3 (fun _ : Unit => h)‖ := by
      simpa [arguments,K] using e
    apply hField.trans
    simp only [triLpMass,ENNReal.toReal_mul,hThree]
    calc
      _ ≤ K * (eLpNorm (f : E → ℂ) 3 volume).toReal * (eLpNorm (g : E → ℂ) 3 volume).toReal *
          (eLpNorm (h : E → ℂ) 3 volume).toReal := by
        have hf : 0 ≤ (eLpNorm (f : E → ℂ) 3 volume).toReal := ENNReal.toReal_nonneg
        have hg : 0 ≤ (eLpNorm (g : E → ℂ) 3 volume).toReal := ENNReal.toReal_nonneg
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left (hScalarNorm f) hK) (hScalarNorm g)
            (norm_nonneg _) (mul_nonneg hK hf))
          (hScalarNorm h) (norm_nonneg _) (mul_nonneg (mul_nonneg hK hf) hg)
      _ = _ := by ring
  have hScale : (1+T)*K = L := by dsimp only [K,L]; ring
  have hFull : K ≤ L := hScale ▸ le_mul_of_one_le_left hK (le_add_of_nonneg_right hT)
  have hTrunc : T*K ≤ L := hScale ▸ mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hK
  refine ⟨fun f g h => (estimate f g h).trans (mul_le_mul_of_nonneg_right hFull ENNReal.toReal_nonneg),?_⟩
  intro I J L' a b' c ha hb' hc f g h
  exact (trunc m K hK estimate I J L' a b' c ha hb' hc f g h).trans
    (mul_le_mul_of_nonneg_right hTrunc ENNReal.toReal_nonneg)

end Burnett.C02
