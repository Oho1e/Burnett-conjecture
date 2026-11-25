import Burnett.Analysis.AllScaleTransfer.ActualCapFullSpectrum
import Burnett.Analysis.AllScaleTransfer.ActualNearCoreSymbol

set_option autoImplicit false
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff

/-- Apply the normalized scalar estimate to the actual cap partition
coefficient after removing its source prefactor. The hypotheses on the
charts and boxes identify the three physical low branches and the
comparable branch of that coefficient. -/
theorem exists_actual_near_cap_core_bound
    (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube outer enlarged κ l b : ℝ) (hB : 0 < B) (hTube : 0 < tube)
    (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hl : 0 < l) (hb : 7*κ/4 < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (hχOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hχZero : ∀ t, 7*κ/4 ≤ t → χ t = 0) :
    ∃ (R : ℝ) (N : ℕ) (C : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ C ∧
      ∀ {metric : Form} {δ inner D : ℝ}
        (S : SmoothThinConeCaps metric δ (tube*δ^2) inner outer enlarged D)
        (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
      ∀ (γ : ↑S.centers) (F : NullCapChart metric γ),
        ‖F.toFrequency.toContinuousLinearMap‖ ≤ B → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ (m : Joint → ℂ) (H : ℝ), Measurable m → (∀ p, ‖m p‖ ≤ H) →
      (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      let A := capFrequencyEquiv F hδ.ne'
      let K := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ)
      let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
      let bases : Fin 3 → Joint → ℂ := ![μ,μ ∘ radianCycle.symm,μ ∘ radianCycle]
      let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (bases i) 0 ∘ pairedFrequencyEquiv A
      let comparable := radianFourBranchSymbol ϑ κ μ 3 ∘ pairedFrequencyEquiv A
      let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
      ∀ (Q : ℝ), 0 ≤ Q →
      (∃ (M : Fin 3 → E → E → ℝ → ℂ) (B₀ : ℝ),
        (∀ i, Measurable (fun p : Joint => M i p.1 p.2 0)) ∧
        (∀ i (p : Joint), ‖M i p.1 p.2 0‖ ≤ B₀) ∧
        (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
        (∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
          ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
            (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ Q) ∧
        ∀ (i : Fin 3) (p : Joint), A p.1 ∈ K → A p.2 ∈ K → A (-(p.1+p.2)) ∈ K →
          ‖A p.1‖/‖A p.2‖ ∈ Ioo (0 : ℝ) b →
          low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖)) →
      (∃ G : ℤ → BoxSpace → ℂ,
        (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) 5)) ∧
        (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ Q) ∧
        ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
          G k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ)) →
      ∀ f g h : SchwartzMap E ℂ, EndpointFiniteAnnulus f → EndpointFiniteAnnulus g → EndpointFiniteAnnulus h →
      (∀ p, radianFourier f p ≠ 0 → A p ∈ K) →
      (∀ p, radianFourier g p ≠ 0 → A p ∈ K) →
      (∀ p, radianFourier h p ≠ 0 → A p ∈ K) →
      ‖radianTrilinearForm (μ ∘ pairedFrequencyEquiv A) f g h‖ ≤ C*Q*(triLpMass f g h 3 3 3).toReal := by
  obtain ⟨R,N,C,hR,hR1,hC,bound⟩ := exists_actual_cap_normalized_full_spectrum_bound
    ϑ hϑ hRange hCut hFlat 5 B tube outer enlarged κ l b (by norm_num)
    hB hTube hOut hOE hκ hκsmall hl hb χ hχ hχRange hχOne hχZero
  refine ⟨R,N,C,hR,hR1,hC,?_⟩
  intro metric δ inner D S hδ hδ1 hSmall γ F hF hFI m H hm hBound hom A K μ bases low comparable I
    Q hQ charts boxes f g h ff gf hf pc qc rc
  obtain ⟨M,B₀,meas₀,b₀,sM,jM,matchLow⟩ := charts
  obtain ⟨G,sG,bG,matchG⟩ := boxes
  obtain ⟨hmCore,hCore,homCore⟩ := capLocalizedNearSymbol_core_properties S m hm H hBound hom γ
  refine bound metric γ F (S.centers_null γ.property).1 hF hFI δ hδ hδ1 hSmall μ ((δ^2)⁻¹*H)
    hmCore hCore homCore M B₀ Q hQ meas₀ b₀ sM jM G sG bG matchG f g h ff gf hf pc qc rc ?_
  intro i p hp hρ
  have supports (x y z : SchwartzMap E ℂ)
      (hx : ∀ u, radianFourier x u ≠ 0 → A u ∈ K)
      (hy : ∀ u, radianFourier y u ≠ 0 → A u ∈ K)
      (hz : ∀ u, radianFourier z u ≠ 0 → A u ∈ K)
      (hW : radianWeight (fun _ => 1) x y z p ≠ 0) :
      A p.1 ∈ K ∧ A p.2 ∈ K ∧ A (-(p.1+p.2)) ∈ K :=
    ⟨hx _ (fun h0 => hW (by simp only [radianWeight,h0,zero_mul,mul_zero])),
      hy _ (fun h0 => hW (by simp only [radianWeight,h0,zero_mul,mul_zero])),
      hz _ (fun h0 => hW (by simp only [radianWeight,h0,mul_zero]))⟩
  have xyz : A p.1 ∈ K ∧ A p.2 ∈ K ∧ A (-(p.1+p.2)) ∈ K := by
    fin_cases i
    · exact supports f g h pc qc rc hp
    · exact supports g h f qc rc pc hp
    · exact supports h f g rc pc qc hp
  exact matchLow i p xyz.1 xyz.2.1 xyz.2.2 hρ

end Burnett.A05
