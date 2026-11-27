import Burnett.Analysis.AllScaleTransfer.AnalyticNearUnscaled
import Burnett.Analysis.AllScaleTransfer.AnalyticNearScalar
import Burnett.Analysis.Fourier.FixedInfraredSchwartz

set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 10000000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier Burnett.C02
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.Analysis.LowRatio (Point)
open scoped ContDiff ENNReal

/-- A representative of the actual Fourier multiplier on the signed
plane `(p,q,-(p+q))`. The representative's bound is used for integration. -/
structure AnalyticNearSymbol (m : Joint → ℂ) : Prop where
  measurable : Measurable m
  bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖m z‖ ≤ B
  homogeneous : ∀ t : ℝ, 0 < t → ∀ z : Joint, m (t • z) = m z

/-- One uniform order-100 bound for all normalized comparable windows. -/
def AnalyticNearComparableBudget (N : ℕ) (A : ℝ) (m : Joint → ℂ) : Prop :=
  ∃ G : ℤ → BoxSpace → ℂ,
    let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
    (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) 5)) ∧
    (∀ k ∈ I, ∀ n ≤ 100, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ A) ∧
    ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
      G k (joinedInputs ζ υ) = m ((2 : ℝ)^k • ζ,υ)

/-- The three unscaled low pieces use genuine one-sided ratio endpoints
and compatible chart traces of those endpoints. -/
def AnalyticNearUnscaledLowBudget (ϑ : ℝ → ℝ) (κ b A : ℝ) (m : Joint → ℂ) : Prop :=
  ∀ slot : Fin 3, ∃ (M : WardPairChart → Point → ℂ) (M₀ : Joint → ℂ),
    (∀ i, ContDiffOn ℝ 100 (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b)) ∧
    (∀ i n, n ≤ 100 → ∀ z ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
    (∀ i pq, pq ∈ wardPairChartAnnulus i →
      M₀ (endpointDirection pq.1,endpointDirection pq.2) = M i (wardPairChartAngles i pq,0)) ∧
    ∀ i pq, pq ∈ wardPairChartAnnulus i → ∀ t : ℝ, 0 < t →
      let ρ := t*(‖pq.1‖/‖pq.2‖)
      ρ ∈ Ioo (0 : ℝ) b →
        radianFourBranchSymbol ϑ κ (radianLowSlotView m slot) 0 (t • pq.1,pq.2) =
          M i (wardPairChartAngles i pq,ρ)

/-- Nonzero frequencies of the same signed triad lie in the thin cone
and satisfy the two projective cap adjacency bounds at its first slot. -/
def AnalyticNearAdjacentSupport (metric : Form) (δ η inner : ℝ) (m : Joint → ℂ) : Prop :=
  ∀ p : Joint, m p ≠ 0 → p.1 ≠ 0 → p.2 ≠ 0 → -(p.1+p.2) ≠ 0 →
    let r := -(p.1+p.2)
    InRelativeCone metric (inner*η) p.1 ∧ InRelativeCone metric (inner*η) p.2 ∧
      InRelativeCone metric (inner*η) r ∧
      projectiveWedgeSq p.1 p.2 ≤ δ^2 ∧ projectiveWedgeSq p.1 r ≤ δ^2

/-- Exact normalized multiplier after localizing by the real base cap
and dividing by the single quadratic thin-angle gain. -/
def AnalyticNearCapBudget (ϑ : ℝ → ℝ) (κ b R A : ℝ) (N : ℕ)
    {metric : Form} {δ η inner outer enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (chart : ∀ γ : ↑S.centers, NullCapChart metric γ) (m : Joint → ℂ) : Prop :=
  ∀ γ : ↑S.centers,
    let a := capFrequencyEquiv (chart γ) hδ
    let K := tsupport (enlargedCapMultiplier metric δ η outer enlarged γ)
    let mγ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
    let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (radianLowSlotView mγ i) 0 ∘ pairedFrequencyEquiv a
    let comparable := radianFourBranchSymbol ϑ κ mγ 3 ∘ pairedFrequencyEquiv a
    (∃ (M : Fin 3 → E → E → ℝ → ℂ) (B₀ : ℝ),
      (∀ i, Measurable (fun p : Joint => M i p.1 p.2 0)) ∧
      (∀ i (p : Joint), ‖M i p.1 p.2 0‖ ≤ B₀) ∧
      (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
      (∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
      ∀ (i : Fin 3) (p : Joint), a p.1 ∈ K → a p.2 ∈ K → a (-(p.1+p.2)) ∈ K →
        ‖a p.1‖/‖a p.2‖ ∈ Ioo (0 : ℝ) b →
          low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖a p.1‖/‖a p.2‖)) ∧
      AnalyticNearComparableBudget N A comparable

/-- A fixed smooth radial high-pass window allowed on any single
differentiated factor. The thresholds and profile are fixed data. -/
structure AnalyticNearInfraredWindow where
  profile : ℝ → ℝ
  smooth : ContDiff ℝ ∞ profile
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  below : ∀ t ≤ lower, profile t = 0
  above : ∀ t ≥ upper, profile t = 1

def analyticNearWindow (window : Option AnalyticNearInfraredWindow) (f : SchwartzMap E ℂ) :
    SchwartzMap E ℂ :=
  match window with
  | none => f
  | some w => Burnett.A07.fixedInfraredSchwartz w.profile w.smooth w.lower w.upper w.lower_pos
      w.below w.above f

/-- Full form and independently signed finite dyadic truncations in
each of its three differentiated factors, with the same constant. -/
def AnalyticNearFormBound (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    (m : Joint → ℂ) (C : ℝ) : Prop :=
  (∀ f g h : SchwartzMap E ℂ,
    ‖radianTrilinearForm m (analyticNearWindow (windows 0) f)
      (analyticNearWindow (windows 1) g) (analyticNearWindow (windows 2) h)‖ ≤
        C*(triLpMass f g h 3 3 3).toReal) ∧
  ∀ (I J L : Finset ℤ) (a b c : ℤ → ℂ),
    (∀ j ∈ I, ‖a j‖ ≤ 1) → (∀ j ∈ J, ‖b j‖ ≤ 1) → (∀ j ∈ L, ‖c j‖ ≤ 1) →
    ∀ f g h : SchwartzMap E ℂ,
      ‖radianTrilinearForm m
        (finiteIntegerRadialTruncation I a (analyticNearWindow (windows 0) f))
        (finiteIntegerRadialTruncation J b (analyticNearWindow (windows 1) g))
        (finiteIntegerRadialTruncation L c (analyticNearWindow (windows 2) h))‖ ≤
      C*(triLpMass f g h 3 3 3).toReal

/-- Three independently fixed infrared windows affect only the
constant in the estimate, with no extra dyadic or thin-angle norm. -/
theorem exists_analyticNear_window_bound (windows : Fin 3 → Option AnalyticNearInfraredWindow) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : Joint → ℂ) (C : ℝ), 0 ≤ C →
      AnalyticNearFormBound (fun _ => none) m C → AnalyticNearFormBound windows m (K*C) := by
  let mass (f : SchwartzMap E ℂ) := (eLpNorm (f : E → ℂ) (ENNReal.ofReal 3) volume).toReal
  have one (window : Option AnalyticNearInfraredWindow) :
      ∃ P : ℝ, 0 ≤ P ∧ ∀ f : SchwartzMap E ℂ, mass (analyticNearWindow window f) ≤ P*mass f := by
    cases window with
    | none => exact ⟨1,zero_le_one,fun f => by simp [analyticNearWindow]⟩
    | some w =>
      obtain ⟨P,hP,applyWindow⟩ := Burnett.A07.exists_fixedInfraredSchwartz_Lp_bound
        w.profile w.smooth w.lower w.upper w.lower_pos w.below w.above 3 (by norm_num)
      refine ⟨P.toReal,ENNReal.toReal_nonneg,?_⟩
      intro f
      have hfinite := ENNReal.mul_ne_top hP.ne ((f.memLp (ENNReal.ofReal 3) volume).eLpNorm_ne_top)
      simpa only [analyticNearWindow,mass,ENNReal.toReal_mul] using
        (ENNReal.toReal_mono hfinite (applyWindow f))
  obtain ⟨P₀,hP₀,w₀⟩ := one (windows 0)
  obtain ⟨P₁,hP₁,w₁⟩ := one (windows 1)
  obtain ⟨P₂,hP₂,w₂⟩ := one (windows 2)
  let K := P₀*P₁*P₂
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hP₀ hP₁) hP₂
  have mass_nonneg (f : SchwartzMap E ℂ) : 0 ≤ mass f := ENNReal.toReal_nonneg
  have hMass (f g h : SchwartzMap E ℂ) :
      (triLpMass (analyticNearWindow (windows 0) f) (analyticNearWindow (windows 1) g)
        (analyticNearWindow (windows 2) h) 3 3 3).toReal ≤ K*(triLpMass f g h 3 3 3).toReal := by
    simp only [triLpMass,ENNReal.toReal_mul]
    change mass (analyticNearWindow (windows 0) f) * mass (analyticNearWindow (windows 1) g) *
      mass (analyticNearWindow (windows 2) h) ≤ K*(mass f*mass g*mass h)
    calc
      _ ≤ (P₀*mass f)*(P₁*mass g)*(P₂*mass h) :=
        mul_le_mul (mul_le_mul (w₀ f) (w₁ g) (mass_nonneg _) (mul_nonneg hP₀ (mass_nonneg f)))
          (w₂ h) (mass_nonneg _) (mul_nonneg (mul_nonneg hP₀ (mass_nonneg f)) (mul_nonneg hP₁ (mass_nonneg g)))
      _ = _ := by unfold K; ring
  refine ⟨K,hK,?_⟩
  intro m C hC estimate
  have scale (f g h : SchwartzMap E ℂ) :
      C*(triLpMass (analyticNearWindow (windows 0) f) (analyticNearWindow (windows 1) g)
        (analyticNearWindow (windows 2) h) 3 3 3).toReal ≤ (K*C)*(triLpMass f g h 3 3 3).toReal :=
    (mul_le_mul_of_nonneg_left (hMass f g h) hC).trans_eq (by ring)
  refine ⟨?_,?_⟩
  · intro f g h
    exact (estimate.1 (analyticNearWindow (windows 0) f) (analyticNearWindow (windows 1) g)
      (analyticNearWindow (windows 2) h)).trans (scale f g h)
  · intro I J L a b c ha hb hc f g h
    exact (estimate.2 I J L a b c ha hb hc (analyticNearWindow (windows 0) f)
      (analyticNearWindow (windows 1) g) (analyticNearWindow (windows 2) h)).trans (scale f g h)

end Burnett.A05
