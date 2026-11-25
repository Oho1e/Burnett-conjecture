import Burnett.Analysis.AllScaleTransfer.ActualNearCapCoreBound
import Burnett.Analysis.AllScaleTransfer.ActualAdjacentNearOuter
import Burnett.Analysis.AllScaleTransfer.ActualFieldRadialLimit

set_option autoImplicit false
set_option maxHeartbeats 10000000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The actual near form under the fixed partition and the uniform
one-sided C100 hypotheses of the normalized cap symbols. Symmetric
radial truncations converge back to the original Fourier form. -/
theorem exists_actual_radian_near_field_bound {ι ξ : Type*} [Fintype ι] [Fintype ξ]
    (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube outer enlarged κ l b : ℝ) (hB : 0 < B) (hTube : 0 < tube)
    (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hl : 0 < l) (hb : 7*κ/4 < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (hχOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hχZero : ∀ t, 7*κ/4 ≤ t → χ t = 0) :
    ∃ (R : ℝ) (N : ℕ) (Cκ : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ Cκ ∧
      ∀ {metric : Form} {δ inner D C₃ : ℝ},
      ∀ (S : SmoothThinConeCaps metric δ (tube*δ^2) inner outer enlarged D)
        (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
          (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ) C₃)
        (chart : ∀ γ : ↑S.centers, NullCapChart metric γ),
      (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) →
      (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) →
      ∀ {q A C : ℝ} (_ : 3 < q) (hδ : δ ∈ Ioc (0 : ℝ) 1),
      4*B*(5*δ) ≤ 1 → 0 < D → 0 ≤ A → 0 ≤ C →
      (∀ v : FieldLp ι (ENNReal.ofReal 3),
        (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^(1/3 : ℝ) ≤
          ((Fintype.card ι : ℝ) * C) * (S.centers.card : ℝ)^(1/(3*(q-2))) * ‖v‖) →
      ∀ (m : ξ → Joint → ℂ) (H : ℝ), (∀ k, Measurable (m k)) →
      (∀ k p, ‖m k p‖ ≤ H) → (∀ k (t : ℝ), 0 < t → ∀ p : Joint, m k (t • p) = m k p) →
      (∀ k (p : Joint), m k p ≠ 0 → p.1 ≠ 0 → p.2 ≠ 0 → -(p.1+p.2) ≠ 0 →
        |quadratic metric p.1| ≤ inner*(tube*δ^2)*‖p.1‖^2 ∧
        ∀ γ : ↑S.centers, capMultiplier S.centers metric δ (tube*δ^2) inner outer γ p.1 ≠ 0 →
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ p.1 = 1 ∧
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ p.2 = 1 ∧
          enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ (-(p.1+p.2)) = 1) →
      (∀ (γ : ↑S.centers) (k : ξ),
        let a := capFrequencyEquiv (chart γ) hδ.1.ne'
        let K := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged γ)
        let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S (m k) γ : Joint → ℂ)
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
          (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ A) ∧
          ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
            G k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ))) →
      ∀ (f : Fin 3 → ι → SchwartzMap E ℂ) (left middle right : ξ → ι),
      let V (i : Fin 3) := schwartzFieldLp3 (f i)
      ‖∑ k : ξ, radianTrilinearForm (m k) (f 0 (left k)) (f 1 (middle k)) (f 2 (right k))‖ ≤
        ((Cκ * (Fintype.card ξ : ℝ)) * ((Fintype.card ι : ℝ) * C)^3 * D^(1/(q-2))) *
          A * δ^(2*(q-3)/(q-2)) * ‖V 0‖ * ‖V 1‖ * ‖V 2‖ := by
  obtain ⟨R,N,Cκ,hR,hR1,hCκ,core⟩ := exists_actual_near_cap_core_bound ϑ hϑ hRange hCut hFlat
    B tube outer enlarged κ l b hB hTube hOut hOE hκ hκsmall hl hb χ hχ hχRange hχOne hχZero
  obtain ⟨Tr,hTr,lim⟩ := exists_radianTrilinearForm_field_bound_of_symmetric_radial_bounds (ι := ι) (ξ := ξ)
  refine ⟨R,N,Cκ*Tr^3,hR,hR1,by positivity,?_⟩
  intro metric δ inner D C₃ S Pplus chart hfwd hinv q A C hq hδ hSmall hD hA hC angular
    m H hm hBound hom support profiles f left middle right V
  have hδpos : 0 < δ := hδ.1
  have hη : 0 < tube*δ^2 := mul_pos hTube (pow_pos hδpos 2)
  let L := ((Cκ * (Fintype.card ξ : ℝ)) * ((Fintype.card ι : ℝ) * C)^3 * D^(1/(q-2))) *
    A * δ^(2*(q-3)/(q-2))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have int (k : ξ) : Integrable (radianTrilinearWeight (m k) (f 0 (left k)) (f 1 (middle k)) (f 2 (right k))) :=
    integrable_radianTrilinearWeight_of_bounded (m k) (hm k).aestronglyMeasurable H (hBound k)
      (f 0 (left k)) (f 1 (middle k)) (f 2 (right k))
  have finite (n : ℕ) :
      let F (i : Fin 3) (a : ι) :=
        finiteIntegerRadialTruncation (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun _ => 1) (f i a)
      ‖∑ k : ξ, radianTrilinearForm (m k) (F 0 (left k)) (F 1 (middle k)) (F 2 (right k))‖ ≤
        L * ‖schwartzFieldLp3 (F 0)‖ * ‖schwartzFieldLp3 (F 1)‖ * ‖schwartzFieldLp3 (F 2)‖ := by
    dsimp only
    refine radian_near_finite_field_bound_of_adjacent_plateaux S Pplus hq hδ hη hD hCκ hA hC angular
      m (fun k => (hm k).aestronglyMeasurable) H hBound (fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ))
      (fun _ _ => 1) f left middle right chart support ?_
    intro γ k f' g' h' P ff gf hf pcf pcg pch
    obtain ⟨low,comparable⟩ := profiles γ k
    exact core S hδ.1 hδ.2 hSmall γ (chart γ) (hfwd γ) (hinv γ)
      (m k) H (hm k) (hBound k) (hom k) A hA low comparable f' g' h' ff gf hf pcf pcg pch
  calc
    _ ≤ (L*Tr^3)*‖V 0‖*‖V 1‖*‖V 2‖ := lim m f left middle right int L hL finite
    _ = _ := by unfold L; ring

end Burnett.A05
