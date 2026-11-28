import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearPatchRate
import Burnett.Analysis.AllScaleTransfer.ActualNearWithProfiles

set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 14500000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory
open Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05 Burnett.A05.BoxFourier
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.Analysis.CapFourier
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.P01 (ProjectionSchwartzMatrix)
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The exact signed endpoint and comparable-box inputs of the public
A05 near estimate for the given localized physical symbols. -/
def WardNearA05Profiles {m : Form} {δ η inn out enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps m δ η inn out enlarged D)
    (chart : ∀ γ : ↑S.centers, NullCapChart m γ)
    (ϑ : ℝ → ℝ) (κ R b A : ℝ) (N : ℕ) (sym : WardNearEntries → Joint → ℂ) : Prop :=
  ∀ (γ : ↑S.centers) (j : WardNearEntries),
    let a := capFrequencyEquiv (chart γ) hδ
    let K := tsupport (enlargedCapMultiplier m δ η out enlarged γ)
    let μ := ((δ^2)⁻¹ • capLocalizedNearSymbol S (sym j) γ : Joint → ℂ)
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
    (∃ F : ℤ → BoxSpace → ℂ,
      (∀ k ∈ I, ContDiffOn ℝ 100 (F k) (ball (0 : BoxSpace) 5)) ∧
      (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (F k) z‖ ≤ A) ∧
      ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
        F k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ))

/-- Once the exact local profiles are provided, the public A05 bound
acts on the original physical gradient input and the original near form. -/
theorem exists_wardActualNearFieldBound_of_A05Profiles
    (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube out enlarged κ l b : ℝ) (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ out)
    (hOE : out < enlarged) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hl : 0 < l) (hb : 7*κ/4 < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (hχOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hχZero : ∀ t, 7*κ/4 ≤ t → χ t = 0) :
    ∃ (R : ℝ) (N : ℕ) (Cκ : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ Cκ ∧
      ∀ (G : Mat), Matrix.det G ≠ 0 → ∀ (a : E → ℝ) (wi wo : ℝ)
        (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G))
        (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (i o inn D C₃ : ℝ)
        (S : SmoothThinConeCaps (inverseMatrix G) δ (tube*δ^2) inn out enlarged D)
        (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
          (enlargedCapMultiplier (inverseMatrix G) δ (tube*δ^2) out enlarged γ) C₃)
        (chart : ∀ γ : ↑S.centers, NullCapChart (inverseMatrix G) γ),
      (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) →
      (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) →
      ∀ q A C H : ℝ, 3 < q → 4*B*(5*δ) ≤ 1 → 0 < D → 0 ≤ A → 0 ≤ C →
      (∀ v : FieldLp WardNearSlot (ENNReal.ofReal 3),
        (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^(1/3 : ℝ) ≤
          ((Fintype.card WardNearSlot : ℝ)*C)*(S.centers.card : ℝ)^(1/(3*(q-2)))*‖v‖) →
      let hη : 0 < tube*δ^2 := mul_pos hTube (pow_pos hδ.1 _)
      let sym := wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o
      (∀ j, Measurable (sym j)) →
      (∀ j x, ‖sym j x‖ ≤ H) →
      (∀ j (t : ℝ), 0 < t → ∀ x : Joint, sym j (t • x) = sym j x) →
      (∀ j (p : Joint), sym j p ≠ 0 → p.1 ≠ 0 → p.2 ≠ 0 → -(p.1+p.2) ≠ 0 →
        |quadratic (inverseMatrix G) p.1| ≤ inn*(tube*δ^2)*‖p.1‖^2 ∧
        ∀ γ : ↑S.centers, capMultiplier S.centers (inverseMatrix G) δ (tube*δ^2) inn out γ p.1 ≠ 0 →
          enlargedCapMultiplier (inverseMatrix G) δ (tube*δ^2) out enlarged γ p.1 = 1 ∧
          enlargedCapMultiplier (inverseMatrix G) δ (tube*δ^2) out enlarged γ p.2 = 1 ∧
          enlargedCapMultiplier (inverseMatrix G) δ (tube*δ^2) out enlarged γ (-(p.1+p.2)) = 1) →
      WardNearA05Profiles hδ.1.ne' S chart ϑ κ R b A N sym →
      ∀ z : ProjectionSchwartzMatrix,
        let Cnear := ((Cκ*(Fintype.card WardNearEntries : ℝ))*((Fintype.card WardNearSlot : ℝ)*C)^3*
          D^(1/(q-2)))*A
        ‖wardActualNearCubicForm G a ϑ κ δ wi wo hm hη i o z‖ ≤
          Cnear*δ^(2*(q-3)/(q-2))*‖schwartzFieldLp3 (wardNearGradient z)‖^3 := by
  obtain ⟨R,N,Cκ,hR,hR1,hCκ,applyNear⟩ := exists_actual_radian_near_field_bound
    (ι := WardNearSlot) (ξ := WardNearEntries) ϑ hϑ hRange hCut hFlat B tube out enlarged κ l b
    hB hTube hOut hOE hκ hκsmall hl hb χ hχ hχRange hχOne hχZero
  refine ⟨R,N,Cκ,hR,hR1,hCκ,?_⟩
  intro G hG a wi wo hm δ hδ i o inn D C₃ S Pplus chart hF hI q A C H hq hSmall hD hA hC hAngular
    hη sym hM hMag hHom hS hProfiles z Cnear
  have hInt (j : WardNearEntries) := integrable_radianTrilinearWeight_of_bounded (sym j)
    (hM j).aestronglyMeasurable H (hMag j)
    (wardNearGradient z j.1) (wardNearGradient z j.2.1) (wardNearGradient z j.2.2)
  have hEq := (wardActualNearCubicForm_eq_gradientSum G hG a ϑ κ δ wi wo hm hη i o z hInt).2
  rw [hEq]
  have hBound := applyNear S Pplus chart hF hI hq hδ hSmall hD hA hC hAngular sym H hM hMag hHom hS hProfiles
    (fun _ => wardNearGradient z) Prod.fst (fun j => j.2.1) (fun j => j.2.2)
  dsimp only at hBound
  exact hBound.trans_eq (by unfold Cnear; ring)

end Burnett.C02
