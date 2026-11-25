import Burnett.Analysis.AllScaleTransfer.ActualEnlargedCapFiniteFactor
import Burnett.Analysis.AngularCaps.SmoothCapFamily

set_option autoImplicit false
set_option maxHeartbeats 3400000

noncomputable section

namespace Burnett.A05

open Set Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped BigOperators

/-- Insert the actual cap partition only in the designated first slot. -/
def capLocalizedNearSymbol
    {metric : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (m : Joint → ℂ) (γ : ↑S.centers) (p : Joint) : ℂ :=
  (capMultiplier S.centers metric δ η inner outer γ p.1 : ℂ) * m p

/-- A single actual angular partition and the three enlarged plateaux recover
the source integral, with the same three radian spectra and signed sum. -/
theorem radianTrilinearForm_eq_sum_capLocalizedNearSymbol
    {metric : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (m : Joint → ℂ) (hm : AEStronglyMeasurable m volume)
    (B : ℝ) (hBound : ∀ p, ‖m p‖ ≤ B)
    (F : Fin 3 → SchwartzMap E ℂ) (u : ↑S.centers → Fin 3 → SchwartzMap E ℂ)
    (hFourier : ∀ γ i ξ, radianFourier (u γ i : E → ℂ) ξ =
      (enlargedCapMultiplier metric δ η outer enlarged γ ξ : ℂ) *
        radianFourier (F i : E → ℂ) ξ)
    (hPartition : ∀ p, radianTrilinearWeight m (F 0) (F 1) (F 2) p ≠ 0 →
      p.1 ≠ 0 ∧ |quadratic metric p.1| ≤ inner*η*‖p.1‖^2)
    (hPlateau : ∀ (γ : ↑S.centers) p, radianTrilinearWeight m (F 0) (F 1) (F 2) p ≠ 0 →
      capMultiplier S.centers metric δ η inner outer γ p.1 ≠ 0 →
      enlargedCapMultiplier metric δ η outer enlarged γ p.1 = 1 ∧
        enlargedCapMultiplier metric δ η outer enlarged γ p.2 = 1 ∧
        enlargedCapMultiplier metric δ η outer enlarged γ (-(p.1+p.2)) = 1) :
    radianTrilinearForm m (F 0) (F 1) (F 2) =
      ∑ γ : ↑S.centers, radianTrilinearForm (capLocalizedNearSymbol S m γ)
        (u γ 0) (u γ 1) (u γ 2) := by
  classical
  let P (γ : ↑S.centers) := capMultiplier S.centers metric δ η inner outer (γ : Vec)
  let Q (γ : ↑S.centers) := enlargedCapMultiplier metric δ η outer enlarged (γ : Vec)
  let T := radianTrilinearWeight m (F 0) (F 1) (F 2)
  let L (γ : ↑S.centers) :=
    radianTrilinearWeight (capLocalizedNearSymbol S m γ) (u γ 0) (u γ 1) (u γ 2)
  have integrable (γ : ↑S.centers) : Integrable (L γ) := by
    have measP : Measurable (P γ) :=
      measurable_of_continuousOn_compl_singleton (0 : Vec)
        (S.smoothness γ γ.property).1.continuousOn
    have measC : Measurable (fun p : Joint => (P γ p.1 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (measP.comp measurable_fst)
    have hMeas : AEStronglyMeasurable (capLocalizedNearSymbol S m γ) volume :=
      measC.aestronglyMeasurable.mul hm
    have hLocal (p : Joint) : ‖capLocalizedNearSymbol S m γ p‖ ≤ B := by
      have hr := S.base_range γ γ.property p.1
      rw [capLocalizedNearSymbol, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1]
      exact ((mul_le_mul_of_nonneg_right hr.2 (norm_nonneg (m p))).trans_eq
        (one_mul (‖m p‖))).trans (hBound p)
    exact integrable_radianTrilinearWeight_of_bounded _ hMeas B hLocal _ _ _
  have localWeight (γ : ↑S.centers) (p : Joint) : L γ p = (P γ p.1 : ℂ) * T p := by
    have factor : L γ p =
        ((P γ p.1 : ℂ) * (Q γ p.1 : ℂ) * (Q γ p.2 : ℂ) * (Q γ (-(p.1+p.2)) : ℂ)) * T p := by
      simp only [L, T, radianTrilinearWeight, radianWeight, capLocalizedNearSymbol,
        hFourier, P, Q]
      ring
    rw [factor]
    by_cases hz : T p = 0
    · simp only [hz, mul_zero]
    by_cases hP : P γ p.1 = 0
    · simp only [hP, Complex.ofReal_zero, zero_mul]
    obtain ⟨h₀, h₁, h₂⟩ := hPlateau γ p hz hP
    change Q γ p.1 = 1 at h₀
    change Q γ p.2 = 1 at h₁
    change Q γ (-(p.1+p.2)) = 1 at h₂
    simp only [h₀, h₁, h₂, Complex.ofReal_one, mul_one]
  have localSum (p : Joint) : (∑ γ : ↑S.centers, L γ p) = T p := by
    simp only [localWeight, ← Finset.sum_mul]
    by_cases hz : T p = 0
    · simp only [hz, mul_zero]
    obtain ⟨hp, hCone⟩ := hPartition p hz
    have hOne := S.partition_inner p.1 hp hCone
    have hC : (∑ γ : ↑S.centers, (P γ p.1 : ℂ)) = 1 := by
      rw [← Complex.ofReal_sum, Finset.univ_eq_attach,
        Finset.sum_attach S.centers (fun w => capMultiplier S.centers metric δ η inner outer w p.1),
        hOne, Complex.ofReal_one]
    rw [hC, one_mul]
  change (tau^8)⁻¹ • (∫ p, T p) = ∑ γ : ↑S.centers, (tau^8)⁻¹ • ∫ p, L γ p
  rw [← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun γ _ => integrable γ)]
  exact congrArg ((tau^8)⁻¹ • ·) (integral_congr_ae (Eventually.of_forall fun p => (localSum p).symm))

/-- The actual near weight supplies both projective edges for the same
cap family. Each projected input is the actual enlarged radian action on
its own finite radial truncation. -/
theorem exists_actual_nearCap_decomposition
    {metric : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (hδ : 0 < δ) (hη : 0 < η) {ϑ : ℝ → ℝ} (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (m : Joint → ℂ) (hm : AEStronglyMeasurable m volume)
    (B : ℝ) (hBound : ∀ p, ‖m p‖ ≤ B)
    (J : Fin 3 → Finset ℤ) (ε : Fin 3 → ℤ → ℂ) (f : Fin 3 → SchwartzMap E ℂ) :
    let F := fun i : Fin 3 => finiteIntegerRadialTruncation (J i) (ε i) (f i)
    (∀ p, radianTrilinearWeight m (F 0) (F 1) (F 2) p ≠ 0 →
      |quadratic metric p.1| ≤ inner*η*‖p.1‖^2 ∧
        |quadratic metric p.2| ≤ outer*η*‖p.2‖^2 ∧
        |quadratic metric (-(p.1+p.2))| ≤ outer*η*‖-(p.1+p.2)‖^2 ∧
        angularNearWeight ϑ δ p.1 p.2 (-(p.1+p.2)) ≠ 0) →
    ∃ u : ↑S.centers → Fin 3 → SchwartzMap E ℂ,
      (∀ γ i x, u γ i x = radianAction (enlargedCapMultiplier metric δ η outer enlarged γ) (F i) x) ∧
      (∀ γ i ξ, radianFourier (u γ i : E → ℂ) ξ =
        (enlargedCapMultiplier metric δ η outer enlarged γ ξ : ℂ) *
          radianFourier (F i : E → ℂ) ξ) ∧
      (∀ γ i, tsupport (radianFourier (u γ i : E → ℂ)) ⊆
        tsupport (enlargedCapMultiplier metric δ η outer enlarged γ) ∩
          tsupport (radianFourier (F i : E → ℂ))) ∧
      radianTrilinearForm m (F 0) (F 1) (F 2) =
        ∑ γ : ↑S.centers, radianTrilinearForm (capLocalizedNearSymbol S m γ)
          (u γ 0) (u γ 1) (u γ 2) := by
  intro F hGeom
  have center (γ : ↑S.centers) : (γ : Vec) ≠ 0 := by
    intro h
    have hn := (S.centers_null γ.property).1
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  choose u hAction hFourier hSupport using
    fun (γ : ↑S.centers) (i : Fin 3) =>
      exists_enlargedCap_finiteIntegerRadialTruncation_schwartz metric δ hη outer enlarged
        (center γ) (J i) (ε i) (f i)
  refine ⟨u, hAction, hFourier, hSupport, ?_⟩
  have nonzero (i : Fin 3) (ξ : E) (h : radianFourier (F i : E → ℂ) ξ ≠ 0) : ξ ≠ 0 := by
    rintro rfl
    exact zero_notMem_finiteIntegerRadialFrequencySupport (J i)
      (tsupport_radianFourier_finiteIntegerRadialTruncation (J i) (ε i) (f i) (subset_tsupport _ h))
  have active (p : Joint) (hp : radianTrilinearWeight m (F 0) (F 1) (F 2) p ≠ 0) :
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ -(p.1+p.2) ≠ 0 := by
    unfold radianTrilinearWeight radianWeight at hp
    refine ⟨nonzero 0 p.1 ?_, nonzero 1 p.2 ?_, nonzero 2 (-(p.1+p.2)) ?_⟩ <;>
      intro h <;> exact hp (by simp only [h, mul_zero, zero_mul])
  apply radianTrilinearForm_eq_sum_capLocalizedNearSymbol S m hm B hBound F u hFourier
  · exact fun p hp => ⟨(active p hp).1, (hGeom p hp).1⟩
  · intro γ p hp hC
    obtain ⟨hp₀, hp₁, hp₂⟩ := active p hp
    obtain ⟨_, hq, hr, hNear⟩ := hGeom p hp
    obtain ⟨hPQ, hPR⟩ := angularNearWeight_nonzero_edges hCut hδ hNear
    exact S.enlarged_on_three_nearSlots γ γ.property p.1 p.2 (-(p.1+p.2))
      hp₀ hp₁ hp₂ (subset_tsupport _ hC) hPQ.le hPR.le hq hr

end Burnett.A05
