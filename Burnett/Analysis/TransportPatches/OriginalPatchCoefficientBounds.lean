import Burnett.Analysis.TransportPatches.CorrectionCoefficientCutoff
import Burnett.Analysis.TransportPatches.ScaledCubicPartition

/-! The projected corrections use the actual inverse of the original
metric on each patch. Compactness supplies constants uniform in the
original sequence, patch center and cutoff scale. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.C03

open Filter Set Metric Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference InverseField InversePerturbation SmoothMetricConnection
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ContDiff Topology

/-- Actual C03 cutoff inverse bounds. The frozen constant is the inverse
metric at the center and the only sequence error is the original uniform
metric difference on the common compact chart window. -/
theorem eventually_original_patchCoefficient_bounds
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g₀ : CoordinateSpace → Tensor2) (g : ℕ → CoordinateSpace → Tensor2)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hND₀ : ∀ x ∈ U, Matrix.det (g₀ x) ≠ 0)
    (hND : ∀ n x, x ∈ U → Matrix.det (g n x) ≠ 0)
    (hConv : TendstoUniformlyOn g g₀ atTop K)
    (D Cχ : ℝ) (hD : 0 ≤ D) (hCχ : 0 ≤ Cχ)
    (hJet : ∀ n x, x ∈ K → ‖coordinateJet (g n) x‖ ≤ D)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hError : ∀ n x, x ∈ K → ‖g n x - g₀ x‖ ≤ e n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (ℓ : ℝ), 0 < ℓ → ∀ a : LatticeIndex,
      let c := patchCenter ℓ a
      let Kpatch := closedBall c (6 * ℓ)
      Kpatch ⊆ K → ∀ χ : CoordinateSpace → ℝ, Differentiable ℝ χ →
      tsupport χ ⊆ Kpatch →
      (∀ x ∈ Kpatch, ‖χ x‖ ≤ 1 ∧ ‖fderiv ℝ χ x‖ ≤ Cχ * ℓ⁻¹) →
      let d := correctionCoefficientPart χ (matrixInverse ∘ g n) (matrixInverse (g₀ c))
      ∀ x, ‖d x‖ ≤ C * (ℓ + e n) ∧ ‖coordinateJet d x‖ ≤ C * (1 + e n / ℓ) := by
  obtain ⟨B, hB, _, hInv⟩ := eventually_original_inverseJet_bounds
    U K hU hK hKU g₀ g hg₀ hg hND₀ hND hConv D hJet
  let A₀ := matrixInverse ∘ g₀
  have hA₀ : ContDiffOn ℝ ∞ A₀ U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact contDiffOn_matrixInverse g₀ U hg₀ hND₀ i j
  have hC := hA₀.continuousOn_fderiv_of_isOpen hU (by simp)
  obtain ⟨L, hL, hLBound⟩ := (hK.image_of_continuousOn (hC.mono hKU)).isBounded.exists_pos_norm_le
  let J := 16 * (2 * B) ^ 2 * D
  let F := 6 * L + 32 * B ^ 2
  let C := F + J + F * Cχ
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC₁ : F ≤ C := by dsimp [C]; linarith [mul_nonneg hF hCχ]
  have hC₂ : J + F * Cχ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hF.trans hC₁, ?_⟩
  filter_upwards [hInv] with n hn
  intro ℓ hℓ a
  dsimp only
  let c := patchCenter ℓ a
  let S := closedBall c (6 * ℓ)
  intro hSK χ hχ hSupp hCut
  let A := matrixInverse ∘ g n
  let G := F * (ℓ + e n)
  have hG : 0 ≤ G := mul_nonneg hF (add_nonneg hℓ.le (he n))
  have hADiff (x : CoordinateSpace) (hx : x ∈ S) : DifferentiableComponentsAt A x := by
    intro i j
    exact ((contDiffOn_matrixInverse (g n) U (hg n) (hND n) i j).contDiffAt
      (hU.mem_nhds (hKU (hSK hx)))).differentiableAt (by simp)
  have hc : c ∈ S := mem_closedBall_self (by positivity)
  have hABound (x : CoordinateSpace) (hx : x ∈ S) :
      ‖A x - A₀ c‖ ≤ G ∧ ‖coordinateJet A x‖ ≤ J := by
    have hVar := (convex_closedBall c (6 * ℓ)).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hA₀.contDiffAt (hU.mem_nhds (hKU (hSK hy)))).differentiableAt (by simp))
      (fun y hy => hLBound _ (mem_image_of_mem _ (hSK hy))) hc hx
    have hRadius : ‖x - c‖ ≤ 6 * ℓ := by simpa only [S, mem_closedBall, dist_eq_norm] using hx
    refine ⟨?_, (hn x (hSK hx)).2⟩
    calc
      _ ≤ ‖A x - A₀ x‖ + ‖A₀ x - A₀ c‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (A x - A₀ x) (A₀ x - A₀ c)
      _ ≤ 32 * B ^ 2 * e n + L * (6 * ℓ) :=
        add_le_add ((hn x (hSK hx)).1.trans (mul_le_mul_of_nonneg_left (hError n x (hSK hx)) (by positivity)))
          (hVar.trans (mul_le_mul_of_nonneg_left hRadius hL.le))
      _ ≤ G := by
        dsimp [G, F]
        nlinarith [mul_nonneg (show 0 ≤ 32 * B ^ 2 by positivity) hℓ.le, mul_nonneg hL.le (he n)]
  intro x
  have hBounds := correctionCoefficientPart_norm_and_jet_le S χ hχ hSupp A (A₀ c) G J
    (Cχ * ℓ⁻¹) hG hJ (mul_nonneg hCχ (inv_nonneg.mpr hℓ.le)) hADiff hCut hABound x
  have hEq : G * (Cχ * ℓ⁻¹) = F * Cχ * (1 + e n / ℓ) := by
    dsimp [G]
    field_simp [hℓ.ne']
  refine ⟨hBounds.1.trans (mul_le_mul_of_nonneg_right hC₁ (add_nonneg hℓ.le (he n))), ?_⟩
  refine hBounds.2.trans ?_
  rw [hEq]
  have hNonneg : 0 ≤ e n / ℓ := div_nonneg (he n) hℓ.le
  calc
    _ ≤ (J + F * Cχ) * (1 + e n / ℓ) := by nlinarith [mul_nonneg hJ hNonneg]
    _ ≤ _ := mul_le_mul_of_nonneg_right hC₂ (by linarith)

end Burnett.C03
