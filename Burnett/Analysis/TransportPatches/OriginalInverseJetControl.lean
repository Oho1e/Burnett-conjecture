import Burnett.Analysis.GaugeProjection.LocalizedVacuumSourceBound
import Burnett.Geometry.InverseField
import Burnett.Geometry.SmoothMetricConnection

/-! Quantitative estimates for the actual inverse metric on the common
compact chart window used by the two C03 corrections. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.C03

open Filter Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference InverseField InversePerturbation SmoothMetricConnection
open Burnett.P01 (norm_coordinateJet_inverse_le)
open scoped ContDiff Topology BigOperators

/-- The original metric error controls its true inverse error. The
original first-derivative bound controls the true first inverse jet on
the same compact set. Both use only original sequence data. -/
theorem eventually_original_inverseJet_bounds
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g₀ : CoordinateSpace → Tensor2) (g : ℕ → CoordinateSpace → Tensor2)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hND₀ : ∀ x ∈ U, Matrix.det (g₀ x) ≠ 0)
    (hND : ∀ n x, x ∈ U → Matrix.det (g n x) ≠ 0)
    (hConv : TendstoUniformlyOn g g₀ atTop K)
    (D : ℝ) (hJet : ∀ n x, x ∈ K → ‖coordinateJet (g n) x‖ ≤ D) :
    ∃ B : ℝ, 0 < B ∧
      (∀ x ∈ K, ‖matrixInverse (g₀ x)‖ ≤ B) ∧
      ∀ᶠ n in atTop, ∀ x ∈ K,
        ‖matrixInverse (g n x) - matrixInverse (g₀ x)‖ ≤
          32 * B ^ 2 * ‖g n x - g₀ x‖ ∧
        ‖coordinateJet (matrixInverse ∘ g n) x‖ ≤ 16 * (2 * B) ^ 2 * D := by
  have hC : ContinuousOn g₀ K :=
    (continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (hg₀ i j).continuousOn).mono hKU
  obtain ⟨B, hB, hInv₀⟩ := exists_pos_bound_matrixInverse g₀ K hK hC (fun x hx => hND₀ x (hKU hx))
  refine ⟨B, hB, hInv₀, ?_⟩
  filter_upwards [eventually_matrixInverse_estimates atTop g₀ g K
    (fun x hx => hND₀ x (hKU hx)) (fun n x hx => hND n x (hKU hx)) hB hInv₀ hConv] with n hn
  intro x hx
  let inv := matrixInverse ∘ g n
  have hxU := hU.mem_nhds (hKU hx)
  have hLeft : ∀ᶠ y in 𝓝 x, ∀ a b,
      (∑ k, inv y a k * g n y k b) = if a = b then 1 else 0 := by
    filter_upwards [hxU] with y hy a b
    exact congrFun (congrFun (matrixInverse_compose (g n y) (hND n y hy)) a) b
  have hRight : ∀ a b, (∑ k, g n x a k * inv x k b) = if a = b then 1 else 0 := by
    intro a b
    exact congrFun (congrFun (compose_matrixInverse (g n x) (hND n x (hKU hx))) a) b
  refine ⟨(hn x hx).2, ?_⟩
  have hBound := norm_coordinateJet_inverse_le (g n) inv x
    (fun i j => ((hg n i j).contDiffAt hxU).differentiableAt (by simp))
    (fun i j => ((contDiffOn_matrixInverse (g n) U (hg n) (hND n) i j).contDiffAt hxU)
      |>.differentiableAt (by simp)) hLeft hRight
  exact hBound.trans (by gcongr; exact (hn x hx).1; exact hJet n x hx)

/-- The squared cutoff loss used for the commutator and divergence
drift in the same source budget. -/
theorem cutoff_square_le_sourceBudget (ℓ e : ℝ) (hℓ : 0 < ℓ) (he : 0 ≤ e) (hE : e ≤ 1) :
    (1 + e / ℓ)^2 ≤ 2 * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e) := by
  have hFirst : e / ℓ ≤ ℓ⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hE hℓ.le
  have hSecond : e ^ 2 / ℓ ^ 2 ≤ (ℓ ^ 2)⁻¹ * e := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg he (sub_nonneg.mpr hE)])
      (sq_nonneg ℓ)
  rw [add_sq, one_pow, div_pow]
  have hPos : 0 ≤ (ℓ ^ 2)⁻¹ * e := mul_nonneg (inv_nonneg.mpr (sq_nonneg ℓ)) he
  linarith

end Burnett.C03
