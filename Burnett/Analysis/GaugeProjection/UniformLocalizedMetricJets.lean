import Burnett.Analysis.GaugeProjection.LocalizedVacuumSourceBound
import Mathlib.Analysis.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option maxHeartbeats 3300000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Filter Set
open scoped BigOperators Topology Matrix.Norms.Elementwise

private abbrev MetricMatrix := Matrix Index Index ℝ

private theorem continuousOn_metricInverse :
    ContinuousOn (fun A : MetricMatrix => A⁻¹) {A | A.det ≠ 0} := by
  intro A hA
  have h : ContinuousAt Ring.inverse A.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hA
  exact (continuousAt_matrix_inv A h).continuousWithinAt

/-- Local uniform convergence to a nondegenerate metric bounds the actual
inverses on the same compact chart set, including the finitely many early
metrics. -/
theorem exists_compact_uniform_metricInverse_bound
    (K : Set CoordinateSpace) (hK : IsCompact K)
    (g : ℕ → CoordinateSpace → MetricMatrix) (g₀ : CoordinateSpace → MetricMatrix)
    (hg : ∀ n, ContinuousOn (g n) K) (hg₀ : ContinuousOn g₀ K)
    (hND : ∀ n x, x ∈ K → (g n x).det ≠ 0) (hND₀ : ∀ x ∈ K, (g₀ x).det ≠ 0)
    (hConv : TendstoUniformlyOn g g₀ atTop K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖(g n x)⁻¹‖ ≤ C := by
  let U : Set MetricMatrix := {A | A.det ≠ 0}
  have ho : IsOpen U := isOpen_ne_fun continuous_id.matrix_det continuous_const
  have hMaps₀ : MapsTo g₀ K U := fun x hx => hND₀ x hx
  obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_metricInverse.comp hg₀ hMaps₀)
  let V : Set MetricMatrix := U ∩ (fun A : MetricMatrix => ‖A⁻¹‖) ⁻¹' Iio (max c 0 + 1)
  have hv : IsOpen V := continuousOn_metricInverse.norm.isOpen_inter_preimage ho isOpen_Iio
  have hSub : g₀ '' K ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hMaps₀ hx, ?_⟩
    exact (hc x hx).trans_lt (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)
  obtain ⟨ε, hε, hV⟩ := (hK.image_of_continuousOn hg₀).exists_thickening_subset_open hv hSub
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hConv ε hε)
  choose cₙ hcₙ using fun n =>
    hK.exists_bound_of_continuousOn
      (continuousOn_metricInverse.comp (hg n) (fun x hx => hND n x hx))
  let D := max c 0 + 1 + ∑ n ∈ Finset.range N, max (cₙ n) 0
  have hS : 0 ≤ ∑ n ∈ Finset.range N, max (cₙ n) 0 :=
    Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨D, by dsimp [D]; positivity, fun n x hx => ?_⟩
  by_cases hn : N ≤ n
  · have hxV : g n x ∈ V := hV (Metric.mem_thickening_iff.mpr
      ⟨g₀ x, mem_image_of_mem _ hx, (dist_comm _ _).trans_lt (hN n hn x hx)⟩)
    have hb : ‖(g n x)⁻¹‖ < max c 0 + 1 := hxV.2
    exact hb.le.trans (le_add_of_nonneg_right hS)
  · have hfin : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    exact (hcₙ n x hx).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (f := fun n => max (cₙ n) 0)
        (fun n _ => le_max_right (cₙ n) 0) hfin).trans
          (le_add_of_nonneg_left (by positivity))))

/-- Compact chart bounds on the metric values and their first derivatives
suffice for the jet data used by the exact projected source. -/
theorem exists_compact_localizedSourceJets_bound
    (K : Set CoordinateSpace)
    (g inv : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (M : ℝ) (hM : 0 ≤ M)
    (hDiff : ∀ n x, x ∈ K → DifferentiableComponentsAt (g n) x)
    (hDiffInv : ∀ n x, x ∈ K → DifferentiableComponentsAt (inv n) x)
    (hLeft : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, ∀ a b,
      (∑ k, inv n y a k * g n y k b) = if a = b then 1 else 0)
    (hRight : ∀ n x, x ∈ K → ∀ a b,
      (∑ k, g n x a k * inv n x k b) = if a = b then 1 else 0)
    (hA : ∀ n x, x ∈ K → ‖inv n x‖ ≤ M)
    (hH : ∀ n x, x ∈ K → ‖g n x - g₀ x‖ ≤ M)
    (hD : ∀ n x, x ∈ K → ‖coordinateJet (g n) x‖ ≤ M)
    (hD₀ : ∀ x ∈ K, ‖coordinateJet g₀ x‖ ≤ M)
    (hD₂ : ∀ x ∈ K, ‖coordinateSecondMetricJet g₀ x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖localizedSourceJets (inv n) (g n) g₀ x‖ ≤ C := by
  let B := 2 * M + 16 * M ^ 3
  refine ⟨B, by positivity, fun n x hx => ?_⟩
  have hMB : M ≤ B := by dsimp [B]; nlinarith [pow_nonneg hM 3]
  have hDI : ‖coordinateJet (inv n) x‖ ≤ 16 * M ^ 3 := by
    refine (norm_coordinateJet_inverse_le (g n) (inv n) x (hDiff n x hx) (hDiffInv n x hx)
      (hLeft n x hx) (hRight n x hx)).trans ?_
    calc
      _ ≤ 16 * M ^ 2 * M := by gcongr <;> first | exact hA n x hx | exact hD n x hx
      _ = _ := by ring
  have hDH : ‖coordinateJet (g n) x - coordinateJet g₀ x‖ ≤ 2 * M := by
    exact (norm_sub_le _ _).trans (by linarith [hD n x hx, hD₀ x hx])
  have hDB : ‖coordinateJet (inv n) x‖ ≤ B := hDI.trans (by dsimp [B]; linarith)
  have hDHB : ‖coordinateJet (g n) x - coordinateJet g₀ x‖ ≤ B :=
    hDH.trans (by dsimp [B]; nlinarith [pow_nonneg hM 3])
  simp only [localizedSourceJets, Prod.norm_def, max_le_iff]
  exact ⟨(hA n x hx).trans hMB, (hD n x hx).trans hMB, hDB,
    (hH n x hx).trans hMB, hDHB, (hD₂ x hx).trans hMB⟩

end Burnett.P01
