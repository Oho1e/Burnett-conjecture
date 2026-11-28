import Burnett.Analysis.TransportWard.Weyl.NormalizedTestedVacuum
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped ContDiff Manifold Topology BigOperators Matrix.Norms.Elementwise

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

private theorem opNorm_le_of_axis_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : E₀ →L[ℝ] V) (C : ℝ) (hC : 0 ≤ C) (h : ∀ j, ‖L (coordinateBasis j)‖ ≤ C) :
    ‖L‖ ≤ 4 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hBasis (j : Fin 4) : coordinateBasis j = EuclideanSpace.single j (1 : ℝ) :=
    EuclideanSpace.basisFun_apply _ _ j
  have he : (∑ j, v j • coordinateBasis j) = v := by
    simpa only [hBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  calc
    ‖L v‖ = ‖∑ j, v j • L (coordinateBasis j)‖ := by
      exact congrArg norm (by simpa only [map_sum, map_smul] using (congrArg L he).symm)
    _ ≤ ∑ j, ‖v j • L (coordinateBasis j)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 4, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v j) (h j) (norm_nonneg _) (norm_nonneg _)
    _ = (4 * C) * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Uniform first-jet control for the exact orthonormalized perturbation and
its reassembled lower metric tensor on a fixed compact chart window. -/
theorem exists_originalNormalizedChartPerturbation_derivative_bounds
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : M) {K : Set E₀} (hK : IsCompact K) (hKU : K ⊆ (chartAt E₀ c).target) :
    let h (n : ℕ) := normalizedChartPerturbation B (g n) c
    let H (n : ℕ) := assembleMetricComponents orthonormalMetricDirection ∘ h n
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ n x, x ∈ K → ∀ s, ‖coordinateMetricFirstJet (h n) x s‖ ≤ C) ∧
      (∀ n x, x ∈ K → ‖fderiv ℝ (H n) x‖ ≤ D) := by
  intro h H
  let U := (chartAt E₀ c).target
  let c₀ := AtlasChart.atPoint c
  obtain ⟨A, hA, hRaw⟩ := Burnett.Microlocal.AtlasVolumeGradient.fixedJet_uniform_bound_on_compact
    r B g hB hg hnB hconv hb c₀ hK hKU
  let smax : ℝ := ∑ i : I, ‖symmetricMetricScale i‖
  have hS₀ : 0 ≤ smax := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hS (i : I) : ‖symmetricMetricScale i‖ ≤ smax :=
    Finset.single_le_sum (fun j _ => norm_nonneg (symmetricMetricScale j)) (Finset.mem_univ i)
  have hD (n : ℕ) (x : E₀) (hx : x ∈ U) : DifferentiableAt ℝ (h n) x :=
    (((contDiffOn_normalizedChartMetric (g n) (hg n) c).sub (contDiffOn_normalizedChartMetric B hB c)).contDiffAt
      ((chartAt E₀ c).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hJ (n : ℕ) (x : E₀) (hx : x ∈ K) (s : ActionSlot I) :
      ‖coordinateMetricFirstJet (h n) x s‖ ≤ smax * A := by
    let B₀ (y : E₀) := fixedComponent B g c₀ n s.2.val y
    let E₁ : ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ (symmetricMetricScale s.2)
    let Ei : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj s.2
    have hNear : (fun y => Ei (h n y)) =ᶠ[𝓝 x] E₁ ∘ B₀ := by
      filter_upwards [(chartAt E₀ c).open_target.mem_nhds (hKU hx)] with y hy
      exact normalizedChartPerturbation_eq_fixedComponent B g c n y hy s.2
    have hRawD : DifferentiableAt ℝ B₀ x :=
      ((fixedComponent_smooth B g hB hg c₀ n s.2.val).contDiffAt
        (c₀.chart.open_target.mem_nhds (hKU hx))).differentiableAt (by simp)
    have hEi := (Ei.hasFDerivAt.comp x (hD n x (hKU hx)).hasFDerivAt).fderiv
    have hE₁ := (E₁.hasFDerivAt.comp x hRawD.hasFDerivAt).fderiv
    have hJval : coordinateMetricFirstJet (h n) x s = symmetricMetricScale s.2 *
        coordinateJet (fixedPerturbation B (g n) c₀) x s.1 s.2.val.1 s.2.val.2 := by
      change (Ei.comp (fderiv ℝ (h n) x)) (coordinateBasis s.1) = _
      change (⇑Ei ∘ h n) =ᶠ[𝓝 x] (⇑E₁ ∘ B₀) at hNear
      rw [← hEi, hNear.fderiv_eq, hE₁]
      rw [show coordinateBasis s.1 = EuclideanSpace.single s.1 (1 : ℝ) from
        EuclideanSpace.basisFun_apply _ _ s.1]
      rfl
    have hEntry : ‖coordinateJet (fixedPerturbation B (g n) c₀) x s.1 s.2.val.1 s.2.val.2‖ ≤ A :=
      ((norm_le_pi_norm _ s.2.val.2).trans ((norm_le_pi_norm _ s.2.val.1).trans
        (norm_le_pi_norm _ s.1))).trans (hRaw n x hx)
    rw [hJval, norm_mul]
    exact mul_le_mul (hS s.2) hEntry (norm_nonneg _) hS₀
  let S := assembleMetricComponents orthonormalMetricDirection
  refine ⟨smax * A, ‖S‖ * (4 * (smax * A)), mul_nonneg hS₀ hA, by positivity, hJ, ?_⟩
  intro n x hx
  have hJAll : ∀ j, ‖fderiv ℝ (h n) x (coordinateBasis j)‖ ≤ smax * A := by
    intro j
    exact (pi_norm_le_iff_of_nonneg (mul_nonneg hS₀ hA)).mpr (fun i => hJ n x hx (j,i))
  have hHH := (S.hasFDerivAt.comp x (hD n x (hKU hx)).hasFDerivAt).fderiv
  change ‖fderiv ℝ (S ∘ h n) x‖ ≤ _
  rw [hHH]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
    (opNorm_le_of_axis_bounds _ _ (mul_nonneg hS₀ hA) hJAll) (norm_nonneg _))

end Burnett.V03.Palatini
