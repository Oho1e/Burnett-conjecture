import Burnett.Analysis.TransportWard.Weyl.WeylGradientLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalLocalizedWeylInputBounds
import Burnett.Analysis.TransportWard.Weyl.OriginalLocalizedWeylPrincipalLimit
import Burnett.Analysis.TransportWard.Weyl.CanonicalPoissonSymbolRegularity
import Burnett.Analysis.TransportWard.Weyl.CanonicalWeylOrderedKernel

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2300

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology BigOperators

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

private theorem toLp_const_smul (s : ℂ) (f : SchwartzMap E₀ ℂ) :
    (s • f).toLp 2 volume = s • f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul s f

/-- The original outer-cutoff field in its Euclidean orthonormal basis
meets the exact H¹ and L² hypotheses of the genuine residual pairings. -/
theorem exists_original_normalizedWeylPerturbation_bounds
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (i : I) :
    let F n := (symmetricMetricScale i : ℂ) • fixedWeylPerturbationSchwartz B g hB hg c χ hχ n i.val
    (∃ C : ℝ, ∀ n, Real.sqrt (schwartzH1Energy (F n)) ≤ C) ∧
      Tendsto (fun n => ‖(F n).toLp 2 volume‖) atTop (𝓝 0) := by
  intro F
  let U n := fixedWeylPerturbationSchwartz B g hB hg c χ hχ n i.val
  let a : ℂ := symmetricMetricScale i
  obtain ⟨hZero,_,hBound⟩ := exists_original_fixedWeylPerturbationSchwartz_bounds
    r B g hB hg hn hconv hb c χ hχ
  obtain ⟨M,_,hU,hD⟩ := hBound i.val
  let L := ‖a‖ * M
  have hF (n : ℕ) : ‖(F n).toLp 2 volume‖ ≤ L := by
    change ‖(a • U n).toLp 2 volume‖ ≤ L
    rw [toLp_const_smul,norm_smul]
    exact mul_le_mul_of_nonneg_left (hU n) (norm_nonneg _)
  have hDF (n : ℕ) (j : Fin 4) :
      ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) (F n)).toLp 2 volume‖ ≤ L := by
    change ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) (a • U n)).toLp 2 volume‖ ≤ L
    rw [map_smul,toLp_const_smul,norm_smul]
    exact mul_le_mul_of_nonneg_left (hD j n) (norm_nonneg _)
  have hEnergy (n : ℕ) : schwartzH1Energy (F n) ≤ L^2 + ∑ _ : Fin 4, L^2 := by
    unfold schwartzH1Energy
    refine add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hF n) 2) ?_
    exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hDF n j) 2)
  refine ⟨⟨Real.sqrt (L^2 + ∑ _ : Fin 4, L^2),fun n => Real.sqrt_le_sqrt (hEnergy n)⟩,?_⟩
  change Tendsto (fun n => ‖(a • U n).toLp 2 volume‖) atTop (𝓝 0)
  simp only [toLp_const_smul,norm_smul]
  simpa only [norm_zero,mul_zero] using (hZero i.val).norm.const_mul ‖a‖

end Burnett.V03.Palatini
