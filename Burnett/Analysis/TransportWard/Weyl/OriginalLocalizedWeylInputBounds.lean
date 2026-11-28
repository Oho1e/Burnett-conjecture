import Burnett.Analysis.TransportWard.Weyl.WeylCovarianceContraction
import Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput
import Burnett.Analysis.TransportWard.Weyl.CanonicalWeylHomogeneousTail
import Burnett.Analysis.TransportWard.Weyl.OriginalChartCovarianceKernel
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2200

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldBilinear
open ManifoldMetric ManifoldMetricSequence MaximalChart Burnett.Fourier
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold Topology BigOperators

local notation "E₀" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M]

private theorem fixedWeylPerturbationSchwartz_tendsto_L2_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hconv : LocallyUniformlyConverges r g B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (k : Pair) :
    Tendsto (fun n => (fixedWeylPerturbationSchwartz B g hB hg c χ hχ n k).toLp 2 volume) atTop (𝓝 0) := by
  have hχLp : MemLp (χ : E₀ → ℝ) 2 volume :=
    (test_smooth χ).continuous.memLp_of_hasCompactSupport (test_compactSupport χ)
  refine Burnett.P01.tendsto_weighted_localizationError_L2_zero (tsupport (χ : E₀ → ℝ))
    (χ : E₀ → ℝ) hχLp (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    (fun n => fixedComponent B g c n k)
    (fixedComponent_localUniform r B g hconv c k _ (test_compactSupport χ) hχ) _ ?_
  intro n
  exact (fixedWeylPerturbationSchwartz B g hB hg c χ hχ n k).coeFn_toLp 2 volume

variable [MeasurableSpace M] [BorelSpace M]

/-- The actual original Schwartz cutoff components are uniformly bounded
with their four coordinate derivatives and converge strongly to zero in L². -/
theorem exists_original_fixedWeylPerturbationSchwartz_bounds
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) :
    let F := fixedWeylPerturbationSchwartz B g hB hg c χ hχ
    let U := fixedGradientSchwartz B g hB hg c χ hχ
    (∀ k : Pair, Tendsto (fun n => (F n k).toLp 2 volume) atTop (𝓝 0)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n (i : JetSlot), ‖(U n i).toLp 2 volume‖ ≤ C) ∧
    ∀ k : Pair, ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, ‖(F n k).toLp 2 volume‖ ≤ M) ∧
      ∀ j : Fin 4, ∀ n, ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) (F n k)).toLp 2 volume‖ ≤ M := by
  intro F U
  let η := inverseHalfDensityWindow B hB hn c χ hχ
  let hη := (inverseHalfDensityWindow_tsupport B hB hn c χ hχ).trans hχ
  obtain ⟨C,hC,hBound,_⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c η hη
  have hRaw (n : ℕ) (i : JetSlot) : ‖(U n i).toLp 2 volume‖ ≤ C := by
    change ‖(fixedGradientSchwartz B g hB hg c χ hχ n i).toLp 2 volume‖ ≤ C
    rw [← fixedVolumeGradientSchwartz_inverseHalfDensityWindow B g hB hg hn c χ hχ n i]
    exact hBound n i
  have hF0 (k : Pair) : Tendsto (fun n => (F n k).toLp 2 volume) atTop (𝓝 0) :=
    fixedWeylPerturbationSchwartz_tendsto_L2_zero r B g hB hg hconv c χ hχ k
  refine ⟨hF0,⟨C,hC,hRaw⟩,fun k => ?_⟩
  let V (j : Fin 4) (n : ℕ) := (SchwartzMap.pderivCLM ℂ (coordinateDirection j) (F n k)).toLp 2 volume
  let Eps (j : Fin 4) (n : ℕ) := V j n - (U n (j,k)).toLp 2 volume
  have he (j : Fin 4) : Tendsto (Eps j) atTop (𝓝 0) :=
    tendsto_fixedWeylPerturbationSchwartz_partial_sub_rawGradient r B g hB hg hconv c χ hχ (j,k)
  obtain ⟨M₀,hM₀⟩ := (Metric.isBounded_range_of_tendsto _ (hF0 k)).exists_norm_le
  choose D hD using fun j => (Metric.isBounded_range_of_tendsto _ (he j)).exists_norm_le
  let m := C + ∑ j : Fin 4, max 0 (D j)
  let M := max M₀ m
  have hm : 0 ≤ m := add_nonneg hC (Finset.sum_nonneg (fun j _ => le_max_left _ _))
  refine ⟨M,hm.trans (le_max_right _ _),fun n => (hM₀ _ ⟨n,rfl⟩).trans (le_max_left _ _),
    fun j n => ?_⟩
  change ‖V j n‖ ≤ M
  have hDj : D j ≤ ∑ k : Fin 4, max 0 (D k) :=
    (le_max_right _ _).trans
      (Finset.single_le_sum (fun k _ => le_max_left 0 (D k)) (Finset.mem_univ j))
  calc
    _ = ‖Eps j n + (U n (j,k)).toLp 2 volume‖ := by dsimp only [Eps]; rw [sub_add_cancel]
    _ ≤ ‖Eps j n‖ + ‖(U n (j,k)).toLp 2 volume‖ := norm_add_le _ _
    _ ≤ (∑ k : Fin 4, max 0 (D k)) + C :=
      add_le_add ((hD j _ ⟨n,rfl⟩).trans hDj) (hRaw n (j,k))
    _ ≤ M := by rw [add_comm]; exact le_max_right _ _

end Burnett.V03
