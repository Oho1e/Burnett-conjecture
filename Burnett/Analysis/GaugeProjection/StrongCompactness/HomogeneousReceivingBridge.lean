import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingCutoff
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingProjectionTrace
import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectionInfraredDifference

/-! The chart's actual homogeneous strong-compactness energy and its covariant defect. -/
set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 5500000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.Analysis.HminusWeightedDual (complexTest)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators ContDiff Manifold Matrix Topology

open private fixedHalfDensity_pos from Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingCutoff

private theorem tendsto_sum_sq_norm_zero_iff {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    (v : ℕ → ι → X) :
    Tendsto (fun n => ∑ i : ι, ‖v n i‖^2) atTop (𝓝 0) ↔
      ∀ i, Tendsto (fun n => v n i) atTop (𝓝 0) := by
  classical
  constructor
  · intro h i
    have hs : Tendsto (fun n => ‖v n i‖^2) atTop (𝓝 (0 : ℝ)) :=
      squeeze_zero (fun _ => sq_nonneg _) (fun n =>
        Finset.single_le_sum (fun j _ => sq_nonneg ‖v n j‖) (Finset.mem_univ i)) h
    have hRoot := (Real.continuous_sqrt.tendsto 0).comp hs
    change Tendsto (fun n => Real.sqrt (‖v n i‖^2)) atTop (𝓝 (Real.sqrt 0)) at hRoot
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hRoot
  · intro h
    have hs (i : ι) : Tendsto (fun n => ‖v n i‖^2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using (h i).norm.pow 2
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum (Finset.univ : Finset ι) (fun i _ => hs i)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

/-- The true local cutoff fluctuation extended by zero in the receiving chart. -/
def receivingCutoffFluctuation (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (n : ℕ) : ProjectionSchwartzMatrix :=
  fun i j => complexTest ⟨fun x => (χ : E → ℝ) x * fixedPerturbation B (g n) c x i j,
    ⟨contDiff_test_mul_local c.chart.open_target (test_smooth χ) hχ
      (fixedComponent_smooth B g hB hg c n (i, j)), (test_compactSupport χ).mul_right⟩⟩

/-- The sum of all squared norm components of the homogeneous projected
gradient of the original cutoff fluctuation on the whole coordinate space. -/
def receivingStrongProjectionEnergy (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (n : ℕ) : ℝ :=
  ∑ d : Index, ∑ k : OrderedPair,
    ‖homogeneousProjectedCoordinateDerivative (receivingCutoffFluctuation B g hB hg c χ hχ n) d k‖^2

/-- On the actual subsequence, the homogeneous strong energy detects the same
projected covariance as the covariant half-density pairings. -/
theorem tendsto_receivingStrongProjectionEnergy_zero_iff
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K) :
    let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    Tendsto (fun n => receivingStrongProjectionEnergy B g hB hg c χ hχc (σ n)) atTop (𝓝 0) ↔
      ∀ᵐ p ∂τ, (χ : E → ℝ) (fixedChartPhase c p.val).1 ≠ 0 →
        let P := principalGaugeProjectionMatrix (WithLp.toLp 2 (atlasChartUnitCovector c p))
        P * atlasAmplitudeMatrix c A.density p * Pᴴ = 0 := by
  intro hχc τ
  let η := inverseHalfDensityCutoff B hB hn c χ hχc
  have hηs : tsupport (η : E → ℝ) ⊆ tsupport (χ : E → ℝ) :=
    inverseHalfDensityCutoff_tsupport B hB hn c χ hχc
  have hη : tsupport (η : E → ℝ) ⊆ c.chart '' K := hηs.trans hχ
  have hηc : tsupport (η : E → ℝ) ⊆ c.chart.target := hηs.trans hχc
  let u (d : Index) (n : ℕ) : ProjectionSchwartzMatrix := fun i j =>
    fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc (σ n) (d, i, j)
  let z := receivingCutoffFluctuation B g hB hg c χ hχc
  obtain ⟨z', hz', hZ', hErr'⟩ := exists_receiving_cutoff_metric_and_derivative_error r B g hB hg hconv c χ hχc
  have hzz : z' = z := by
    funext n i j
    ext x
    exact hz' n x i j
  subst z'
  have hχeq : fixedWeightedCutoff B hB hn c η hηc = χ :=
    fixedWeightedCutoff_inverseHalfDensityCutoff B hB hn c χ hχc
  have hFixed (n : ℕ) (d i j : Index) : fixedVolumeGradientSchwartz B g hB hg hn c η hηc n (d, i, j) =
      fixedGradientSchwartz B g hB hg c χ hχc n (d, i, j) := by
    ext x
    rw [fixedVolumeGradientSchwartz_apply, fixedGradientSchwartz_apply]
    have he := congrFun (congrArg Subtype.val hχeq) x
    change (η : E → ℝ) x * fixedHalfDensity B c x = (χ : E → ℝ) x at he
    rw [he]
  let q (d : Index) (n : ℕ) : ProjectionSchwartzMatrix := fun i j => coordinateDerivative d (z (σ n) i j)
  have hInputs (d i j : Index) : Tendsto (fun n => (q d n i j).toLp 2 volume - (u d n i j).toLp 2 volume)
      atTop (𝓝 0) := by
    have hCov := fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c η hηc (d, i, j)
    simp only [hFixed] at hCov
    have h := ((hErr' d i j).comp hσ.tendsto_atTop).sub (hCov.comp hσ.tendsto_atTop)
    refine Tendsto.congr (fun n => ?_) (by simpa only [sub_zero] using h)
    dsimp only [Function.comp_apply, q, u]
    abel
  have hProj (d : Index) (k : OrderedPair) : Tendsto (fun n =>
        (projectionFullSchwartz (q d n) k.1 k.2).toLp 2 volume -
        (projectionFullSchwartz (u d n) k.1 k.2).toLp 2 volume) atTop (𝓝 0) := by
    have hPi : Tendsto (fun n => projectionMatrixToL2 (q d n) - projectionMatrixToL2 (u d n)) atTop (𝓝 0) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      exact hInputs d i j
    let F := (projectionL2Entry k.1 k.2).comp projectionFullL2
    have h := (F.continuous.tendsto 0).comp hPi
    change Tendsto (fun n => F (projectionMatrixToL2 (q d n) - projectionMatrixToL2 (u d n))) atTop (𝓝 (F 0)) at h
    rw [map_zero] at h
    simp only [map_sub, F, ContinuousLinearMap.comp_apply, projectionFullL2_eq_schwartz] at h
    exact h
  let V (n : ℕ) (a : Index × OrderedPair) := homogeneousProjectedCoordinateDerivative (z (σ n)) a.1 a.2
  let W (n : ℕ) (a : Index × OrderedPair) := (projectionFullSchwartz (u a.1 n) a.2.1 a.2.2).toLp 2 volume
  have hClose (a : Index × OrderedPair) : Tendsto (fun n => V n a - W n a) atTop (𝓝 0) := by
    have hIR := (homogeneousProjectedCoordinateDerivative_sub_regularized_tendsto_zero z hZ' a.1 a.2).comp hσ.tendsto_atTop
    have h := hIR.add (hProj a.1 a.2)
    simp only [zero_add] at h
    refine h.congr (fun n => ?_)
    have he := congrFun (congrFun (projectionFullSchwartz_coordinateDerivative a.1 (z (σ n))) a.2.1) a.2.2
    change projectionFullSchwartz (q a.1 n) a.2.1 a.2.2 =
      coordinateDerivative a.1 (projectionFullSchwartz (z (σ n)) a.2.1 a.2.2) at he
    dsimp only [Function.comp_apply, V, W]
    rw [he]
    abel
  have hSwap : (∀ a, Tendsto (fun n => V n a) atTop (𝓝 0)) ↔
      (∀ a, Tendsto (fun n => W n a) atTop (𝓝 0)) := by
    constructor
    · intro h a
      simpa only [sub_sub_cancel, sub_zero] using (h a).sub (hClose a)
    · intro h a
      simpa only [sub_add_cancel, zero_add] using (hClose a).add (h a)
  have hTrace := tendsto_receiving_projection_energy_zero_iff r B g hB hg hn σ A hA hPair c K hK hKc η hη
  change (Tendsto (fun n => ∑ d : Index, ∑ k : OrderedPair, ‖W n (d, k)‖^2) atTop (𝓝 0)) ↔ _ at hTrace
  have hSupport (x : E) (hx : x ∈ c.chart.target) : (η : E → ℝ) x ≠ 0 ↔ (χ : E → ℝ) x ≠ 0 := by
    have he := congrFun (congrArg Subtype.val hχeq) x
    change (η : E → ℝ) x * fixedHalfDensity B c x = (χ : E → ℝ) x at he
    rw [← he]
    simp [(fixedHalfDensity_pos B hn c hx).ne']
  have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hCut : ∀ᵐ p ∂τ, (η : E → ℝ) (fixedChartPhase c p.val).1 ≠ 0 ↔
      (χ : E → ℝ) (fixedChartPhase c p.val).1 ≠ 0 := by
    filter_upwards [ae_restrict_mem (μ := A.control) hWin] with p hp
    have hc := hKc hp
    apply hSupport
    rw [FixedCotangentChart.fixedChartPhase_of_mem c p.val hc]
    exact c.chart.mapsTo hc
  change (Tendsto (fun n => ∑ d : Index, ∑ k : OrderedPair, ‖V n (d, k)‖^2) atTop (𝓝 0)) ↔ _
  have hVsum (n : ℕ) : (∑ d : Index, ∑ k : OrderedPair, ‖V n (d, k)‖^2) =
      ∑ a : Index × OrderedPair, ‖V n a‖^2 := (Fintype.sum_prod_type (fun a => ‖V n a‖^2)).symm
  have hWsum (n : ℕ) : (∑ d : Index, ∑ k : OrderedPair, ‖W n (d, k)‖^2) =
      ∑ a : Index × OrderedPair, ‖W n a‖^2 := (Fintype.sum_prod_type (fun a => ‖W n a‖^2)).symm
  simp only [hWsum] at hTrace
  simp only [hVsum]
  rw [tendsto_sum_sq_norm_zero_iff V, hSwap, ← tendsto_sum_sq_norm_zero_iff W, hTrace]
  constructor <;> intro h <;> filter_upwards [h, hCut] with p hp he
  · exact fun hnz => hp (he.mpr hnz)
  · exact fun hnz => hp (he.mp hnz)

end Burnett.P01
