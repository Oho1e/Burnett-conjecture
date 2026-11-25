import Burnett.Analysis.BaseMarginal.IntrinsicBaseEnergy
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Identify the actual projected measure using scalar compact tests. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 3800000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Function Set MeasureTheory Filter Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open scoped ContDiff Manifold Topology ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

private theorem measure_eq_of_smooth_compact_tests (μ ν : Measure M)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (htest : ∀ φ : M → ℝ, ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ →
      (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  have oneWay (m n : Measure M) [IsLocallyFiniteMeasure m] [IsLocallyFiniteMeasure n]
      (hTests : ∀ φ : M → ℝ, ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ →
        (∫ x, φ x ∂m) = ∫ x, φ x ∂n) (K : Set M) (hK : IsCompact K) : m K ≤ n K := by
    apply le_of_forall_gt
    intro a ha
    obtain ⟨U, hKU, hU, hMassU⟩ := K.exists_isOpen_lt_of_lt a ha
    obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
    have hDis : Disjoint (interior L)ᶜ K := disjoint_left.mpr (fun _ hx hK' => hx (hKL hK'))
    obtain ⟨φ, h0, h1, h01⟩ := exists_smooth_zero_one_of_isClosed Model isOpen_interior.isClosed_compl hK.isClosed hDis
    have hsL : support φ ⊆ L := fun x hx => interior_subset (by
      by_contra hNot
      exact hx (h0 hNot))
    have hc : HasCompactSupport (φ : M → ℝ) :=
      hL.of_isClosed_subset isClosed_closure (closure_minimal hsL hL.isClosed)
    have hIm : Integrable (K.indicator (fun _ : M => (1 : ℝ))) m :=
      (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
    have hIn : Integrable (U.indicator (fun _ : M => (1 : ℝ))) n :=
      (integrableOn_const (hMassU.trans_le le_top).ne).integrable_indicator hU.measurableSet
    have hLeft : m.real K ≤ ∫ x, φ x ∂m := by
      calc
        _ = ∫ x, K.indicator (fun _ : M => (1 : ℝ)) x ∂m := by rw [integral_indicator hK.measurableSet]; simp
        _ ≤ _ := integral_mono hIm (φ.contMDiff.continuous.integrable_of_hasCompactSupport hc) (fun x => by
          by_cases hx : x ∈ K
          · simp only [indicator_of_mem hx, h1 hx, Pi.one_apply, le_refl]
          · simpa only [indicator_of_notMem hx] using (h01 x).1)
    have hRight : (∫ x, φ x ∂n) ≤ n.real U := by
      calc
        _ ≤ ∫ x, U.indicator (fun _ : M => (1 : ℝ)) x ∂n :=
          integral_mono (φ.contMDiff.continuous.integrable_of_hasCompactSupport hc) hIn (fun x => by
            by_cases hx : x ∈ U
            · simpa only [indicator_of_mem hx] using (h01 x).2
            · have hφx : φ x = 0 := notMem_support.mp (fun hx' => hx (hLU (hsL hx')))
              simp only [indicator_of_notMem hx, hφx, le_refl])
        _ = _ := by rw [integral_indicator hU.measurableSet]; simp
    have hLe : m K ≤ n U := (ENNReal.toReal_le_toReal hK.measure_lt_top.ne (hMassU.trans_le le_top).ne).mp
      (hLeft.trans ((hTests φ φ.contMDiff hc).le.trans hRight))
    exact hLe.trans_lt hMassU
  have hK (K : Set M) (hK : IsCompact K) : μ K = ν K := le_antisymm
    (oneWay μ ν htest K hK) (oneWay ν μ (fun φ hs hc => (htest φ hs hc).symm) K hK)
  apply Measure.ext
  intro U hU
  rw [hU.measure_eq_iSup_isCompact μ, hU.measure_eq_iSup_isCompact ν]
  exact iSup_congr fun K => iSup_congr fun _ => iSup_congr fun hc => hK K hc

theorem auxiliaryEinsteinDensity_baseMarginal (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (μ : Measure (Cosphere r)) (hFin : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hMom : HasCosphereEinsteinMoments r B hn μ) :
    μ.map projection = (ManifoldVolume.geometricMeasure B).withDensity
      (fun x => ENNReal.ofReal (auxiliaryEinsteinDensity r B hn x)) := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  let V := ManifoldVolume.geometricMeasure B
  let e := auxiliaryEinsteinDensity r B hn
  let w (x : M) := ENNReal.ofReal (e x)
  let m := μ.map projection
  let n := V.withDensity w
  have he : Continuous e := (contMDiff_auxiliaryEinsteinDensity r B hB hs hn).continuous
  have hw : Measurable w := ENNReal.continuous_ofReal.measurable.comp he.measurable
  have hπ : Measurable (projection (r := r)) := (continuous_projection r).measurable
  have hnneg : ∀ x, 0 ≤ e x := auxiliaryEinsteinDensity_nonneg_of_moments r B hB hs hn μ hMom
  letI : IsLocallyFiniteMeasure V := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  letI : IsLocallyFiniteMeasure m := by
    refine ⟨fun x => ?_⟩
    obtain ⟨K, hK, hKn, _⟩ := exists_compact_subset (isOpen_univ : IsOpen (Set.univ : Set M)) (mem_univ x)
    refine ⟨K, mem_interior_iff_mem_nhds.mp hKn, ?_⟩
    rw [Measure.map_apply hπ hK.measurableSet]
    exact hFin K hK
  letI : IsLocallyFiniteMeasure n := by
    refine ⟨fun x => ?_⟩
    obtain ⟨K, hK, hKn, _⟩ := exists_compact_subset (isOpen_univ : IsOpen (Set.univ : Set M)) (mem_univ x)
    refine ⟨K, mem_interior_iff_mem_nhds.mp hKn, ?_⟩
    obtain ⟨C, hC⟩ := (hK.image he).isBounded.exists_norm_le
    rw [withDensity_apply w hK.measurableSet]
    calc
      _ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂V := lintegral_mono_ae (by
        filter_upwards [ae_restrict_mem (μ := V) hK.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC _ (mem_image_of_mem e hy))))
      _ < ⊤ := by rw [lintegral_const, Measure.restrict_apply_univ]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  apply measure_eq_of_smooth_compact_tests m n
  intro φ hφ hc
  obtain ⟨_, _, ht⟩ := auxiliaryEinsteinDensity_tests_on_original_measure r B hn μ hMom φ hφ hc
  rw [integral_map hπ.aemeasurable hφ.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ]
  simpa only [w, Function.comp_apply, ENNReal.toReal_ofReal (hnneg _), smul_eq_mul, mul_comm] using ht.symm

end Burnett.F08.IntrinsicBaseMarginal
