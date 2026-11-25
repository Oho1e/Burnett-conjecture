import Burnett.Analysis.BaseMarginal.OriginalBaseMarginalPointwiseAssembly

/-! Vanishing of the fixed physical measure gives pointwise vacuum on the open base set. -/

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 4500000

noncomputable section
namespace Burnett.P01

open Set Filter MeasureTheory ProbabilityTheory Module Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open ManifoldMetricTransition BackgroundConnection CurvatureDifference ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection hamiltonian)
open Burnett.Analysis.LocalWeakRicciIdentification (coordinateRicci_component_smoothOn)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open Burnett.F08.IntrinsicBaseMarginal
open scoped ContDiff Manifold ProbabilityTheory ENNReal

section Graph

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- With the same graph law, zero mass above a measurable base set makes its conditional measures zero there. -/
theorem ae_kernel_eq_zero_on_baseWindow_of_graphMeasure_zero
    (V : Measure X) [SFinite V] (μ : Measure Y) (π : Y → X) (hπ : Measurable π)
    (κ : Kernel X Y) [IsSFiniteKernel κ] (hLaw : V ⊗ₘ κ = μ.map (fun p => (π p, p)))
    (U : Set X) (hU : MeasurableSet U) (hZero : μ (π ⁻¹' U) = 0) :
    ∀ᵐ x ∂V.restrict U, κ x = 0 := by
  let F (p : Y) := (π p, p)
  have hF : Measurable F := hπ.prodMk measurable_id
  have hPre : F ⁻¹' (U ×ˢ (univ : Set Y)) = π ⁻¹' U := by
    ext p
    simp [F]
  have hM : (V ⊗ₘ κ) (U ×ˢ (univ : Set Y)) = 0 := by
    rw [hLaw, Measure.map_apply hF (hU.prod MeasurableSet.univ), hPre]
    exact hZero
  rw [Measure.compProd_apply_prod hU MeasurableSet.univ,
    lintegral_eq_zero_iff (κ.measurable_coe MeasurableSet.univ)] at hM
  exact hM.mono fun _ hp => Measure.measure_univ_eq_zero.mp hp

end Graph

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The smooth coordinate Ricci components extend an almost-everywhere zero tensor to all of the open set. -/
theorem intrinsicRicci_eq_zeroOn_of_ae (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (U : Set M) (hU : IsOpen U)
    (hAE : ∀ᵐ x ∂(ManifoldVolume.geometricMeasure B).restrict U,
      ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) :
    ∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0 := by
  intro x hx
  let V := ManifoldVolume.geometricMeasure B
  letI : V.IsOpenPosMeasure := ManifoldVolumeRegularity.geometricMeasure_isOpenPosMeasure B hB hn
  let e := chartAt CoordinateSpace x
  let S := U ∩ e.source
  have hS : IsOpen S := hU.inter e.open_source
  have hxe : x ∈ e.source := mem_chart_source CoordinateSpace x
  let Γ := computedConnection (coordinateBilinear B x)
  let f (i j : Index) (y : M) := coordinateRicci Γ (e y) i j
  have hCont (i j : Index) : ContinuousOn (f i j) S :=
    (((coordinateRicci_component_smoothOn B hB hn x i j).continuousOn).comp e.continuousOn e.mapsTo).mono inter_subset_right
  have hZero (i j : Index) : f i j =ᵐ[V.restrict S] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (show S ⊆ U from inter_subset_left) hAE,
      ae_restrict_mem (μ := V) hS.measurableSet] with y h hy
    exact (IntrinsicRicciTrace.ricci_coordinate_basis B hB hs hn x y hy.2 i j).symm.trans (h _ _)
  let b := tensorTangentBasis x x hxe
  have hR : ricciBilinearForm B x = 0 := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    have hFx := V.eqOn_open_of_ae_eq (hZero i j) hS (hCont i j) continuousOn_const
      (show x ∈ S from ⟨hx, hxe⟩)
    change IntrinsicRicciTrace.ricci B x (tensorTangentBasis x x hxe i) (tensorTangentBasis x x hxe j) = 0
    rw [tensorTangentBasis_apply, tensorTangentBasis_apply]
    simpa only [coordinateBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using
      (IntrinsicRicciTrace.ricci_coordinate_basis B hB hs hn x x hxe i j).trans hFx
  intro u v
  exact LinearMap.congr_fun₂ hR u v

/-- From the conditional tensor moments of the same physical measure, zero mass over an open set gives pointwise vacuum. -/
theorem intrinsicRicci_eq_zero_on_open_of_angularFiberMoments (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (κ : Kernel M (Cosphere r)) [IsSFiniteKernel κ]
    (hLaw : ManifoldVolume.geometricMeasure B ⊗ₘ κ = μ.map (fun p => (projection p, p)))
    (hPoint : ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, ∀ u v : TangentSpace Model x,
      Integrable (fiberQuadraticPhase x u v) (κ x) ∧
        intrinsicEinstein B hn x u v = ∫ p, fiberQuadraticPhase x u v p ∂κ x)
    (hScal : ∀ x, intrinsicScalar B hn x = 0) (U : Set M) (hU : IsOpen U)
    (hZero : μ (projection ⁻¹' U) = 0) :
    ∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0 := by
  let V := ManifoldVolume.geometricMeasure B
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  letI : IsLocallyFiniteMeasure V := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  have hK := ae_kernel_eq_zero_on_baseWindow_of_graphMeasure_zero V μ projection
    (continuous_projection r).measurable κ hLaw U hU.measurableSet hZero
  apply intrinsicRicci_eq_zeroOn_of_ae B hB hs hn U hU
  filter_upwards [hK, ae_restrict_of_ae (s := U) hPoint] with x hKx hx u v
  have hh := (hx u v).2
  rw [hKx, integral_zero_measure, intrinsicEinstein_eq_ricci_of_scalar_zero B hn x (hScal x)] at hh
  exact hh

/-- The original vacuum sequence provides the symmetry needed for the full angular tensor identity. -/
theorem intrinsicRicci_eq_zero_on_open_of_originalEinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (μ : Measure (Cosphere r))
    (hFin : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hNull : μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r B hSig.isNondegenerate μ)
    (hScal : ∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) (U : Set M) (hU : IsOpen U)
    (hZero : μ (projection ⁻¹' U) = 0) :
    ∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0 := by
  let hn := hSig.isNondegenerate
  let hs := hSig.isSymmetric
  have hS := intrinsicEinstein_isSymm_of_originalVacuum r B g hB hg hs hsG hn hnG hconv hb hv
  obtain ⟨κ, hk, hLaw, _, hSupport, _, _⟩ := exists_original_angularDisintegration r B hB hs hn μ hFin hNull hMom
  letI : IsSFiniteKernel κ := hk
  have hFiber : ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, κ x {p | projection p ≠ x} = 0 :=
    hSupport.mono fun _ hp => measure_mono_null (fun _ hf => Or.inl hf) hp.2
  exact intrinsicRicci_eq_zero_on_open_of_angularFiberMoments r B hB hs hn μ κ hLaw
    (ae_intrinsicEinstein_eq_angularFiberMoment r B hB hn hS μ hMom κ hLaw hFiber) hScal U hU hZero

end Burnett.P01
