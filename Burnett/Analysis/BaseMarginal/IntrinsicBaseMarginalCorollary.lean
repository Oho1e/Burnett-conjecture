import Burnett.Analysis.BaseMarginal.DependentUnitNullFibers
import Burnett.Analysis.BaseMarginal.OriginalBaseMarginalPointwiseAssembly

/-! The full base marginal and angular disintegration of a fixed quadratic measure. -/

set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 4700000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory ProbabilityTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection hamiltonian)
open Burnett.Geometry.CotangentAngularExtension
  (contMDiff_dualEnergy cotangentBundle_t2Space cotangentBundle_secondCountable)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open scoped ContDiff Manifold ProbabilityTheory ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The corollary concerns one fixed measure throughout. Fiber uniqueness is
among all measurable disintegrations of that measure over background volume. -/
structure BaseMarginalAndAngularDisintegration (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (Cosphere r)) : Prop where
  smooth_density : ContMDiff Model 𝓘(ℝ) ∞ (auxiliaryEinsteinDensity r B hn)
  nonnegative_density : ∀ x, 0 ≤ auxiliaryEinsteinDensity r B hn x
  base_marginal : μ.map projection = (ManifoldVolume.geometricMeasure B).withDensity
    (fun x => ENNReal.ofReal (auxiliaryEinsteinDensity r B hn x))
  no_base_concentration : μ.map projection ≪ ManifoldVolume.geometricMeasure B
  angular_disintegration : ∃ ν : UnitNullFiberMeasures r B hn, ν.Reconstructs μ ∧ ν.HasMassAndMoments
  disintegration_unique : ∀ ν ν' : UnitNullFiberMeasures r B hn, ν.Reconstructs μ → ν'.Reconstructs μ →
    ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, ν.law x = ν'.law x
  vanishes_over_open_vacuum : ∀ U : Set M, IsOpen U →
    (∀ x ∈ U, ricciBilinearForm B x = 0) → μ (projection ⁻¹' U) = 0

private def unitNullFiberGraph (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) : Set (M × Cosphere r) :=
  {z | z.2 ∈ unitNullFiberSet r B hn z.1}

private theorem measurable_unitNullFiberGraph (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (hB : IsSmooth B) (hs : IsSymmetric B) :
    MeasurableSet (unitNullFiberGraph r B hn) := by
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_secondCountable (M := M)
  have hH : Continuous (hamiltonian (r := r) B hn) :=
    ((contMDiff_dualEnergy B hB hn hs).continuous.comp continuous_subtype_val).div_const 2
  exact ((isClosed_eq ((continuous_projection r).comp continuous_snd) continuous_fst).inter
    (isClosed_eq (hH.comp continuous_snd) continuous_const)).measurableSet

omit [T2Space M] [SecondCountableTopology M] [BorelSpace M] in
private theorem measurableEmbedding_fiberInclusion {r : Metric (M := M)} {B : Field (M := M)}
    {hn : IsNondegenerate B} (hF : MeasurableSet (unitNullFiberGraph r B hn)) (x : M) :
    MeasurableEmbedding (Subtype.val : UnitNullFiber r B hn x → Cosphere r) :=
  MeasurableEmbedding.subtype_coe ((measurable_const.prodMk measurable_id) hF)

omit [T2Space M] in
private theorem jointLaw_of_fiber_reconstruction {r : Metric (M := M)} {B : Field (M := M)}
    {hn : IsNondegenerate B} {μ : Measure (Cosphere r)} {ν : UnitNullFiberMeasures r B hn}
    (hν : ν.Reconstructs μ) (S : Set (M × Cosphere r)) (hS : MeasurableSet S) :
    μ.map (fun p => (projection p, p)) S = ∫⁻ x, ambientUnitNullFiberLaw ν.law x (Prod.mk x ⁻¹' S)
      ∂ManifoldVolume.geometricMeasure B := by
  let f (p : Cosphere r) := (projection p, p)
  have h : Measurable f := (continuous_projection r).measurable.prodMk measurable_id
  calc
    _ = μ (f ⁻¹' S) := Measure.map_apply h hS
    _ = ∫⁻ x, ν.law x (Subtype.val ⁻¹' (f ⁻¹' S)) ∂ManifoldVolume.geometricMeasure B :=
      UnitNullFiberMeasures.reconstructs_apply hν (h hS)
    _ = _ := by
      apply lintegral_congr fun x => ?_
      rw [show ambientUnitNullFiberLaw ν.law x (Prod.mk x ⁻¹' S) =
        ν.law x (Subtype.val ⁻¹' (Prod.mk x ⁻¹' S)) from
        Measure.map_apply measurable_subtype_coe (measurable_prodMk_left hS)]
      congr 1
      ext p
      change (projection p.val, p.val) ∈ S ↔ (x, p.val) ∈ S
      rw [p.property.1]

/-- For any fixed quadratic measure of the admissible vacuum sequence, prove
the base marginal and disintegrate the same measure into its unit null fibers. -/
theorem baseMarginal_and_angularDisintegration (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (μ : Measure (Cosphere r)) (hFin : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hNull : μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r B hSig.isNondegenerate μ)
    (hScal : ∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) :
    BaseMarginalAndAngularDisintegration r B hSig.isNondegenerate μ := by
  let hn := hSig.isNondegenerate
  let hs := hSig.isSymmetric
  let V := ManifoldVolume.geometricMeasure B
  have hMarg := auxiliaryEinsteinDensity_baseMarginal r B hB hs hn μ hFin hMom
  have hSmooth := contMDiff_auxiliaryEinsteinDensity r B hB hs hn
  have hNonneg := auxiliaryEinsteinDensity_nonneg_of_moments r B hB hs hn μ hMom
  obtain ⟨κ, hκ, hLaw, hκFin, hSupport, hRec, hUnique⟩ :=
    exists_original_angularDisintegration r B hB hs hn μ hFin hNull hMom
  letI := hκ
  have hFiber : ∀ᵐ x ∂V, κ x {p | projection p ≠ x} = 0 :=
    hSupport.mono fun _ hx => measure_mono_null (fun _ hy => Or.inl hy) hx.2
  have hSymm := intrinsicEinstein_isSymm_of_originalVacuum r B g hB hg hs hsG hn hnG hconv hb hv
  have hPoint := ae_intrinsicEinstein_eq_angularFiberMoment r B hB hn hSymm μ hMom κ hLaw hFiber
  have hGraph := measurable_unitNullFiberGraph r B hn hB hs
  let G := unitNullFiberGraph r B hn
  let j (x : M) : UnitNullFiber r B hn x → Cosphere r := Subtype.val
  have hj (x : M) : MeasurableEmbedding (j x) := measurableEmbedding_fiberInclusion hGraph x
  let ν (x : M) : Measure (UnitNullFiber r B hn x) := (κ x).comap (j x)
  have hPush (x : M) : ambientUnitNullFiberLaw ν x = (κ x).restrict (unitNullFiberSet r B hn x) := by
    change ((κ x).comap (j x)).map (j x) = _
    rw [(hj x).map_comap, show range (j x) = unitNullFiberSet r B hn x from Subtype.range_coe]
  have hMeas : Measurable (ambientUnitNullFiberLaw ν) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have hGS : MeasurableSet (G ∩ Prod.snd ⁻¹' S) := hGraph.inter (measurable_snd hS)
    have hEq : (fun x => ambientUnitNullFiberLaw ν x S) =
        fun x => κ x (Prod.mk x ⁻¹' (G ∩ Prod.snd ⁻¹' S)) := by
      funext x
      rw [hPush x, Measure.restrict_apply hS, inter_comm S]
      rfl
    rw [hEq]
    exact Kernel.measurable_kernel_prodMk_left hGS
  have hMap : ambientUnitNullFiberLaw ν =ᵐ[V] (κ : M → Measure (Cosphere r)) := by
    filter_upwards [hSupport] with x hx
    rw [hPush x]
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    change κ x (unitNullFiberSet r B hn x)ᶜ = 0
    simpa only [unitNullFiberSet, compl_setOf, not_and_or] using hx.2
  have hTotal (x : M) : ambientUnitNullFiberLaw ν x univ = ν x univ := by
    change (ν x).map (j x) univ = _
    rw [(hj x).map_apply, preimage_univ]
  have hνFin : ∀ᵐ x ∂V, ν x univ < ⊤ := by
    filter_upwards [hMap] with x hx
    rw [← hTotal x, hx]
    exact (hκFin x).measure_univ_lt_top
  let K : UnitNullFiberMeasures r B hn := ⟨ν, hMeas, hνFin⟩
  refine ⟨hSmooth, hNonneg, hMarg, physicalMarginal_absolutelyContinuous r B hn μ hMarg,
    ⟨K, ?_, ?_⟩, ?_, ?_⟩
  · change μ = V.bind (ambientUnitNullFiberLaw ν)
    ext S hS
    rw [Measure.bind_apply hS hMeas.aemeasurable]
    refine (hRec S hS).trans ?_
    apply lintegral_congr_ae
    filter_upwards [hMap] with x hx
    exact congrArg (fun m : Measure (Cosphere r) => m S) hx.symm
  · change UnitNullFiberMeasures.HasMassAndMoments K
    filter_upwards [hMap, hSupport, hPoint] with x hx hmass hm
    refine ⟨(hTotal x).symm.trans ((congrArg (fun m : Measure (Cosphere r) => m univ) hx).trans hmass.1), ?_⟩
    intro u v q
    have hq (p : UnitNullFiber r B hn x) : fiberQuadraticPhase x u v (j x p) = q p := by
      have hp : projection (j x p) = x := p.property.1
      rw [fiberQuadraticPhase, dif_pos hp]
      rfl
    have hMapx : (ν x).map (j x) = κ x := hx
    have hI : Integrable (fiberQuadraticPhase x u v) ((ν x).map (j x)) := hMapx.symm ▸ (hm u v).1
    refine ⟨((hj x).integrable_map_iff.mp hI).congr (Eventually.of_forall hq), ?_⟩
    calc
      _ = ∫ p, fiberQuadraticPhase x u v p ∂κ x := (hm u v).2
      _ = ∫ p, fiberQuadraticPhase x u v p ∂(ν x).map (j x) := by rw [hMapx]
      _ = ∫ p, fiberQuadraticPhase x u v (j x p) ∂ν x := (hj x).integral_map _
      _ = _ := integral_congr_ae (Eventually.of_forall hq)
  · intro L L' hL hL'
    let J : Kernel M (Cosphere r) := ⟨ambientUnitNullFiberLaw L.law, L.measurable_ambient⟩
    let J' : Kernel M (Cosphere r) := ⟨ambientUnitNullFiberLaw L'.law, L'.measurable_ambient⟩
    have hJ := hUnique J (jointLaw_of_fiber_reconstruction hL)
    have hJ' := hUnique J' (jointLaw_of_fiber_reconstruction hL')
    filter_upwards [hJ, hJ'] with x hx hx'
    have hEq : (L.law x).map (j x) = (L'.law x).map (j x) := hx.trans hx'.symm
    have hc := congrArg (fun m : Measure (Cosphere r) => m.comap (j x)) hEq
    simpa only [(hj x).comap_map] using hc
  · intro U hU hRic
    exact physicalMeasure_zero_over_vacuumOpen r B hn μ hMarg hScal U hU fun x hx u v =>
      congrArg (fun A : LinearMap.BilinForm ℝ (TangentSpace Model x) => A u v) (hRic x hx)

end Burnett.F08.IntrinsicBaseMarginal
