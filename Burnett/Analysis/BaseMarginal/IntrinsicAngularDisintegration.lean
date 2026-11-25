import Burnett.Analysis.BaseMarginal.CompactTargetDisintegration
import Burnett.Analysis.BaseMarginal.IntrinsicBaseMarginal

/-! Disintegrate the same physical measure on the actual auxiliary unit null fibers. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 4400000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set MeasureTheory Filter ProbabilityTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection hamiltonian)
open Burnett.Geometry.CotangentAngularExtension (contMDiff_dualEnergy cotangentBundle_t2Space cotangentBundle_secondCountable)
open Burnett.F08.FiberGluing
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open scoped ContDiff Manifold Topology ENNReal ProbabilityTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The graph couples each unit covector to its own base point before disintegration. -/
theorem exists_original_angularDisintegration (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (μ : Measure (Cosphere r)) (hFin : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hNull : μ {p | hamiltonian B hn p ≠ 0} = 0) (hMom : HasCosphereEinsteinMoments r B hn μ) :
    let V := ManifoldVolume.geometricMeasure B
    let w (x : M) := ENNReal.ofReal (auxiliaryEinsteinDensity r B hn x)
    let ρ := μ.map (fun p => (projection p, p))
    ∃ k : Kernel M (Cosphere r), IsSFiniteKernel k ∧ V ⊗ₘ k = ρ ∧ (∀ x, IsFiniteMeasure (k x)) ∧
      (∀ᵐ x ∂V, k x univ = w x ∧ k x {p | projection p ≠ x ∨ hamiltonian B hn p ≠ 0} = 0) ∧
      (∀ U : Set (Cosphere r), MeasurableSet U → μ U = ∫⁻ x, k x U ∂V) ∧
      ∀ k' : Kernel M (Cosphere r), (∀ S : Set (M × Cosphere r), MeasurableSet S →
        ρ S = ∫⁻ x, k' x (Prod.mk x ⁻¹' S) ∂V) → k' =ᵐ[V] k := by
  intro V w ρ
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_secondCountable (M := M)
  letI : IsLocallyFiniteMeasure V := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  let U := compactCovering M
  have hU (n : ℕ) : IsCompact (U n) := isCompact_compactCovering M n
  have hUm (n : ℕ) : MeasurableSet (U n) := (hU n).measurableSet
  have hCover : ⋃ n, U n = univ := iUnion_compactCovering M
  letI : ∀ n, IsFiniteMeasure (V.restrict (U n)) := fun n => ⟨by
    rw [Measure.restrict_apply_univ]
    exact (hU n).measure_lt_top⟩
  let π : Cosphere r → M := projection
  let F (p : Cosphere r) := (π p, p)
  have hπ : Measurable π := (continuous_projection r).measurable
  have hF : Measurable F := hπ.prodMk measurable_id
  have hMarg : μ.map π = V.withDensity w := auxiliaryEinsteinDensity_baseMarginal r B hB hs hn μ hFin hMom
  have hE := (contMDiff_auxiliaryEinsteinDensity r B hB hs hn).continuous
  have hw : Measurable w := ENNReal.continuous_ofReal.measurable.comp hE.measurable
  let W (n : ℕ) : Set (Cosphere r) := {p | p.val ∈ cotangentUnitNull r B hn ∧ π p ∈ U n}
  have hW (n : ℕ) : IsCompact (W n) := by
    rw [Subtype.isCompact_iff]
    have hIm : Subtype.val '' W n = {p ∈ cotangentUnitNull r B hn | p.proj ∈ U n} := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hp
        exact ⟨⟨p, hp.1.1⟩, hp, rfl⟩
    rw [hIm]
    exact isCompact_cotangentUnitNull_over r B hB hn hs (hU n)
  have hLocal (n : ℕ) : ∃ k : Kernel M (Cosphere r), IsFiniteKernel k ∧
      V.restrict (U n) ⊗ₘ k = ρ.restrict (Prod.fst ⁻¹' U n) ∧
      ∀ᵐ x ∂V.restrict (U n), k x univ = w x := by
    let ν := μ.restrict (π ⁻¹' U n)
    let v := V.restrict (U n)
    let weight := (U n).indicator w
    letI : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hFin _ (hU n)⟩
    have hSupp : ν (W n)ᶜ = 0 := by
      apply ae_iff.mp
      filter_upwards [ae_restrict_mem (μ := μ) (hπ (hUm n)), ae_restrict_of_ae (ae_iff.mpr hNull)] with p hp hnP
      refine ⟨⟨p.prop, ?_⟩, hp⟩
      change dualEnergy B hn p.val / 2 = 0 at hnP
      linarith
    have hWgt : w =ᵐ[v] weight := by
      filter_upwards [ae_restrict_mem (μ := V) (hUm n)] with x hx
      exact (indicator_of_mem hx w).symm
    have hm : ν.map π = v.withDensity weight := by
      change (μ.restrict (π ⁻¹' U n)).map π = _
      rw [← Measure.restrict_map hπ (hUm n), hMarg, restrict_withDensity (hUm n)]
      exact withDensity_congr_ae hWgt
    obtain ⟨C, hC⟩ := ((hU n).image hE).isBounded.exists_norm_le
    have hb (x : M) : weight x ≤ ENNReal.ofReal C := by
      change (U n).indicator w x ≤ _
      by_cases hx : x ∈ U n
      · rw [indicator_of_mem hx]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC _ (mem_image_of_mem _ hx)))
      · rw [indicator_of_notMem hx]
        exact zero_le _
    obtain ⟨k, hk, hLaw, hMass⟩ := exists_finite_graphDisintegration_of_compact_target v ν π hπ (hW n) hSupp
      weight (hw.indicator (hUm n)) hm _ ENNReal.ofReal_ne_top hb
    have hRestr : ν.map F = ρ.restrict (Prod.fst ⁻¹' U n) :=
      (Measure.restrict_map hF (measurable_fst (hUm n))).symm
    refine ⟨k, hk, hLaw.trans hRestr, ?_⟩
    filter_upwards [hMass, hWgt] with x hx he
    exact hx.trans he.symm
  choose k hKfin hKlaw hKmass using hLocal
  letI : ∀ n, IsFiniteKernel (k n) := hKfin
  let κ := patchKernel U hUm k
  obtain ⟨hLaw, hFinite⟩ := patchKernel_disintegrates V ρ U hUm hCover k hKlaw
  have hM := patchKernel_ae_of_local V U hUm hCover k (fun x μx => μx univ = w x) hKmass
  let Z : Set (M × Cosphere r) := {z | π z.2 = z.1 ∧ hamiltonian B hn z.2 = 0}
  have hH : Continuous (hamiltonian (r := r) B hn) :=
    ((contMDiff_dualEnergy B hB hn hs).continuous.comp continuous_subtype_val).div_const 2
  have hZ : MeasurableSet Z := ((isClosed_eq ((continuous_projection r).comp continuous_snd) continuous_fst).inter
    (isClosed_eq (hH.comp continuous_snd) continuous_const)).measurableSet
  have hZ0 : ρ Zᶜ = 0 := by
    change μ.map F Zᶜ = 0
    rw [Measure.map_apply hF hZ.compl]
    exact measure_mono_null (fun p hp => fun hz => hp ⟨rfl, hz⟩) hNull
  have hFib : ∀ᵐ x ∂V, κ x (Prod.mk x ⁻¹' Zᶜ) = 0 := by
    rw [← hLaw, Measure.compProd_apply hZ.compl,
      lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hZ.compl)] at hZ0
    exact hZ0
  refine ⟨κ, inferInstance, hLaw, hFinite, ?_, ?_, patchKernel_unique_of_integral_sections V ρ U hUm hCover k hKlaw⟩
  · filter_upwards [hM, hFib] with x hx hf
    exact ⟨hx, by simpa only [Z, preimage_compl, compl_setOf, not_and_or] using hf⟩
  · intro S hS
    have hh := congrArg (fun (m : Measure (M × Cosphere r)) => m (Prod.snd ⁻¹' S)) hLaw
    change (V ⊗ₘ κ) (Prod.snd ⁻¹' S) = μ.map F (Prod.snd ⁻¹' S) at hh
    rw [Measure.compProd_apply (measurable_snd hS), Measure.map_apply hF (measurable_snd hS)] at hh
    exact hh.symm

end Burnett.F08.IntrinsicBaseMarginal
