import Burnett.Geometry.Cotangent.Core
import Burnett.Geometry.Cotangent.LocalAngular
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.AngularExtension

open Set Function
open scoped Manifold ContDiff

variable {E H X B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  [T2Space X] [SigmaCompactSpace X] [TopologicalSpace B]

/-- Glue local smooth extensions on a closed subset, preserving the specified closed base support. -/
theorem extend_closed_with_base_support (I : ModelWithCorners ℝ E H) [IsManifold I ∞ X]
    {S : Set X} (hS : IsClosed S) (a : X → ℝ) (p : X → B) (hp : Continuous p)
    {K : Set B} (hK : IsClosed K)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ g : X → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ g U ∧ EqOn g a (U ∩ S) ∧
        ∀ y ∈ U, p y ∉ K → g y = 0) :
    ∃ f : X → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ EqOn f a S ∧ tsupport f ⊆ p ⁻¹' K := by
  classical
  choose U hU hmem g hg hgeq hzero using fun x : S => hloc x.1 x.2
  have hcover : S ⊆ ⋃ i, U i := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hS U hU hcover
  let f := fun x => ∑ᶠ i, ρ i x • g i x
  have hsupp {i : S} {x : X} (hx : ρ i x ≠ 0) : x ∈ U i :=
    hρ i (subset_tsupport (ρ i) hx)
  refine ⟨f, hρ.contMDiff_finsum_smul hU hg, ?_, ?_⟩
  · intro x hx
    calc
      f x = ∑ᶠ i, ρ i x • a x := by
        apply finsum_congr
        intro i
        by_cases hi : ρ i x = 0
        · simp [hi]
        · rw [hgeq i ⟨hsupp hi, hx⟩]
      _ = (∑ᶠ i, ρ i x) • a x := (finsum_smul _ _).symm
      _ = a x := by rw [ρ.sum_eq_one hx, one_smul]
  · apply closure_minimal _ (hK.preimage hp)
    intro x hx
    by_contra h
    apply hx
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases hi : ρ i x = 0
    · simp [hi]
    · rw [hzero i x (hsupp hi) h, smul_zero]

end Burnett.Geometry.AngularExtension

namespace Burnett.Geometry.CotangentAngularExtension

open Bundle Set Function
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.UnitNullAngular (Phase)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

abbrev CotangentModelWithCorners := Model.prod 𝓘(ℝ, CotangentModel)

abbrev CoordinatePhaseModel := Model.prod 𝓘(ℝ, Covector)

def cotangentSource (c : M) : Set (CotangentBundle M) :=
  (fun p => p.1) ⁻¹' (chartAt CoordinateSpace c).source

def phaseTarget (c : M) : Set Phase :=
  (chartAt CoordinateSpace c).target ×ˢ (univ : Set Covector)

theorem isOpen_cotangentSource (c : M) : IsOpen (cotangentSource c) :=
  (chartAt CoordinateSpace c).open_source.preimage continuous_cotangent_projection

omit [IsManifold Model ∞ M] in
theorem isOpen_phaseTarget (c : M) : IsOpen (phaseTarget c) :=
  (chartAt CoordinateSpace c).open_target.prod isOpen_univ

theorem cotangentTrivialization_source (c : M) :
    (cotangentTrivialization c).source = cotangentSource c := by
  rw [(cotangentTrivialization c).source_eq, cotangentTrivialization_baseSet]
  rfl

def cotangentChart (c : M) (p : CotangentBundle M) : Phase :=
  (chartAt CoordinateSpace c p.1, cotangentCoords c p)

def cotangentChartInverse (c : M) (p : Phase) : CotangentBundle M :=
  cotangentAssemble c ((chartAt CoordinateSpace c).symm p.1, p.2)

theorem cotangentChart_mapsTo (c : M) :
    MapsTo (cotangentChart c) (cotangentSource c) (phaseTarget c) :=
  fun _ hp => ⟨(chartAt CoordinateSpace c).map_source hp, trivial⟩

theorem cotangentChartInverse_mapsTo (c : M) :
    MapsTo (cotangentChartInverse c) (phaseTarget c) (cotangentSource c) :=
  fun _ hp => (chartAt CoordinateSpace c).symm_mapsTo hp.1

theorem cotangentChart_left_inv (c : M) {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    cotangentChartInverse c (cotangentChart c p) = p := by
  unfold cotangentChartInverse cotangentChart
  rw [(chartAt CoordinateSpace c).left_inv hp]
  exact cotangentAssemble_coords c p hp

theorem cotangentChart_right_inv (c : M) {p : Phase} (hp : p ∈ phaseTarget c) :
    cotangentChart c (cotangentChartInverse c p) = p := by
  rcases p with ⟨y, ξ⟩
  have hy : y ∈ (chartAt CoordinateSpace c).target := hp.1
  have hs := (chartAt CoordinateSpace c).symm_mapsTo hy
  unfold cotangentChart cotangentChartInverse
  have hb : (cotangentAssemble c ((chartAt CoordinateSpace c).symm y, ξ)).1 =
      (chartAt CoordinateSpace c).symm y := rfl
  rw [hb, (chartAt CoordinateSpace c).right_inv hy, cotangentCoords_assemble c _ hs]

private theorem contDiff_componentsOfCLM :
    ContDiff ℝ ∞ (fun (L : CotangentModel) (i : Index) => L (coordinateBasis i)) := by
  apply contDiff_pi.mpr
  intro i
  exact (ContinuousLinearMap.apply ℝ ℝ (coordinateBasis i)).contDiff

private theorem contDiff_covectorCLM : ContDiff ℝ ∞ covectorCLM := by
  unfold covectorCLM
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).smul contDiff_const

private theorem cotangentTrivialization_atlas (c : M) : MemTrivializationAtlas (cotangentTrivialization c) := by
  unfold cotangentTrivialization
  infer_instance

theorem contMDiffOn_cotangentChart (c : M) :
    ContMDiffOn CotangentModelWithCorners CoordinatePhaseModel ∞ (cotangentChart c) (cotangentSource c) := by
  letI := cotangentTrivialization_atlas c
  have htriv := (cotangentTrivialization c).contMDiffOn (IB := Model) (n := ∞)
  rw [cotangentTrivialization_source] at htriv
  have hbase : MapsTo (fun p => (cotangentTrivialization c p).1) (cotangentSource c)
      (chartAt CoordinateSpace c).source := by
    intro p hp
    change (cotangentTrivialization c p).1 ∈ (chartAt CoordinateSpace c).source
    rw [(cotangentTrivialization c).coe_fst (cotangentTrivialization_source c ▸ hp)]
    exact hp
  have hfst : ContMDiffOn CotangentModelWithCorners Model ∞
      (fun p => chartAt CoordinateSpace c (cotangentTrivialization c p).1) (cotangentSource c) :=
    (contMDiffOn_chart (I := Model)).comp (contMDiff_fst.comp_contMDiffOn htriv) hbase
  have hsnd : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ, Covector) ∞
      (cotangentCoords c) (cotangentSource c) :=
    contDiff_componentsOfCLM.contMDiff.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn htriv)
  apply (hfst.prodMk hsnd).congr
  intro p hp
  unfold cotangentChart
  rw [(cotangentTrivialization c).coe_fst (cotangentTrivialization_source c ▸ hp)]

theorem contMDiffOn_cotangentChartInverse (c : M) :
    ContMDiffOn CoordinatePhaseModel CotangentModelWithCorners ∞
      (cotangentChartInverse c) (phaseTarget c) := by
  letI := cotangentTrivialization_atlas c
  have htriv := (cotangentTrivialization c).contMDiffOn_symm (IB := Model) (n := ∞)
  have h1 : ContMDiffOn CoordinatePhaseModel Model ∞
      (fun p : Phase => (chartAt CoordinateSpace c).symm p.1) (phaseTarget c) :=
    (contMDiffOn_chart_symm (I := Model)).comp contMDiffOn_fst (fun _ hp => hp.1)
  have h2 : ContMDiffOn CoordinatePhaseModel 𝓘(ℝ, CotangentModel) ∞
      (fun p : Phase => covectorCLM p.2) (phaseTarget c) :=
    contDiff_covectorCLM.contMDiff.comp_contMDiffOn contMDiffOn_snd
  have hm : MapsTo
      (fun p : Phase => ((chartAt CoordinateSpace c).symm p.1, covectorCLM p.2))
      (phaseTarget c) (cotangentTrivialization c).target := by
    rw [(cotangentTrivialization c).target_eq, cotangentTrivialization_baseSet]
    exact fun _ hp => ⟨(chartAt CoordinateSpace c).symm_mapsTo hp.1, trivial⟩
  refine (htriv.comp (h1.prodMk h2) hm).congr ?_
  intro p hp
  have hy := (chartAt CoordinateSpace c).symm_mapsTo hp.1
  have hb : (chartAt CoordinateSpace c).symm p.1 ∈ (cotangentTrivialization c).baseSet := by
    rwa [cotangentTrivialization_baseSet]
  unfold cotangentChartInverse cotangentAssemble
  exact (cotangentTrivialization c).mk_symm hb (covectorCLM p.2)

end Burnett.Geometry.CotangentAngularExtension

namespace Burnett.Geometry.CotangentAngularExtension

open Bundle Set Function
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.UnitNullAngular (Phase chartInverse chartInverse_smooth contDiffOn_dualPair)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem coordinateContDiffOn_to_manifold {f : Phase → ℝ} {U : Set Phase}
    (hf : ContDiffOn ℝ ∞ f U) : ContMDiffOn CoordinatePhaseModel 𝓘(ℝ) ∞ f U := by
  have hh := hf.contMDiffOn
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
  exact hh

theorem contMDiff_dualEnergy (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) :
    ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ (dualEnergy g hgn) := by
  intro p
  let c := p.1
  have hp : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  let Q := fun q : Phase => symbolNorm (chartInverse g c q.1) q.2
  have hQ : ContDiffOn ℝ ∞ Q (phaseTarget c) := by
    unfold Q
    simp_rw [← UnitNullAngular.dualPair_self]
    exact contDiffOn_dualPair (chartInverse g c) (chartInverse_smooth g hg hgn c)
      (fun _ hp => hp.1) contDiffOn_snd contDiffOn_snd
  have hcomp := (coordinateContDiffOn_to_manifold hQ).comp (contMDiffOn_cotangentChart c)
    (cotangentChart_mapsTo c)
  have hcomp' : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ (dualEnergy g hgn) (cotangentSource c) :=
    hcomp.congr (fun q hq => dualEnergy_chart g hgn hgs c q hq)
  exact hcomp'.contMDiffAt ((isOpen_cotangentSource c).mem_nhds hp)

theorem isClosed_cotangentUnitNull (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) :
    IsClosed (cotangentUnitNull r g hgn) := by
  have hr := (contMDiff_dualEnergy r.inner (ManifoldBilinear.isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) r.symm).continuous
  have hG := (contMDiff_dualEnergy g hg hgn hgs).continuous
  exact (isClosed_eq hr continuous_const).inter (isClosed_eq hG continuous_const)

theorem cotangentChart_unitNull_iff (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (c : M) {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    cotangentChart c p ∈ UnitNullAngular.chartUnitNull r g c ↔ p ∈ cotangentUnitNull r g hgn := by
  rw [UnitNullAngular.chartUnitNull_mem]
  unfold cotangentChart cotangentUnitNull
  rw [mem_setOf_eq, dualEnergy_chart g hgn hgs c p hp,
    dualEnergy_chart r.inner (GlobalLeviCivita.inner_nondegenerate r) r.symm c p hp]
  have hx : (chartAt CoordinateSpace c) p.1 ∈ (chartAt CoordinateSpace c).target :=
    (chartAt CoordinateSpace c).map_source hp
  simp only [hx, and_true]
  rfl

/-- A local smooth extension on the actual cotangent bundle, preserving the prescribed base support. -/
theorem local_actual_cotangent_extension (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a (cotangentUnitNull r g hgn))
    {K : Set M} (hvanish : ∀ p ∈ cotangentUnitNull r g hgn, p.1 ∉ K → a p = 0)
    (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hgn) :
    ∃ U : Set (CotangentBundle M), IsOpen U ∧ p ∈ U ∧
      ∃ ext : CotangentBundle M → ℝ, ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ ext U ∧
        EqOn ext a (U ∩ cotangentUnitNull r g hgn) ∧ ∀ q ∈ U, q.1 ∉ K → ext q = 0 := by
  let c := p.1
  have hpSource : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  have hpChart : cotangentChart c p ∈ UnitNullAngular.chartUnitNull r g c :=
    (cotangentChart_unitNull_iff r g hgn hgs c hpSource).mpr hp
  obtain ⟨W, hWo, hpW, hWt, ret, hret, hmaps, hbase, hfix⟩ :=
    UnitNullAngular.local_chartUnitNull_retraction r g hg hgn hgs c hpChart
  let U := cotangentSource c ∩ cotangentChart c ⁻¹' W
  have hU : IsOpen U :=
    (contMDiffOn_cotangentChart c).continuousOn.isOpen_inter_preimage (isOpen_cotangentSource c) hWo
  have hc : ContMDiffOn CotangentModelWithCorners CoordinatePhaseModel ∞ (cotangentChart c) U :=
    (contMDiffOn_cotangentChart c).mono inter_subset_left
  have hretM : ContMDiffOn CoordinatePhaseModel CoordinatePhaseModel ∞ ret W := by
    have h := hret.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hI : MapsTo (cotangentChartInverse c) (UnitNullAngular.chartUnitNull r g c) (cotangentUnitNull r g hgn) := by
    intro q hq
    have ht : q ∈ phaseTarget c := hq.2
    have hsource := cotangentChartInverse_mapsTo c ht
    apply (cotangentChart_unitNull_iff r g hgn hgs c hsource).mp
    rwa [cotangentChart_right_inv c ht]
  let lift := cotangentChartInverse c ∘ ret ∘ cotangentChart c
  have hphase : MapsTo (ret ∘ cotangentChart c) U (UnitNullAngular.chartUnitNull r g c) :=
    hmaps.comp (fun _ hq => hq.2)
  have hlift : ContMDiffOn CotangentModelWithCorners CotangentModelWithCorners ∞ lift U :=
    (contMDiffOn_cotangentChartInverse c).comp (hretM.comp hc (fun _ hq => hq.2))
      (fun _ hq => (hphase hq).2)
  refine ⟨U, hU, ⟨hpSource, hpW⟩, a ∘ lift, ha.comp hlift (hI.comp hphase), ?_, ?_⟩
  · intro q hq
    have hsource : q ∈ cotangentSource c := hq.1.1
    have ht : cotangentChart c q ∈ UnitNullAngular.chartUnitNull r g c :=
      (cotangentChart_unitNull_iff r g hgn hgs c hsource).mpr hq.2
    change a (cotangentChartInverse c (ret (cotangentChart c q))) = a q
    rw [hfix _ hq.1.2 ht, cotangentChart_left_inv c hsource]
  · intro q hq hqK
    have hb : (lift q).1 = q.1 := by
      change (chartAt CoordinateSpace c).symm (ret (cotangentChart c q)).1 = q.1
      rw [hbase _ hq.2]
      exact (chartAt CoordinateSpace c).left_inv hq.1
    apply hvanish _ (hI (hphase hq))
    change (lift q).1 ∉ K
    rwa [hb]

end Burnett.Geometry.CotangentAngularExtension

namespace Burnett.Geometry.CotangentAngularExtension

open Bundle Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def cotangentChartHomeomorph (c : M) : cotangentSource c ≃ₜ phaseTarget c where
  toFun p := ⟨cotangentChart c p.1, cotangentChart_mapsTo c p.2⟩
  invFun q := ⟨cotangentChartInverse c q.1, cotangentChartInverse_mapsTo c q.2⟩
  left_inv p := Subtype.ext (cotangentChart_left_inv c p.2)
  right_inv q := Subtype.ext (cotangentChart_right_inv c q.2)
  continuous_toFun :=
    (continuousOn_iff_continuous_restrict.mp (contMDiffOn_cotangentChart c).continuousOn).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_restrict.mp (contMDiffOn_cotangentChartInverse c).continuousOn).subtype_mk _

theorem cotangentBundle_t2Space [T2Space M] : T2Space (CotangentBundle M) := by
  constructor
  intro p q hpq
  by_cases he : p.1 = q.1
  · let c := p.1
    have hp : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
    have hq : q ∈ cotangentSource c := by
      change q.1 ∈ (chartAt CoordinateSpace c).source
      rw [← he]
      exact hp
    have hpq' : (⟨p, hp⟩ : cotangentSource c) ≠ ⟨q, hq⟩ :=
      fun h => hpq (congrArg Subtype.val h)
    haveI : T2Space (cotangentSource c) := (cotangentChartHomeomorph c).isEmbedding.t2Space
    obtain ⟨U, V, hU, hV, hpu, hqv, hd⟩ := t2_separation hpq'
    refine ⟨Subtype.val '' U, Subtype.val '' V,
      (isOpen_cotangentSource c).isOpenMap_subtype_val _ hU,
      (isOpen_cotangentSource c).isOpenMap_subtype_val _ hV,
      ⟨⟨p, hp⟩, hpu, rfl⟩, ⟨⟨q, hq⟩, hqv, rfl⟩, disjoint_image_of_injective Subtype.val_injective hd⟩
  · obtain ⟨U, V, hU, hV, hp, hq, hd⟩ := t2_separation he
    let proj := fun z : CotangentBundle M => z.1
    exact ⟨proj ⁻¹' U, proj ⁻¹' V, hU.preimage continuous_cotangent_projection,
      hV.preimage continuous_cotangent_projection, hp, hq, hd.preimage proj⟩

theorem cotangentBundle_secondCountable [SecondCountableTopology M] :
    SecondCountableTopology (CotangentBundle M) := by
  obtain ⟨C, hC, hcover⟩ := isOpen_iUnion_countable
    (fun c : M => (chartAt CoordinateSpace c).source) (fun c => (chartAt CoordinateSpace c).open_source)
  have hbase (m : M) : m ∈ ⋃ c ∈ C, (chartAt CoordinateSpace c).source := by
    rw [hcover]
    exact mem_iUnion.mpr ⟨m, mem_chart_source CoordinateSpace m⟩
  letI : Countable C := hC.to_subtype
  letI : ∀ c : C, SecondCountableTopology (cotangentSource c.1) :=
    fun c => (cotangentChartHomeomorph c.1).isEmbedding.secondCountableTopology
  apply secondCountableTopology_of_countable_cover (U := fun c : C => cotangentSource c.1)
    (fun c => isOpen_cotangentSource c.1)
  apply eq_univ_of_forall
  intro p
  obtain ⟨c, hc, hp⟩ := mem_iUnion₂.mp (hbase p.1)
  exact mem_iUnion.mpr ⟨⟨c, hc⟩, hp⟩

theorem finiteDimensional_cotangentModel : FiniteDimensional ℝ CotangentModel := by
  let e : (CoordinateSpace →ₗ[ℝ] ℝ) ≃ₗ[ℝ] CotangentModel := LinearMap.toContinuousLinearMap
  exact e.finiteDimensional

theorem cotangentBundle_sigmaCompact [SecondCountableTopology M] :
    SigmaCompactSpace (CotangentBundle M) := by
  letI := cotangentBundle_secondCountable (M := M)
  letI := finiteDimensional_cotangentModel
  letI : LocallyCompactSpace (ModelProd CoordinateSpace CotangentModel) :=
    CotangentModelWithCorners.locallyCompactSpace
  letI : LocallyCompactSpace (CotangentBundle M) :=
    ChartedSpace.locallyCompactSpace (ModelProd CoordinateSpace CotangentModel) (CotangentBundle M)
  infer_instance

/-- Global smooth extension of angular data from the actual unit-null subset of the cotangent bundle. -/
theorem actual_cotangent_angular_extension [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a (cotangentUnitNull r g hgn))
    {K : Set M} (hK : IsCompact K) (hz : ∀ p ∈ cotangentUnitNull r g hgn, p.1 ∉ K → a p = 0) :
    ∃ f : CotangentBundle M → ℝ, ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ f ∧
      EqOn f a (cotangentUnitNull r g hgn) ∧ tsupport f ⊆ (fun p => p.1) ⁻¹' K := by
  letI := finiteDimensional_cotangentModel
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_sigmaCompact (M := M)
  exact Burnett.Geometry.AngularExtension.extend_closed_with_base_support CotangentModelWithCorners
    (isClosed_cotangentUnitNull r g hg hgn hgs) a (fun p => p.1) continuous_cotangent_projection
    hK.isClosed (fun p hp => local_actual_cotangent_extension r g hg hgn hgs a ha hz p hp)

end Burnett.Geometry.CotangentAngularExtension

namespace Burnett.Geometry.CotangentAngularExtension

open Bundle Set Function
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.UnitNullAngular (Phase)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem contMDiff_cotangentScale :
    ContMDiff (𝓘(ℝ).prod CotangentModelWithCorners) CotangentModelWithCorners ∞
      (fun q : ℝ × CotangentBundle M => cotangentScale q.1 q.2) := by
  intro q
  let c := q.2.1
  let U : Set (ℝ × CotangentBundle M) := Prod.snd ⁻¹' cotangentSource c
  have hU : IsOpen U := (isOpen_cotangentSource c).preimage continuous_snd
  have hq : q ∈ U := mem_chart_source CoordinateSpace c
  have hC : ContMDiffOn (𝓘(ℝ).prod CotangentModelWithCorners) CoordinatePhaseModel ∞
      (fun z : ℝ × CotangentBundle M => cotangentChart c z.2) U :=
    (contMDiffOn_cotangentChart c).comp contMDiffOn_snd (fun _ hz => hz)
  let F := fun z : ℝ × CotangentBundle M =>
    ((cotangentChart c z.2).1, z.1 • (cotangentChart c z.2).2)
  have hF : ContMDiffOn (𝓘(ℝ).prod CotangentModelWithCorners) CoordinatePhaseModel ∞ F U :=
    (contMDiff_fst.comp_contMDiffOn hC).prodMk
      (contMDiffOn_fst.smul (contMDiff_snd.comp_contMDiffOn hC))
  have hT : MapsTo F U (phaseTarget c) := fun z hz => ⟨(cotangentChart_mapsTo c hz).1, trivial⟩
  have hI := (contMDiffOn_cotangentChartInverse c).comp hF hT
  have hS : ContMDiffOn (𝓘(ℝ).prod CotangentModelWithCorners) CotangentModelWithCorners ∞
      (fun z : ℝ × CotangentBundle M => cotangentScale z.1 z.2) U := by
    apply hI.congr
    intro z hz
    have hsource : cotangentScale z.1 z.2 ∈ cotangentSource c := hz
    have he : cotangentChart c (cotangentScale z.1 z.2) = F z := by
      unfold cotangentChart F
      rw [cotangentScale_projection, cotangentScale_coords]
      rfl
    have h := (cotangentChart_left_inv c hsource).symm
    rwa [he] at h
  exact hS.contMDiffAt (hU.mem_nhds hq)

def puncturedCotangent : Set (CotangentBundle M) := {p | p.2 ≠ 0}

def intrinsicWeightedTrace (b s : CotangentBundle M → ℝ) (p : CotangentBundle M) : ℝ :=
  b (cotangentScale (s p) p) / s p

theorem contMDiffOn_intrinsicWeightedTrace (r : Metric (M := M))
    (g : ManifoldBilinear.Field (M := M)) (hgn : ManifoldBilinear.IsNondegenerate g)
    (b s : CotangentBundle M → ℝ)
    (hb : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent)
    (hs : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s (cotangentUnitNull r g hgn))
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p) :
    ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ (intrinsicWeightedTrace b s)
      (cotangentUnitNull r g hgn) := by
  have hL : ContMDiffOn CotangentModelWithCorners CotangentModelWithCorners ∞
      (fun p : CotangentBundle M => cotangentScale (s p) p) (cotangentUnitNull r g hgn) :=
    contMDiff_cotangentScale.comp_contMDiffOn (hs.prodMk contMDiffOn_id)
  have hpunct : MapsTo (fun p => cotangentScale (s p) p) (cotangentUnitNull r g hgn) puncturedCotangent := by
    intro p hp
    change s p • p.2 ≠ 0
    exact smul_ne_zero (hpos p hp).ne' (cotangentUnitNull_covector_ne_zero r g hgn hp)
  exact (hb.comp hL hpunct).div₀ hs (fun p hp => (hpos p hp).ne')

/-- Global smooth angular extension for the actual test trace, with compact base support. -/
theorem actual_weightedTrace_angular_extension [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (b s : CotangentBundle M → ℝ)
    (hb : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent)
    (hcompact : HasCompactSupport (fun p : puncturedCotangent (M := M) => b p.1))
    (hs : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s (cotangentUnitNull r g hgn))
    (hpos : ∀ p ∈ cotangentUnitNull r g hgn, 0 < s p) :
    ∃ K : Set M, IsCompact K ∧ ∃ f : CotangentBundle M → ℝ,
      ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ f ∧
      EqOn f (intrinsicWeightedTrace b s) (cotangentUnitNull r g hgn) ∧
      tsupport f ⊆ (fun p => p.1) ⁻¹' K := by
  let proj := fun p : puncturedCotangent (M := M) => p.1.1
  let K : Set M := proj '' tsupport (fun p : puncturedCotangent (M := M) => b p.1)
  have hK : IsCompact K := hcompact.image (continuous_cotangent_projection.comp continuous_subtype_val)
  refine ⟨K, hK, actual_cotangent_angular_extension r g hg hgn hgs _
    (contMDiffOn_intrinsicWeightedTrace r g hgn b s hb hs hpos) hK ?_⟩
  intro p hp hpK
  have hz : b (cotangentScale (s p) p) = 0 := by
    by_contra h
    have hn : cotangentScale (s p) p ∈ puncturedCotangent := by
      change s p • p.2 ≠ 0
      exact smul_ne_zero (hpos p hp).ne' (cotangentUnitNull_covector_ne_zero r g hgn hp)
    exact hpK ⟨⟨cotangentScale (s p) p, hn⟩, subset_tsupport _ h, rfl⟩
  rw [intrinsicWeightedTrace, hz, zero_div]

end Burnett.Geometry.CotangentAngularExtension
