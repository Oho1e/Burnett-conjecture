import Burnett.Counterexamples.Rosen.Example

/-!
# Rosen multiscale example

The intrinsic compact tensor tests and the full Einstein moment identity.
-/

set_option autoImplicit false

noncomputable section

noncomputable section
namespace Burnett.RosenMultiscale.Transport.BaseTestClass
open Filter MeasureTheory Set Burnett.RicciSymbol
open scoped ContDiff Topology

def rosenBaseDomain : Set Coordinate := {x | x 0 ∈ rosenInterval}

theorem rosenBaseDomain_isOpen : IsOpen rosenBaseDomain :=
  isOpen_Ioo.preimage (continuous_apply 0)

def rosenBaseLebesgue : Measure rosenBaseDomain := coordinateLebesgue.comap Subtype.val

theorem rosenBaseLebesgue_map : rosenBaseLebesgue.map Subtype.val = coordinateLebesgue := by
  rw [rosenBaseLebesgue, map_comap_subtype_coe rosenBaseDomain_isOpen.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem coordinateLebesgue_ae_mem

/-- Smoothness in the single coordinate chart of the actual open base slab.
No ambient extension or support requirement is assumed. -/
def HasLocalSmoothBaseRepresentatives (f : rosenBaseDomain → ℝ) : Prop :=
  ∀ p : rosenBaseDomain, ∃ (U : Set (Coordinate))
    (F : Coordinate → ℝ),
    IsOpen U ∧ (p : Coordinate) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ q : rosenBaseDomain, (q : Coordinate) ∈ U → F q.val = f q

/-- The actual zero extension of an intrinsically defined base test. -/
def baseZeroExtension (f : rosenBaseDomain → ℝ) (p : Coordinate) : ℝ := by
  classical
  exact if hp : p ∈ rosenBaseDomain then f ⟨p, hp⟩ else 0

theorem baseZeroExtension_on_subtype (f : rosenBaseDomain → ℝ) (p : rosenBaseDomain) :
    baseZeroExtension f p.val = f p := by
  simp [baseZeroExtension, p.property]

theorem baseZeroExtension_off_domain (f : rosenBaseDomain → ℝ)
    {p : Coordinate} (hp : p ∉ rosenBaseDomain) :
    baseZeroExtension f p = 0 := by
  simp [baseZeroExtension, hp]

theorem baseZeroExtension_support_subset (f : rosenBaseDomain → ℝ) :
    Function.support (baseZeroExtension f) ⊆ Subtype.val '' tsupport f := by
  intro p hp
  by_cases hd : p ∈ rosenBaseDomain
  · refine ⟨⟨p, hd⟩, ?_, rfl⟩
    apply subset_closure
    simpa [Function.mem_support, baseZeroExtension, hd] using hp
  · exact False.elim (hp (baseZeroExtension_off_domain f hd))

theorem compact_image_tsupport (f : rosenBaseDomain → ℝ) (hc : HasCompactSupport f) :
    IsCompact (Subtype.val '' tsupport f : Set (Coordinate)) :=
  hc.isCompact.image continuous_subtype_val

theorem baseZeroExtension_tsupport_subset_image (f : rosenBaseDomain → ℝ)
    (hc : HasCompactSupport f) :
    tsupport (baseZeroExtension f) ⊆ Subtype.val '' tsupport f :=
  closure_minimal (baseZeroExtension_support_subset f) (compact_image_tsupport f hc).isClosed

theorem baseZeroExtension_tsupport_subset_domain (f : rosenBaseDomain → ℝ)
    (hc : HasCompactSupport f) : tsupport (baseZeroExtension f) ⊆ rosenBaseDomain := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := baseZeroExtension_tsupport_subset_image f hc hp
  exact q.property

theorem baseZeroExtension_hasCompactSupport (f : rosenBaseDomain → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (baseZeroExtension f) := by
  exact (compact_image_tsupport f hc).of_isClosed_subset isClosed_closure
    (baseZeroExtension_tsupport_subset_image f hc)

theorem baseZeroExtension_eventuallyEq_representative
    (f : rosenBaseDomain → ℝ) (p : rosenBaseDomain)
    (U : Set (Coordinate)) (F : Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : rosenBaseDomain, q.val ∈ U → F q.val = f q) :
    baseZeroExtension f =ᶠ[𝓝 p.val] F := by
  filter_upwards [rosenBaseDomain_isOpen.mem_nhds p.property, hU.mem_nhds hpU]
    with q hq hqU
  rw [baseZeroExtension, dif_pos hq]
  exact (hrep ⟨q, hq⟩ hqU).symm

theorem baseZeroExtension_contDiff (f : rosenBaseDomain → ℝ)
    (hs : HasLocalSmoothBaseRepresentatives f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (baseZeroExtension f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ rosenBaseDomain
  · obtain ⟨U, F, hU, hpU, hF, hrep⟩ := hs ⟨p, hp⟩
    exact (hF.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
      (baseZeroExtension_eventuallyEq_representative f ⟨p, hp⟩ U F hU hpU hrep)
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp
      (fun h => hp (baseZeroExtension_tsupport_subset_domain f hc h))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coordinate => (0 : ℝ)) p)
      |>.congr_of_eventuallyEq hzero

theorem hasLocalSmoothRepresentatives_iff_zeroExtension_contDiff
    (f : rosenBaseDomain → ℝ) (hc : HasCompactSupport f) :
    HasLocalSmoothBaseRepresentatives f ↔ ContDiff ℝ ∞ (baseZeroExtension f) := by
  refine ⟨fun hs => baseZeroExtension_contDiff f hs hc, ?_⟩
  intro hext p
  exact ⟨Set.univ, baseZeroExtension f, isOpen_univ, mem_univ _, hext.contDiffOn,
    fun q _ => baseZeroExtension_on_subtype f q⟩

theorem exists_ambient_zero_extension (f : rosenBaseDomain → ℝ)
    (hs : HasLocalSmoothBaseRepresentatives f) (hc : HasCompactSupport f) :
    ∃ b : Coordinate → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ rosenBaseDomain ∧
      (∀ p : rosenBaseDomain, b p.val = f p) ∧
      (∀ p ∉ rosenBaseDomain, b p = 0) :=
  ⟨baseZeroExtension f, baseZeroExtension_contDiff f hs hc,
    baseZeroExtension_hasCompactSupport f hc, baseZeroExtension_tsupport_subset_domain f hc,
    baseZeroExtension_on_subtype f, fun _ hp => baseZeroExtension_off_domain f hp⟩

theorem baseZeroExtension_fderiv_eq_representative
    (f : rosenBaseDomain → ℝ) (p : rosenBaseDomain)
    (U : Set (Coordinate)) (F : Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : rosenBaseDomain, q.val ∈ U → F q.val = f q) :
    fderiv ℝ (baseZeroExtension f) p.val = fderiv ℝ F p.val :=
  (baseZeroExtension_eventuallyEq_representative f p U F hU hpU hrep).fderiv_eq

/-- Extend each genuine intrinsic tensor component, without an ambient support input. -/
def tensorZeroExtension (S : rosenBaseDomain → CoordinateMetric) : Coordinate → CoordinateMetric :=
  fun x i j => baseZeroExtension (fun p => S p i j) x

theorem tensor_component_hasCompactSupport (S : rosenBaseDomain → CoordinateMetric)
    (hS : HasCompactSupport S) (i j : Index) : HasCompactSupport (fun p => S p i j) :=
  hS.comp_left (g := fun m : CoordinateMetric => m i j) rfl

theorem tensorZeroExtension_on_subtype (S : rosenBaseDomain → CoordinateMetric)
    (p : rosenBaseDomain) : tensorZeroExtension S p.val = S p := by
  ext i j
  exact baseZeroExtension_on_subtype (fun p => S p i j) p

theorem tensorZeroExtension_component_properties (S : rosenBaseDomain → CoordinateMetric)
    (hs : ∀ i j : Index, HasLocalSmoothBaseRepresentatives (fun p => S p i j))
    (hc : HasCompactSupport S) (i j : Index) :
    ContDiff ℝ ∞ (fun x => tensorZeroExtension S x i j) ∧
      HasCompactSupport (fun x => tensorZeroExtension S x i j) ∧
      tsupport (fun x => tensorZeroExtension S x i j) ⊆ rosenBaseDomain :=
  ⟨baseZeroExtension_contDiff _ (hs i j) (tensor_component_hasCompactSupport S hc i j),
    baseZeroExtension_hasCompactSupport _ (tensor_component_hasCompactSupport S hc i j),
    baseZeroExtension_tsupport_subset_domain _ (tensor_component_hasCompactSupport S hc i j)⟩

/-- The actual base point of a nonzero phase-space point in the open slab. -/
def phaseBase (p : rosenPhaseDomain) : rosenBaseDomain := ⟨p.val.1, p.property.1⟩

theorem intrinsic_tensor_einstein_moment (pulled : Bool)
    (S : rosenBaseDomain → CoordinateMetric)
    (hs : ∀ i j : Index, HasLocalSmoothBaseRepresentatives (fun p => S p i j))
    (hc : HasCompactSupport S) :
    let l := fun p : rosenPhaseDomain =>
      ∑ k : Index × Index, S (phaseBase p) k.1 k.2 * p.val.2 k.1 * p.val.2 k.2
    let r := fun x : rosenBaseDomain =>
      ∑ k : Index × Index, S x k.1 k.2 * rosenLimitEinstein pulled x.val k.1 k.2 *
        Real.sqrt |(rosenLimitMetric pulled x.val).det|
    Integrable l (rosenPhaseMeasure pulled) ∧ Integrable r rosenBaseLebesgue ∧
      (∫ p, l p ∂rosenPhaseMeasure pulled) = ∫ x, r x ∂rosenBaseLebesgue := by
  let L0 := fun p : rosenPhaseDomain =>
    ∑ k : Index × Index, tensorZeroExtension S p.val.1 k.1 k.2 * p.val.2 k.1 * p.val.2 k.2
  let L := fun p : rosenPhaseDomain =>
    ∑ k : Index × Index, S (phaseBase p) k.1 k.2 * p.val.2 k.1 * p.val.2 k.2
  let R0 := fun x : Coordinate =>
    ∑ k : Index × Index, tensorZeroExtension S x k.1 k.2 * rosenLimitEinstein pulled x k.1 k.2 *
      Real.sqrt |(rosenLimitMetric pulled x).det|
  let R := fun x : rosenBaseDomain =>
    ∑ k : Index × Index, S x k.1 k.2 * rosenLimitEinstein pulled x.val k.1 k.2 *
      Real.sqrt |(rosenLimitMetric pulled x.val).det|
  have h := rosenPhaseMeasure_einstein_moment pulled (tensorZeroExtension S)
    (fun i j => ⟨(tensorZeroExtension_component_properties S hs hc i j).1.continuous,
      (tensorZeroExtension_component_properties S hs hc i j).2.1⟩)
  change Integrable L0 (rosenPhaseMeasure pulled) ∧ Integrable R0 coordinateLebesgue ∧
    (∫ p, L0 p ∂rosenPhaseMeasure pulled) = ∫ x, R0 x ∂coordinateLebesgue at h
  have hL : L0 = L := by
    funext p
    dsimp [L0, L]
    rw [show tensorZeroExtension S p.val.1 = S (phaseBase p) from
      tensorZeroExtension_on_subtype S (phaseBase p)]
  have hR : (fun x : rosenBaseDomain => R0 x.val) = R := by
    funext x
    dsimp [R0, R]
    rw [tensorZeroExtension_on_subtype]
  have hcoe : Measurable (Subtype.val : rosenBaseDomain → Coordinate) := measurable_subtype_coe
  have hRmap : Integrable R0 (rosenBaseLebesgue.map Subtype.val) := by
    rw [rosenBaseLebesgue_map]
    exact h.2.1
  have hi : Integrable (fun x : rosenBaseDomain => R0 x.val) rosenBaseLebesgue :=
    (integrable_map_measure hRmap.aestronglyMeasurable hcoe.aemeasurable).mp hRmap
  have heq : (∫ x : rosenBaseDomain, R0 x.val ∂rosenBaseLebesgue) =
      ∫ x, R0 x ∂coordinateLebesgue := by
    have hh := integral_map hcoe.aemeasurable hRmap.aestronglyMeasurable
    rw [rosenBaseLebesgue_map] at hh
    exact hh.symm
  rw [hR] at hi heq
  rw [hL] at h
  exact ⟨h.1, hi, h.2.2.trans heq.symm⟩

end Burnett.RosenMultiscale.Transport.BaseTestClass
