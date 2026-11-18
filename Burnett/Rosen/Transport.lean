import Burnett.Counterexamples.Rosen.TestClass
import Burnett.Geometry.InverseField
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# General Rosen plane waves

The graph measure, its supports and local moments, and full Hamiltonian transport.
-/

set_option autoImplicit false

noncomputable section

set_option autoImplicit false
noncomputable section

namespace Burnett.RosenGeneral.Transport

open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open Burnett.RosenMultiscale.Transport.Fubini
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

def baseSlab (I : Set ℝ) : Set Coordinate := {x | x 0 ∈ I}

def slabVolume (I : Set ℝ) : Measure Coordinate := volume.restrict (baseSlab I)

def slabProductVolume (I : Set ℝ) : Measure (ℝ × Spatial) :=
  (volume.restrict I).prod (volume : Measure Spatial)

theorem baseSlab_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (baseSlab I) :=
  hI.preimage (continuous_apply 0)

theorem assemble_measurePreserving_slab (I : Set ℝ) (hI : MeasurableSet I) :
    MeasurePreserving assemble (slabProductVolume I) (slabVolume I) := by
  have hs : MeasurableSet (baseSlab I) := hI.preimage (measurable_pi_apply 0)
  have h := assemble_measurePreserving_all.restrict_preimage hs
  have he : assemble ⁻¹' baseSlab I = I ×ˢ (Set.univ : Set Spatial) := by
    ext p
    simp only [baseSlab, mem_preimage, mem_setOf_eq, assemble_zero, mem_prod, mem_univ, and_true]
  rw [he, ← Measure.restrict_prod_eq_prod_univ] at h
  exact h

def weightedFlux (w : ℝ → ℝ) (φ : Coordinate → ℝ) (x : Coordinate) : ℝ :=
  w (x 0) * fderiv ℝ φ x (coordinateBasis 1)

theorem weightedFlux_tsupport_subset (w : ℝ → ℝ) (φ : Coordinate → ℝ) :
    tsupport (weightedFlux w φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have hd : fderiv ℝ φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hn ((tsupport_fderiv_subset ℝ) hh))
  exact hx (by simp [weightedFlux, hd])

theorem weightedFlux_continuous (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hsub : tsupport φ ⊆ baseSlab I) :
    Continuous (weightedFlux w φ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ baseSlab I
  · have hwx : ContinuousAt w (x 0) := hw.continuousAt (hI.mem_nhds hx)
    have he : ContinuousAt (fun y : Coordinate => y 0) x := (continuous_apply 0).continuousAt
    have hd : Continuous fun y : Coordinate => fderiv ℝ φ y (coordinateBasis 1) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hwx.comp' (f := fun y : Coordinate => y 0) he).mul hd.continuousAt
  · have hn : x ∉ tsupport (weightedFlux w φ) :=
      fun hh => hx (hsub (weightedFlux_tsupport_subset w φ hh))
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    exact (continuousAt_const : ContinuousAt (fun _ : Coordinate => (0 : ℝ)) x).congr he.symm

theorem weighted_directional_integral_zero (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hsub : tsupport φ ⊆ baseSlab I) :
    Integrable (weightedFlux w φ) (slabVolume I) ∧
      (∫ x, weightedFlux w φ x ∂slabVolume I) = 0 := by
  have hcompact : HasCompactSupport (weightedFlux w φ) :=
    hc.mono' (fun x hx => weightedFlux_tsupport_subset w φ (subset_closure hx))
  have hiall : Integrable (weightedFlux w φ) (volume : Measure Coordinate) :=
    (weightedFlux_continuous I hI w hw φ hφ hsub).integrable_of_hasCompactSupport hcompact
  have hi : Integrable (weightedFlux w φ) (slabVolume I) := hiall.mono_measure Measure.restrict_le_self
  have hm := assemble_measurePreserving_slab I hI.measurableSet
  have emb : MeasurableEmbedding assemble := by
    rw [assemble_eq_measurableInverse]
    exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm.measurableEmbedding
  have hip : Integrable (fun p : ℝ × Spatial => weightedFlux w φ (assemble p))
      (slabProductVolume I) := (hm.integrable_comp_emb emb).mpr hi
  refine ⟨hi, (hm.integral_comp emb _).symm.trans ?_⟩
  rw [slabProductVolume, integral_prod _ hip]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  change (∫ s : Spatial, weightedFlux w φ (assemble (u, s))) = 0
  simp only [weightedFlux, assemble_zero]
  rw [integral_const_mul, integral_traceSlice_directional_zero φ hφ hc u, mul_zero]

end Burnett.RosenGeneral.Transport

noncomputable section

namespace Burnett.RosenGeneral.Transport

open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open Burnett.RosenMultiscale.Transport.Fubini
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal NNReal

def slabWeight (I : Set ℝ) (w : ℝ → ℝ) (x : Coordinate) : ℝ≥0 := by
  classical
  exact (I.piecewise w (fun _ => 0) (x 0)).toNNReal

theorem slabWeight_measurable (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) : Measurable (slabWeight I w) := by
  classical
  have hm : Measurable (I.piecewise w (fun _ => 0)) :=
    hw.measurable_piecewise continuous_const.continuousOn hI.measurableSet
  exact (hm.comp (measurable_pi_apply 0)).real_toNNReal

theorem slabWeight_coe_of_mem (I : Set ℝ) (w : ℝ → ℝ)
    (hn : ∀ u ∈ I, 0 ≤ w u) (x : Coordinate) (h : x ∈ baseSlab I) :
    (slabWeight I w x : ℝ) = w (x 0) := by
  classical
  change x 0 ∈ I at h
  simp [slabWeight, h, Real.toNNReal_of_nonneg (hn _ h)]

theorem slabVolume_ae_mem (I : Set ℝ) (hI : IsOpen I) :
    ∀ᵐ x ∂slabVolume I, x ∈ baseSlab I :=
  ae_restrict_mem (baseSlab_isOpen hI).measurableSet

def weightedGraphMeasure (I : Set ℝ) (w : ℝ → ℝ) : Measure (Coordinate × Coordinate) :=
  ((slabVolume I).withDensity fun x => (slabWeight I w x : ℝ≥0∞)).map (fun x => (x, du))

theorem weightedGraphMeasure_ae_graph (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ) :
    ∀ᵐ p ∂weightedGraphMeasure I w, p.1 ∈ baseSlab I ∧ p.2 = du := by
  have emb : MeasurableEmbedding (fun x : Coordinate => (x, du)) :=
    MeasurableEmbedding.id.prodMk_right du
  apply emb.ae_map_iff.mpr
  have hx : ∀ᵐ x ∂(slabVolume I).withDensity (fun x => (slabWeight I w x : ℝ≥0∞)), x ∈ baseSlab I :=
    (withDensity_absolutelyContinuous (slabVolume I) _).ae_le (slabVolume_ae_mem I hI)
  exact hx.mono (fun _ h => ⟨h, rfl⟩)

theorem weightedGraphMeasure_pairing (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u) (F : Coordinate × Coordinate → ℝ) :
    (Integrable F (weightedGraphMeasure I w) ↔
      Integrable (fun x => w (x 0) * F (x, du)) (slabVolume I)) ∧
    (∫ p, F p ∂weightedGraphMeasure I w) = ∫ x, w (x 0) * F (x, du) ∂slabVolume I := by
  have emb : MeasurableEmbedding (fun x : Coordinate => (x, du)) :=
    MeasurableEmbedding.id.prodMk_right du
  have hmeas := slabWeight_measurable I hI w hw
  have he : (fun x : Coordinate => (slabWeight I w x : ℝ) • F (x, du)) =ᵐ[slabVolume I]
      fun x => w (x 0) * F (x, du) := by
    filter_upwards [slabVolume_ae_mem I hI] with x hx
    simp only [slabWeight_coe_of_mem I w hn x hx, smul_eq_mul]
  constructor
  · rw [weightedGraphMeasure, emb.integrable_map_iff, integrable_withDensity_iff_integrable_smul hmeas]
    exact integrable_congr he
  · rw [weightedGraphMeasure, emb.integral_map, integral_withDensity_eq_integral_smul hmeas]
    exact integral_congr_ae he

def phaseDomain (I : Set ℝ) : Set (Coordinate × Coordinate) :=
  {p | p.1 ∈ baseSlab I ∧ p.2 ≠ 0}

theorem phaseDomain_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (phaseDomain I) :=
  ((baseSlab_isOpen hI).preimage continuous_fst).inter
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)

def phaseMeasure (I : Set ℝ) (w : ℝ → ℝ) : Measure (phaseDomain I) :=
  (weightedGraphMeasure I w).comap Subtype.val

theorem phaseMeasure_map (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ) :
    (phaseMeasure I w).map Subtype.val = weightedGraphMeasure I w := by
  rw [phaseMeasure, map_comap_subtype_coe (phaseDomain_isOpen hI).measurableSet]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [weightedGraphMeasure_ae_graph I hI w] with p hp
  exact ⟨hp.1, hp.2 ▸ du_ne_zero⟩

theorem trace_tsupport_subset_slab (I : Set ℝ) (b : Coordinate × Coordinate → ℝ)
    (hc : HasCompactSupport b) (hsub : tsupport b ⊆ phaseDomain I) :
    tsupport (fun x => b (x, du)) ⊆ baseSlab I := by
  have h : tsupport (fun x => b (x, du)) ⊆ Prod.fst '' tsupport b := by
    apply closure_minimal _ (hc.image continuous_fst).isClosed
    intro x hx
    exact ⟨(x, du), subset_closure hx, rfl⟩
  intro x hx
  obtain ⟨p, hp, rfl⟩ := h hx
  exact (hsub hp).1

theorem phaseMeasure_ambient_transport (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    (g : Coordinate → CoordinateMetric)
    (hHamilton : ∀ (a : Coordinate → Coordinate → ℝ) (x : Coordinate), x ∈ baseSlab I →
      canonicalHamilton g a x du = -basePartial 1 a x du)
    (b : Coordinate × Coordinate → ℝ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hsub : tsupport b ⊆ phaseDomain I) :
    let H := fun p : phaseDomain I => canonicalHamilton g (fun x ξ => b (x, ξ)) p.val.1 p.val.2
    Integrable H (phaseMeasure I w) ∧ (∫ p, H p ∂phaseMeasure I w) = 0 := by
  let F := fun p : Coordinate × Coordinate =>
    canonicalHamilton g (fun x ξ => b (x, ξ)) p.1 p.2
  let φ := fun x => b (x, du)
  have hflux := weighted_directional_integral_zero I hI w hw φ
    (joint_trace_contDiff b hb) (joint_trace_hasCompactSupport b hc)
    (trace_tsupport_subset_slab I b hc hsub)
  have he : (fun x : Coordinate => w (x 0) * F (x, du)) =ᵐ[slabVolume I]
      fun x => -weightedFlux w φ x := by
    filter_upwards [slabVolume_ae_mem I hI] with x hx
    change w (x 0) * canonicalHamilton g (fun x ξ => b (x, ξ)) x du = _
    rw [hHamilton _ x hx]
    simp [weightedFlux, φ, basePartial]
  have hm := weightedGraphMeasure_pairing I hI w hw hn F
  have hFI := hm.1.mpr (hflux.1.neg.congr he.symm)
  have hF0 : (∫ p, F p ∂weightedGraphMeasure I w) = 0 := by
    rw [hm.2, integral_congr_ae he, integral_neg, hflux.2, neg_zero]
  have emb := MeasurableEmbedding.subtype_coe (phaseDomain_isOpen hI).measurableSet
  rw [← phaseMeasure_map I hI w] at hFI hF0
  exact ⟨emb.integrable_map_iff.mp hFI, (emb.integral_map F).symm.trans hF0⟩

end Burnett.RosenGeneral.Transport

noncomputable section

namespace Burnett.RosenGeneral.Transport

open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open MeasureTheory Set Filter
open scoped ContDiff Topology

def HasLocalSmoothRepresentatives {I : Set ℝ} (f : phaseDomain I → ℝ) : Prop :=
  ∀ p : phaseDomain I, ∃ (U : Set (Coordinate × Coordinate))
    (F : Coordinate × Coordinate → ℝ),
    IsOpen U ∧ p.val ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ q : phaseDomain I, q.val ∈ U → F q.val = f q

def phaseZeroExtension {I : Set ℝ} (f : phaseDomain I → ℝ) (p : Coordinate × Coordinate) : ℝ := by
  classical
  exact if hp : p ∈ phaseDomain I then f ⟨p, hp⟩ else 0

theorem phaseZeroExtension_tsupport_subset_image {I : Set ℝ} (f : phaseDomain I → ℝ)
    (hc : HasCompactSupport f) :
    tsupport (phaseZeroExtension f) ⊆ Subtype.val '' tsupport f := by
  have hcompact : IsCompact (Subtype.val '' tsupport f : Set (Coordinate × Coordinate)) :=
    hc.isCompact.image continuous_subtype_val
  apply closure_minimal _ hcompact.isClosed
  intro p hp
  by_cases hd : p ∈ phaseDomain I
  · have hfp : f ⟨p, hd⟩ ≠ 0 := by
      simpa only [Function.mem_support, phaseZeroExtension, dif_pos hd] using hp
    exact ⟨⟨p, hd⟩, subset_closure hfp, rfl⟩
  · exact False.elim (hp (by simp [phaseZeroExtension, hd]))

theorem phaseZeroExtension_eventuallyEq_representative {I : Set ℝ} (hI : IsOpen I)
    (f : phaseDomain I → ℝ) (p : phaseDomain I)
    (U : Set (Coordinate × Coordinate)) (F : Coordinate × Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : phaseDomain I, q.val ∈ U → F q.val = f q) :
    phaseZeroExtension f =ᶠ[𝓝 p.val] F := by
  filter_upwards [(phaseDomain_isOpen hI).mem_nhds p.property, hU.mem_nhds hpU] with q hq hqU
  rw [phaseZeroExtension, dif_pos hq]
  exact (hrep ⟨q, hq⟩ hqU).symm

theorem phaseZeroExtension_properties {I : Set ℝ} (hI : IsOpen I) (f : phaseDomain I → ℝ)
    (hs : HasLocalSmoothRepresentatives f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (phaseZeroExtension f) ∧ HasCompactSupport (phaseZeroExtension f) ∧
      tsupport (phaseZeroExtension f) ⊆ phaseDomain I := by
  have hsub : tsupport (phaseZeroExtension f) ⊆ phaseDomain I := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := phaseZeroExtension_tsupport_subset_image f hc hp
    exact q.property
  have hcompact : HasCompactSupport (phaseZeroExtension f) :=
    (hc.isCompact.image continuous_subtype_val).of_isClosed_subset isClosed_closure
      (phaseZeroExtension_tsupport_subset_image f hc)
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, hcompact, hsub⟩
  intro p
  by_cases hp : p ∈ phaseDomain I
  · obtain ⟨U, F, hU, hpU, hF, hrep⟩ := hs ⟨p, hp⟩
    exact (hF.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
      (phaseZeroExtension_eventuallyEq_representative hI f ⟨p, hp⟩ U F hU hpU hrep)
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h => hp (hsub h))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coordinate × Coordinate => (0 : ℝ)) p)
      |>.congr_of_eventuallyEq hzero

def intrinsicHamilton {I : Set ℝ} (g : Coordinate → CoordinateMetric)
    (f : phaseDomain I → ℝ) (p : phaseDomain I) : ℝ :=
  canonicalHamilton g (fun x ξ => phaseZeroExtension f (x, ξ)) p.val.1 p.val.2

theorem intrinsicHamilton_eq_representative {I : Set ℝ} (hI : IsOpen I)
    (g : Coordinate → CoordinateMetric) (f : phaseDomain I → ℝ) (p : phaseDomain I)
    (U : Set (Coordinate × Coordinate)) (F : Coordinate × Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : phaseDomain I, q.val ∈ U → F q.val = f q) :
    intrinsicHamilton g f p = canonicalHamilton g (fun x ξ => F (x, ξ)) p.val.1 p.val.2 :=
  Burnett.RosenMultiscale.Transport.TestClass.canonicalHamilton_congr_germ _ _ _ _
    (phaseZeroExtension_eventuallyEq_representative hI f p U F hU hpU hrep)

theorem phaseMeasure_intrinsic_transport (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    (g : Coordinate → CoordinateMetric)
    (hHamilton : ∀ (a : Coordinate → Coordinate → ℝ) (x : Coordinate), x ∈ baseSlab I →
      canonicalHamilton g a x du = -basePartial 1 a x du)
    (f : phaseDomain I → ℝ) (hf : HasLocalSmoothRepresentatives f) (hc : HasCompactSupport f) :
    Integrable (intrinsicHamilton g f) (phaseMeasure I w) ∧
      (∫ p, intrinsicHamilton g f p ∂phaseMeasure I w) = 0 := by
  obtain ⟨hsc, hcc, hsub⟩ := phaseZeroExtension_properties hI f hf hc
  exact phaseMeasure_ambient_transport I hI w hw hn g hHamilton (phaseZeroExtension f) hsc hcc hsub

end Burnett.RosenGeneral.Transport

noncomputable section

namespace Burnett.RosenGeneral.Transport

open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open MeasureTheory Set Filter

theorem phaseMeasure_ae_du (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ) :
    ∀ᵐ p ∂phaseMeasure I w, p.val.2 = du := by
  have h := weightedGraphMeasure_ae_graph I hI w
  rw [← phaseMeasure_map I hI w] at h
  have emb := MeasurableEmbedding.subtype_coe (phaseDomain_isOpen hI).measurableSet
  exact (emb.ae_map_iff.mp h).mono (fun _ hp => hp.2)

theorem phaseMeasure_pairing (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u) (F : Coordinate × Coordinate → ℝ) :
    (Integrable (fun p : phaseDomain I => F p.val) (phaseMeasure I w) ↔
      Integrable (fun x => w (x 0) * F (x, du)) (slabVolume I)) ∧
    (∫ p : phaseDomain I, F p.val ∂phaseMeasure I w) =
      ∫ x, w (x 0) * F (x, du) ∂slabVolume I := by
  have emb := MeasurableEmbedding.subtype_coe (phaseDomain_isOpen hI).measurableSet
  have hm := weightedGraphMeasure_pairing I hI w hw hn F
  rw [← phaseMeasure_map I hI w] at hm
  exact ⟨emb.integrable_map_iff.symm.trans hm.1, (emb.integral_map F).symm.trans hm.2⟩

end Burnett.RosenGeneral.Transport

noncomputable section

namespace Burnett.RosenGeneral.Transport

open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

theorem weightedGraphMeasure_compact_base (I : Set ℝ) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    {K : Set Coordinate} (hK : IsCompact K) (hKs : K ⊆ baseSlab I) :
    weightedGraphMeasure I w (Prod.fst ⁻¹' K) < ∞ := by
  let μ := slabVolume I
  let W := fun x : Coordinate => (slabWeight I w x : ℝ≥0∞)
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hcont : ContinuousOn (fun x : Coordinate => w (x 0)) K :=
    hw.comp (continuous_apply 0).continuousOn (fun x hx => hKs hx)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  have hbound : ∀ᵐ x ∂μ.restrict K, W x ≤ ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem hKmeas] with x hx
    have hle : w (x 0) ≤ C := hC (mem_image_of_mem _ hx)
    change ((slabWeight I w x : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal C
    rw [← ENNReal.ofReal_coe_nnreal, slabWeight_coe_of_mem I w hn x (hKs hx)]
    exact ENNReal.ofReal_le_ofReal hle
  have hvol : μ K < ∞ :=
    (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top
  have hgraph : Measurable (fun x : Coordinate => (x, du)) := measurable_id.prodMk measurable_const
  rw [weightedGraphMeasure, Measure.map_apply hgraph (hKmeas.preimage measurable_fst)]
  change μ.withDensity W K < ∞
  rw [withDensity_apply W hKmeas]
  calc
    (∫⁻ x, W x ∂μ.restrict K) ≤ ∫⁻ _x, ENNReal.ofReal C ∂μ.restrict K :=
      lintegral_mono_ae hbound
    _ = ENNReal.ofReal C * μ K := by rw [lintegral_const, Measure.restrict_apply_univ]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol

theorem phaseMeasure_compact_base (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    {K : Set Coordinate} (hK : IsCompact K) (hKs : K ⊆ baseSlab I) :
    phaseMeasure I w {p : phaseDomain I | p.val.1 ∈ K} < ∞ := by
  have hm : MeasurableSet (Prod.fst ⁻¹' K : Set (Coordinate × Coordinate)) :=
    hK.isClosed.measurableSet.preimage measurable_fst
  change phaseMeasure I w (Subtype.val ⁻¹' (Prod.fst ⁻¹' K)) < ∞
  rw [← Measure.map_apply measurable_subtype_coe hm, phaseMeasure_map I hI w]
  exact weightedGraphMeasure_compact_base I w hw hn hK hKs

theorem phaseMeasure_regular (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u) : (phaseMeasure I w).Regular := by
  letI : LocallyCompactSpace (phaseDomain I) := (phaseDomain_isOpen hI).locallyCompactSpace
  letI : IsFiniteMeasureOnCompacts (phaseMeasure I w) := ⟨fun L hL => by
    let f : phaseDomain I → Coordinate := fun p => p.val.1
    have hproj : IsCompact (f '' L) := hL.image (continuous_fst.comp continuous_subtype_val)
    have hSlab : f '' L ⊆ baseSlab I := by
      rintro x ⟨p, _, rfl⟩
      exact p.property.1
    have hsub : L ⊆ {p : phaseDomain I | p.val.1 ∈ f '' L} := fun p hp =>
      mem_image_of_mem _ hp
    exact (measure_mono hsub).trans_lt (phaseMeasure_compact_base I hI w hw hn hproj hSlab)⟩
  infer_instance

theorem phaseMeasure_closed_graph_carrier (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ) :
    IsClosed {p : phaseDomain I | p.val.2 = du} ∧
      phaseMeasure I w ({p : phaseDomain I | p.val.2 = du}ᶜ) = 0 := by
  refine ⟨isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const, ?_⟩
  exact phaseMeasure_ae_du I hI w

theorem phaseMeasure_closed_null_carrier (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (g : Coordinate → CoordinateMetric) (hnull : ∀ x ∈ baseSlab I, P g x du = 0) :
    ∃ K : Set (phaseDomain I), IsClosed K ∧
      phaseMeasure I w Kᶜ = 0 ∧ ∀ p ∈ K, P g p.val.1 p.val.2 = 0 := by
  obtain ⟨hK, hcarrier⟩ := phaseMeasure_closed_graph_carrier I hI w
  refine ⟨{p | p.val.2 = du}, hK, hcarrier, ?_⟩
  intro p hp
  change p.val.2 = du at hp
  rw [hp]
  exact hnull p.val.1 p.property.1

theorem phaseMeasure_ae_null (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (g : Coordinate → CoordinateMetric) (hnull : ∀ x ∈ baseSlab I, P g x du = 0) :
    ∀ᵐ p ∂phaseMeasure I w, P g p.val.1 p.val.2 = 0 := by
  filter_upwards [phaseMeasure_ae_du I hI w] with p hp
  rw [hp]
  exact hnull p.val.1 p.property.1

theorem phaseMeasure_compact_continuous_fiber_weight (I : Set ℝ) (hI : IsOpen I) (w : ℝ → ℝ)
    (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    {K : Set Coordinate} (hK : IsCompact K) (hKs : K ⊆ baseSlab I)
    (F : Coordinate × Coordinate → ℝ) (hF : ContinuousOn (fun x : Coordinate => F (x, du)) K) :
    ∫⁻ p in {p : phaseDomain I | p.val.1 ∈ K},
      ENNReal.ofReal (F p.val) ∂phaseMeasure I w < ∞ := by
  let Q := {p : phaseDomain I | p.val.1 ∈ K}
  let μ := phaseMeasure I w
  have hQ : MeasurableSet Q :=
    hK.isClosed.measurableSet.preimage (measurable_fst.comp measurable_subtype_coe)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hF
  have hbound : ∀ᵐ p ∂μ.restrict Q, ENNReal.ofReal (F p.val) ≤ ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem hQ, ae_restrict_of_ae (phaseMeasure_ae_du I hI w)] with p hp hd
    have hh : F (p.val.1, du) ≤ C := hC (mem_image_of_mem _ hp)
    change ENNReal.ofReal (F (p.val.1, p.val.2)) ≤ ENNReal.ofReal C
    rw [hd]
    exact ENNReal.ofReal_le_ofReal hh
  calc
    (∫⁻ p, ENNReal.ofReal (F p.val) ∂μ.restrict Q) ≤ ∫⁻ _p, ENNReal.ofReal C ∂μ.restrict Q :=
      lintegral_mono_ae hbound
    _ = ENNReal.ofReal C * μ Q := by rw [lintegral_const, Measure.restrict_apply_univ]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (phaseMeasure_compact_base I hI w hw hn hK hKs)

theorem du_euclidean_norm : ‖(WithLp.toLp 2 du : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [du, coordinateBasis, Pi.single_apply]

theorem phaseMeasure_compact_euclidean_second_moment (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    {K : Set Coordinate} (hK : IsCompact K) (hKs : K ⊆ baseSlab I) :
    (∫⁻ p in {p : phaseDomain I | p.val.1 ∈ K},
      ENNReal.ofReal (‖(WithLp.toLp 2 p.val.2 : EuclideanSpace ℝ (Fin 4))‖ ^ 2)
      ∂phaseMeasure I w) = phaseMeasure I w {p : phaseDomain I | p.val.1 ∈ K} ∧
    phaseMeasure I w {p : phaseDomain I | p.val.1 ∈ K} < ∞ := by
  let Q := {p : phaseDomain I | p.val.1 ∈ K}
  let μ := phaseMeasure I w
  have he : (fun p : phaseDomain I =>
      ENNReal.ofReal (‖(WithLp.toLp 2 p.val.2 : EuclideanSpace ℝ (Fin 4))‖ ^ 2)) =ᵐ[μ.restrict Q]
      fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [ae_restrict_of_ae (phaseMeasure_ae_du I hI w)] with p hp
    simp [hp, du_euclidean_norm]
  refine ⟨?_, phaseMeasure_compact_base I hI w hw hn hK hKs⟩
  change (∫⁻ p, ENNReal.ofReal (‖(WithLp.toLp 2 p.val.2 : EuclideanSpace ℝ (Fin 4))‖ ^ 2)
    ∂μ.restrict Q) = μ Q
  rw [lintegral_congr_ae he, lintegral_one, Measure.restrict_apply_univ]


def auxiliaryCovectorSquare (r : Coordinate → CoordinateMetric)
    (p : Coordinate × Coordinate) : ℝ :=
  dotProduct p.2 (Matrix.mulVec (Burnett.Geometry.InverseField.matrixInverse (r p.1)) p.2)

theorem auxiliaryCovectorSquare_du (r : Coordinate → CoordinateMetric) (x : Coordinate) :
    auxiliaryCovectorSquare r (x, du) = Burnett.Geometry.InverseField.matrixInverse (r x) 0 0 := by
  simp [auxiliaryCovectorSquare, dotProduct, Matrix.mulVec, du, coordinateBasis, Fin.sum_univ_succ]

theorem auxiliaryCovectorSquare_du_continuousOn {K : Set Coordinate}
    (r : Coordinate → CoordinateMetric) (hr : ContinuousOn r K)
    (hpos : ∀ x ∈ K, Matrix.PosDef (r x)) :
    ContinuousOn (fun x : Coordinate => auxiliaryCovectorSquare r (x, du)) K := by
  have hInv : ContinuousOn (fun x => Burnett.Geometry.InverseField.matrixInverse (r x)) K :=
    Burnett.Geometry.InverseField.continuousOn_matrixInverse r K hr
      (fun x hx => (hpos x hx).det_pos.ne')
  have h00 : Continuous fun M : CoordinateMetric => M 0 0 :=
    (continuous_apply 0).comp (continuous_apply 0)
  simpa only [auxiliaryCovectorSquare_du] using h00.comp_continuousOn hInv

theorem phaseMeasure_compact_auxiliary_second_moment (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    {K : Set Coordinate} (hK : IsCompact K) (hKs : K ⊆ baseSlab I)
    (r : Coordinate → CoordinateMetric) (hr : ContinuousOn r (baseSlab I))
    (hpos : ∀ x ∈ baseSlab I, Matrix.PosDef (r x)) :
    ∫⁻ p in {p : phaseDomain I | p.val.1 ∈ K},
      ENNReal.ofReal (auxiliaryCovectorSquare r p.val) ∂phaseMeasure I w < ∞ := by
  exact phaseMeasure_compact_continuous_fiber_weight I hI w hw hn hK hKs
    (auxiliaryCovectorSquare r) (auxiliaryCovectorSquare_du_continuousOn r (hr.mono hKs)
      (fun x hx => hpos x (hKs hx)))

theorem phaseMeasure_eq_zero_of_weight_zero (I : Set ℝ) (w : ℝ → ℝ)
    (hz : ∀ u ∈ I, w u = 0) : phaseMeasure I w = 0 := by
  classical
  have hW : slabWeight I w = 0 := by
    funext x
    by_cases hx : x 0 ∈ I
    · simp [slabWeight, hx, hz _ hx]
    · simp [slabWeight, hx]
  simp [phaseMeasure, weightedGraphMeasure, hW]


theorem phaseAuxiliaryCovectorSquare_pos {I : Set ℝ}
    (r : Coordinate → CoordinateMetric)
    (hpos : ∀ x ∈ baseSlab I, Matrix.PosDef (r x)) (p : phaseDomain I) :
    0 < auxiliaryCovectorSquare r p.val := by
  simpa [auxiliaryCovectorSquare, Burnett.Geometry.InverseField.matrixInverse] using
    (hpos p.val.1 p.property.1).inv.2 p.val.2 p.property.2

theorem phaseMeasure_compact_auxiliary_second_moment_integrable (I : Set ℝ) (hI : IsOpen I)
    (w : ℝ → ℝ) (hw : ContinuousOn w I) (hn : ∀ u ∈ I, 0 ≤ w u)
    {K : Set Coordinate} (hK : IsCompact K) (hKs : K ⊆ baseSlab I)
    (r : Coordinate → CoordinateMetric) (hr : ContinuousOn r (baseSlab I))
    (hpos : ∀ x ∈ baseSlab I, Matrix.PosDef (r x)) :
    IntegrableOn (fun p : phaseDomain I => auxiliaryCovectorSquare r p.val)
      {p : phaseDomain I | p.val.1 ∈ K} (phaseMeasure I w) := by
  have hnonneg : 0 ≤ᵐ[(phaseMeasure I w).restrict {p : phaseDomain I | p.val.1 ∈ K}]
      (fun p : phaseDomain I => auxiliaryCovectorSquare r p.val) :=
    Eventually.of_forall (fun p => (phaseAuxiliaryCovectorSquare_pos r hpos p).le)
  classical
  let Q := {p : phaseDomain I | p.val.1 ∈ K}
  let μ := (phaseMeasure I w).restrict Q
  let g := fun x : Coordinate => auxiliaryCovectorSquare r (x, du)
  let ψ := K.piecewise g (fun _ => 0)
  have hproj : Measurable (fun p : phaseDomain I => p.val.1) :=
    measurable_fst.comp measurable_subtype_coe
  have hQ : MeasurableSet Q := hK.isClosed.measurableSet.preimage hproj
  have hcont : ContinuousOn g K :=
    auxiliaryCovectorSquare_du_continuousOn r (hr.mono hKs) (fun x hx => hpos x (hKs hx))
  have hψ : Measurable ψ :=
    hcont.measurable_piecewise continuous_const.continuousOn hK.isClosed.measurableSet
  have he : (fun p : phaseDomain I => auxiliaryCovectorSquare r p.val) =ᵐ[μ]
      (fun p => ψ p.val.1) := by
    filter_upwards [ae_restrict_mem hQ, ae_restrict_of_ae (phaseMeasure_ae_du I hI w)] with p hp hd
    change p.val.1 ∈ K at hp
    change auxiliaryCovectorSquare r (p.val.1, p.val.2) = ψ p.val.1
    rw [hd]
    simp [ψ, g, hp]
  have hm : AEStronglyMeasurable (fun p : phaseDomain I => auxiliaryCovectorSquare r p.val) μ :=
    (hψ.comp hproj).aestronglyMeasurable.congr he.symm
  exact (lintegral_ofReal_ne_top_iff_integrable hm hnonneg).mp
    (phaseMeasure_compact_auxiliary_second_moment I hI w hw hn hK hKs r hr hpos).ne

end Burnett.RosenGeneral.Transport
