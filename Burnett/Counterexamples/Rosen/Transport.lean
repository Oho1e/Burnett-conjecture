import Burnett.Counterexamples.Rosen.Kinetic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Rosen multiscale example

The full phase-space measure and its transport integral in both coordinate systems.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale.Transport.Fubini
open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology

abbrev Spatial := Fin 3 → ℝ

def assembleL : (ℝ × Spatial) ≃L[ℝ] Coordinate :=
  Fin.consEquivL ℝ (fun _ : Fin 4 => ℝ)

def assemble (p : ℝ × Spatial) : Coordinate := assembleL p

def baseProductMeasure : Measure (ℝ × Spatial) :=
  (volume.restrict rosenInterval).prod (volume : Measure Spatial)

theorem assemble_eq_cons (p : ℝ × Spatial) : assemble p = Fin.cons p.1 p.2 := rfl

theorem assemble_zero (p : ℝ × Spatial) : assemble p 0 = p.1 := rfl

theorem assemble_succ (p : ℝ × Spatial) (i : Fin 3) :
    assemble p i.succ = p.2 i := rfl

theorem assemble_eq_measurableInverse :
    assemble = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm := by
  funext p
  simp [assemble_eq_cons, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]

theorem assemble_measurePreserving_all :
    MeasurePreserving assemble
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) (volume : Measure Coordinate) := by
  rw [assemble_eq_measurableInverse]
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm

theorem assemble_measurePreserving :
    MeasurePreserving assemble baseProductMeasure coordinateLebesgue := by
  have hs : MeasurableSet {x : Coordinate | x 0 ∈ rosenInterval} :=
    isOpen_Ioo.measurableSet.preimage (measurable_pi_apply 0)
  have h := assemble_measurePreserving_all.restrict_preimage hs
  have he : assemble ⁻¹' {x : Coordinate | x 0 ∈ rosenInterval} =
      rosenInterval ×ˢ (Set.univ : Set Spatial) := by
    ext p
    simp only [mem_preimage, mem_setOf_eq, assemble_zero, mem_prod, mem_univ, and_true]
  rw [he, ← Measure.restrict_prod_eq_prod_univ] at h
  exact h

theorem map_assemble_baseProductMeasure :
    Measure.map assemble baseProductMeasure = coordinateLebesgue :=
  assemble_measurePreserving.map_eq

theorem integral_coordinateLebesgue_eq_product (F : Coordinate → ℝ) :
    (∫ x, F x ∂coordinateLebesgue) =
      ∫ p, F (assemble p) ∂baseProductMeasure := by
  have h := assemble_measurePreserving.integral_comp
    (by rw [assemble_eq_measurableInverse]; exact
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm.measurableEmbedding) F
  exact h.symm


def tailL : Coordinate →L[ℝ] Spatial :=
  (ContinuousLinearMap.snd ℝ ℝ Spatial).comp assembleL.symm.toContinuousLinearMap

theorem tailL_assemble (p : ℝ × Spatial) : tailL (assemble p) = p.2 := by
  simp [tailL, assemble]

def traceSlice (φ : Coordinate → ℝ) (u : ℝ) (s : Spatial) : ℝ :=
  φ (assemble (u, s))

theorem traceSlice_contDiff (φ : Coordinate → ℝ) (hφ : ContDiff ℝ ∞ φ) (u : ℝ) :
    ContDiff ℝ ∞ (traceSlice φ u) := by
  have hi : ContDiff ℝ ∞ (fun s : Spatial => (u, s)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [traceSlice, assemble, Function.comp_def] using
    hφ.comp (assembleL.contDiff.comp hi)

theorem traceSlice_hasCompactSupport (φ : Coordinate → ℝ)
    (hc : HasCompactSupport φ) (u : ℝ) :
    HasCompactSupport (traceSlice φ u) := by
  apply HasCompactSupport.intro (hc.image tailL.continuous)
  intro s hs
  change φ (assemble (u, s)) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  apply hs
  exact ⟨assemble (u, s), hx, tailL_assemble (u, s)⟩

theorem traceSlice_fderiv (φ : Coordinate → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (u : ℝ) (s : Spatial) :
    fderiv ℝ (traceSlice φ u) s (Pi.single (0 : Fin 3) 1) =
      fderiv ℝ φ (assemble (u, s)) (coordinateBasis 1) := by
  have hc : HasFDerivAt (fun _ : Spatial => u) (0 : Spatial →L[ℝ] ℝ) s :=
    hasFDerivAt_const u s
  have hi : HasFDerivAt (fun y : Spatial => y) (ContinuousLinearMap.id ℝ Spatial) s :=
    hasFDerivAt_id s
  have ha := assembleL.hasFDerivAt.comp s (hc.prodMk hi)
  have hd := ((hφ.differentiable (by simp)).differentiableAt).hasFDerivAt.comp s ha
  simp only [Function.comp_def] at hd
  unfold traceSlice assemble
  rw [hd.fderiv]
  change fderiv ℝ φ (assembleL (u, s))
      (assembleL (0, (Pi.single (0 : Fin 3) 1 : Spatial))) =
    fderiv ℝ φ (assembleL (u, s)) (coordinateBasis 1)
  have hv : assembleL (0, (Pi.single (0 : Fin 3) 1 : Spatial)) = coordinateBasis 1 := by
    ext i
    fin_cases i <;> rfl
  rw [hv]

theorem integral_traceSlice_directional_zero (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (u : ℝ) :
    (∫ s : Spatial, fderiv ℝ φ (assemble (u, s)) (coordinateBasis 1)) = 0 := by
  have hs := traceSlice_contDiff φ hφ u
  have hcs := traceSlice_hasCompactSupport φ hc u
  have hD : Continuous
      (fun s : Spatial => fderiv ℝ (traceSlice φ u) s (Pi.single (0 : Fin 3) 1)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiD : Integrable
      (fun s : Spatial => fderiv ℝ (traceSlice φ u) s (Pi.single (0 : Fin 3) 1))
      (volume : Measure Spatial) := hD.integrable_of_hasCompactSupport
    (hcs.fderiv_apply ℝ (Pi.single (0 : Fin 3) 1))
  have hi : Integrable (traceSlice φ u) (volume : Measure Spatial) :=
    hs.continuous.integrable_of_hasCompactSupport hcs
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Spatial)) (f := fun _ : Spatial => (1 : ℝ))
    (g := traceSlice φ u) (v := Pi.single (0 : Fin 3) 1)
    (by simp) (by simpa using hiD) (by simpa using hi)
    (differentiable_const (1 : ℝ)) (hs.differentiable (by simp))
  simp only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul,
    integral_zero, neg_zero] at hibp
  simpa only [traceSlice_fderiv φ hφ u] using hibp

def commonFlux (φ : Coordinate → ℝ) (x : Coordinate) : ℝ :=
  -2 * (Real.cos (x 0))^2 * fderiv ℝ φ x (coordinateBasis 1)

theorem commonFlux_continuous (φ : Coordinate → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (commonFlux φ) := by
  have hD : Continuous (fun x : Coordinate => fderiv ℝ φ x (coordinateBasis 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (continuous_const.mul ((Real.continuous_cos.comp (continuous_apply 0)).pow 2)).mul hD

theorem commonFlux_hasCompactSupport (φ : Coordinate → ℝ) (hc : HasCompactSupport φ) :
    HasCompactSupport (commonFlux φ) :=
  (hc.fderiv_apply ℝ (coordinateBasis 1)).mul_left

theorem commonFlux_integrable_all (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (commonFlux φ) (volume : Measure Coordinate) :=
  (commonFlux_continuous φ hφ).integrable_of_hasCompactSupport
    (commonFlux_hasCompactSupport φ hc)

theorem commonFlux_integrable (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (commonFlux φ) coordinateLebesgue :=
  (commonFlux_integrable_all φ hφ hc).mono_measure Measure.restrict_le_self

theorem commonFlux_product_integrable (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun p : ℝ × Spatial => commonFlux φ (assemble p)) baseProductMeasure := by
  have hh : Continuous (fun p : ℝ × Spatial => commonFlux φ (assemble p)) :=
    (commonFlux_continuous φ hφ).comp assembleL.continuous
  have hc' : HasCompactSupport (fun p : ℝ × Spatial => commonFlux φ (assemble p)) :=
    (commonFlux_hasCompactSupport φ hc).comp_homeomorph assembleL.toHomeomorph
  have hi : Integrable (fun p : ℝ × Spatial => commonFlux φ (assemble p))
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) :=
    hh.integrable_of_hasCompactSupport hc'
  apply hi.mono_measure
  rw [baseProductMeasure, Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_le_self

theorem commonFlux_product_integral_zero (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p : ℝ × Spatial, commonFlux φ (assemble p) ∂baseProductMeasure) = 0 := by
  rw [baseProductMeasure, integral_prod _ (commonFlux_product_integrable φ hφ hc)]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  simp only [commonFlux, assemble_zero, Pi.zero_apply]
  rw [integral_const_mul, integral_traceSlice_directional_zero φ hφ hc u, mul_zero]

theorem commonFlux_integral_zero (φ : Coordinate → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, commonFlux φ x ∂coordinateLebesgue) = 0 := by
  rw [integral_coordinateLebesgue_eq_product]
  exact commonFlux_product_integral_zero φ hφ hc



theorem pulled_density_eq_commonFlux (a : Coordinate → Coordinate → ℝ)
    (x : Coordinate) (hx : x 0 ∈ rosenInterval) :
    pulledLimitDensity x *
        canonicalHamilton (pulledRosenField Real.cos (fun _ => 0)) a x du =
      commonFlux (fun y => a y du) x := by
  rw [canonicalHamilton_pulled_cos_du a x hx]
  simp only [pulledLimitDensity, commonFlux, basePartial]
  have hb := (cos_pos_on_original_interval (x 0) hx).ne'
  calc
    _ = -2 * (Real.cos (x 0))^2 *
        (Real.cos (x 0) * (Real.cos (x 0))⁻¹) *
        fderiv ℝ (fun y => a y du) x (coordinateBasis 1) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hb, mul_one]

theorem original_density_eq_commonFlux (a : Coordinate → Coordinate → ℝ)
    (x : Coordinate) (hx : x 0 ∈ rosenInterval) :
    originalLimitDensity x *
        canonicalHamilton (originalRosenField Real.cos (fun _ => 0)) a x du =
      commonFlux (fun y => a y du) x := by
  rw [canonicalHamilton_original_cos_du a x hx]
  simp only [originalLimitDensity, commonFlux, basePartial]
  ring

theorem pulled_density_transport_of_compact_trace (a : Coordinate → Coordinate → ℝ)
    (ha : ContDiff ℝ ∞ (fun x => a x du))
    (hc : HasCompactSupport (fun x => a x du)) :
    Integrable (fun x => pulledLimitDensity x *
      canonicalHamilton (pulledRosenField Real.cos (fun _ => 0)) a x du) coordinateLebesgue ∧
    (∫ x, pulledLimitDensity x *
      canonicalHamilton (pulledRosenField Real.cos (fun _ => 0)) a x du
        ∂coordinateLebesgue) = 0 := by
  have hs : MeasurableSet {x : Coordinate | x 0 ∈ rosenInterval} :=
    isOpen_Ioo.measurableSet.preimage (measurable_pi_apply 0)
  have hmem : ∀ᵐ x ∂coordinateLebesgue, x 0 ∈ rosenInterval :=
    ae_restrict_mem hs
  have he : (fun x => pulledLimitDensity x *
      canonicalHamilton (pulledRosenField Real.cos (fun _ => 0)) a x du) =ᵐ[coordinateLebesgue]
      commonFlux (fun x => a x du) := by
    filter_upwards [hmem] with x hx
    exact pulled_density_eq_commonFlux a x hx
  exact ⟨(commonFlux_integrable _ ha hc).congr he.symm,
    (integral_congr_ae he).trans (commonFlux_integral_zero _ ha hc)⟩

theorem original_density_transport_of_compact_trace (a : Coordinate → Coordinate → ℝ)
    (ha : ContDiff ℝ ∞ (fun x => a x du))
    (hc : HasCompactSupport (fun x => a x du)) :
    Integrable (fun x => originalLimitDensity x *
      canonicalHamilton (originalRosenField Real.cos (fun _ => 0)) a x du) coordinateLebesgue ∧
    (∫ x, originalLimitDensity x *
      canonicalHamilton (originalRosenField Real.cos (fun _ => 0)) a x du
        ∂coordinateLebesgue) = 0 := by
  have hs : MeasurableSet {x : Coordinate | x 0 ∈ rosenInterval} :=
    isOpen_Ioo.measurableSet.preimage (measurable_pi_apply 0)
  have hmem : ∀ᵐ x ∂coordinateLebesgue, x 0 ∈ rosenInterval :=
    ae_restrict_mem hs
  have he : (fun x => originalLimitDensity x *
      canonicalHamilton (originalRosenField Real.cos (fun _ => 0)) a x du) =ᵐ[coordinateLebesgue]
      commonFlux (fun x => a x du) := by
    filter_upwards [hmem] with x hx
    exact original_density_eq_commonFlux a x hx
  exact ⟨(commonFlux_integrable _ ha hc).congr he.symm,
    (integral_congr_ae he).trans (commonFlux_integral_zero _ ha hc)⟩

theorem joint_trace_contDiff (b : Coordinate × Coordinate → ℝ) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun x => b (x, du)) :=
  hb.comp (contDiff_id.prodMk contDiff_const)

theorem joint_trace_hasCompactSupport (b : Coordinate × Coordinate → ℝ)
    (hc : HasCompactSupport b) :
    HasCompactSupport (fun x => b (x, du)) := by
  apply HasCompactSupport.intro (hc.image continuous_fst)
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hpoint
  exact hx ⟨(x, du), hpoint, rfl⟩

theorem pulled_density_transport_of_joint_compact_test
    (b : Coordinate × Coordinate → ℝ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) :
    Integrable (fun x => pulledLimitDensity x *
      canonicalHamilton (pulledRosenField Real.cos (fun _ => 0))
        (fun y ξ => b (y, ξ)) x du) coordinateLebesgue ∧
    (∫ x, pulledLimitDensity x *
      canonicalHamilton (pulledRosenField Real.cos (fun _ => 0))
        (fun y ξ => b (y, ξ)) x du ∂coordinateLebesgue) = 0 :=
  pulled_density_transport_of_compact_trace (fun y ξ => b (y, ξ))
    (joint_trace_contDiff b hb) (joint_trace_hasCompactSupport b hc)

theorem original_density_transport_of_joint_compact_test
    (b : Coordinate × Coordinate → ℝ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) :
    Integrable (fun x => originalLimitDensity x *
      canonicalHamilton (originalRosenField Real.cos (fun _ => 0))
        (fun y ξ => b (y, ξ)) x du) coordinateLebesgue ∧
    (∫ x, originalLimitDensity x *
      canonicalHamilton (originalRosenField Real.cos (fun _ => 0))
        (fun y ξ => b (y, ξ)) x du ∂coordinateLebesgue) = 0 :=
  original_density_transport_of_compact_trace (fun y ξ => b (y, ξ))
    (joint_trace_contDiff b hb) (joint_trace_hasCompactSupport b hc)

theorem originalRosen_volume (B ψ : ℝ → ℝ) (x : Coordinate) :
    Real.sqrt |(originalRosenField B ψ x).det| = (B (x 0))^2 := by
  rw [originalRosenField_eq_block, pulledMetricAt_det]
  simp only [one_pow, one_mul]
  rw [screen_product]
  have he : (B (x 0))^4 = ((B (x 0))^2)^2 := by ring
  rw [abs_neg, he, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]

theorem originalLimitDensity_eq_actual_volume (x : Coordinate) :
    originalLimitDensity x =
      2 * Real.sqrt |(originalRosenField Real.cos (fun _ => 0) x).det| := by
  rw [originalRosen_volume]
  rfl

theorem pulledLimitDensity_eq_actual_volume (x : Coordinate)
    (hx : x 0 ∈ rosenInterval) :
    pulledLimitDensity x =
      2 * Real.sqrt |(pulledRosenField Real.cos (fun _ => 0) x).det| := by
  have hv := pulledRosen_volume (Real.cos (x 0)) (deriv Real.cos (x 0)) (x 1) 0
    (cos_pos_on_original_interval (x 0) hx)
  change 2 * (Real.cos (x 0))^3 =
    2 * Real.sqrt |(pulledMetricAt (Real.cos (x 0)) (deriv Real.cos (x 0)) (x 1)
      (screenX (Real.cos (x 0)) 0) (screenZ (Real.cos (x 0)) 0)).det|
  rw [hv]


end Burnett.RosenMultiscale.Transport.Fubini

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open Filter MeasureTheory Set
open scoped ContDiff Topology ENNReal

def rosenPhaseDomain : Set (Coordinate × Coordinate) := {p | p.1 0 ∈ rosenInterval ∧ p.2 ≠ 0}

theorem rosenPhaseDomain_isOpen : IsOpen rosenPhaseDomain :=
  (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_fst)).inter
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)

def rosenPhaseMeasure (pulled : Bool) : Measure rosenPhaseDomain :=
  (rosenKineticMeasure pulled).comap Subtype.val

theorem rosenPhaseMeasure_map (pulled : Bool) : (rosenPhaseMeasure pulled).map Subtype.val = rosenKineticMeasure pulled := by
  rw [rosenPhaseMeasure, map_comap_subtype_coe rosenPhaseDomain_isOpen.measurableSet]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [rosenKineticMeasure_ae_nonzero_null pulled] with p hp
  exact ⟨hp.1, hp.2.1⟩

theorem rosenPhaseMeasure_regular (pulled : Bool) : (rosenPhaseMeasure pulled).Regular := by
  letI : IsFiniteMeasureOnCompacts (rosenKineticMeasure pulled) := ⟨fun K hK => by
    have hbase := rosenKineticMeasure_compact_base pulled (hK.image continuous_fst)
    have hsub : K ⊆ Prod.fst ⁻¹' (Prod.fst '' K) := fun p hp => ⟨p, hp, rfl⟩
    exact (measure_mono hsub).trans_lt hbase⟩
  exact Measure.Regular.comap' _ rosenPhaseDomain_isOpen.isOpenEmbedding_subtypeVal

theorem rosenPhaseMeasure_ne_zero (pulled : Bool) : rosenPhaseMeasure pulled ≠ 0 := by
  intro h
  have hmap := rosenPhaseMeasure_map pulled
  rw [h, Measure.map_zero] at hmap
  exact rosenKineticMeasure_ne_zero pulled hmap.symm

theorem rosenKineticMeasure_transports_compact_test (pulled : Bool) (b : Coordinate × Coordinate → ℝ)
    (hb : ContDiff ℝ ∞ b) (hcompact : HasCompactSupport b) :
    let H := fun p : Coordinate × Coordinate => canonicalHamilton (rosenLimitMetric pulled)
      (fun x ξ => b (x, ξ)) p.1 p.2
    Integrable H (rosenKineticMeasure pulled) ∧ (∫ p, H p ∂rosenKineticMeasure pulled) = 0 := by
  have h := rosenKineticMeasure_transport_pairing pulled (fun x ξ => b (x, ξ))
  cases pulled
  · have hf := Fubini.original_density_transport_of_joint_compact_test b hb hcompact
    exact ⟨h.1.mpr hf.1, h.2.trans hf.2⟩
  · have hf := Fubini.pulled_density_transport_of_joint_compact_test b hb hcompact
    exact ⟨h.1.mpr hf.1, h.2.trans hf.2⟩

theorem rosenPhaseMeasure_transports_compact_test (pulled : Bool) (b : Coordinate × Coordinate → ℝ)
    (hb : ContDiffOn ℝ ∞ b rosenPhaseDomain) (hcompact : HasCompactSupport b)
    (hsupport : tsupport b ⊆ rosenPhaseDomain) :
    let H := fun p : rosenPhaseDomain => canonicalHamilton (rosenLimitMetric pulled)
      (fun x ξ => b (x, ξ)) p.1.1 p.1.2
    Integrable H (rosenPhaseMeasure pulled) ∧ (∫ p, H p ∂rosenPhaseMeasure pulled) = 0 := by
  have hb' : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ rosenPhaseDomain
    · exact hb.contDiffAt (rosenPhaseDomain_isOpen.mem_nhds hx)
    · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun hs => hx (hsupport hs))
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coordinate × Coordinate => (0 : ℝ)) x)
        |>.congr_of_eventuallyEq hzero
  have h := rosenKineticMeasure_transports_compact_test pulled b hb' hcompact
  rw [← rosenPhaseMeasure_map pulled] at h
  have hcoe : Measurable (Subtype.val : rosenPhaseDomain → Coordinate × Coordinate) := measurable_subtype_coe
  exact ⟨(integrable_map_measure h.1.aestronglyMeasurable hcoe.aemeasurable).mp h.1,
    (integral_map hcoe.aemeasurable h.1.aestronglyMeasurable).symm.trans h.2⟩

end Burnett.RosenMultiscale.Transport
