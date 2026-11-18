import Burnett.Counterexamples.Rosen.Transport

/-!
# Rosen multiscale example

The exact compact smooth test class on the open punctured phase domain.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale.Transport.TestClass

open Filter MeasureTheory Set
open scoped ContDiff Topology

/-- Smoothness in the single coordinate chart of the actual open phase domain.
No ambient extension or support requirement is assumed. -/
def HasLocalSmoothRepresentatives (f : rosenPhaseDomain → ℝ) : Prop :=
  ∀ p : rosenPhaseDomain, ∃ (U : Set (Coordinate × Coordinate))
    (F : Coordinate × Coordinate → ℝ),
    IsOpen U ∧ (p : Coordinate × Coordinate) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ q : rosenPhaseDomain, (q : Coordinate × Coordinate) ∈ U → F q.val = f q

/-- The actual zero extension of an intrinsically defined phase test. -/
def phaseZeroExtension (f : rosenPhaseDomain → ℝ) (p : Coordinate × Coordinate) : ℝ := by
  classical
  exact if hp : p ∈ rosenPhaseDomain then f ⟨p, hp⟩ else 0

theorem phaseZeroExtension_on_subtype (f : rosenPhaseDomain → ℝ) (p : rosenPhaseDomain) :
    phaseZeroExtension f p.val = f p := by
  simp [phaseZeroExtension, p.property]

theorem phaseZeroExtension_off_domain (f : rosenPhaseDomain → ℝ)
    {p : Coordinate × Coordinate} (hp : p ∉ rosenPhaseDomain) :
    phaseZeroExtension f p = 0 := by
  simp [phaseZeroExtension, hp]

theorem phaseZeroExtension_support_subset (f : rosenPhaseDomain → ℝ) :
    Function.support (phaseZeroExtension f) ⊆ Subtype.val '' tsupport f := by
  intro p hp
  by_cases hd : p ∈ rosenPhaseDomain
  · refine ⟨⟨p, hd⟩, ?_, rfl⟩
    apply subset_closure
    simpa [Function.mem_support, phaseZeroExtension, hd] using hp
  · exact False.elim (hp (phaseZeroExtension_off_domain f hd))

theorem compact_image_tsupport (f : rosenPhaseDomain → ℝ) (hc : HasCompactSupport f) :
    IsCompact (Subtype.val '' tsupport f : Set (Coordinate × Coordinate)) :=
  hc.isCompact.image continuous_subtype_val

theorem phaseZeroExtension_tsupport_subset_image (f : rosenPhaseDomain → ℝ)
    (hc : HasCompactSupport f) :
    tsupport (phaseZeroExtension f) ⊆ Subtype.val '' tsupport f :=
  closure_minimal (phaseZeroExtension_support_subset f) (compact_image_tsupport f hc).isClosed

theorem phaseZeroExtension_tsupport_subset_domain (f : rosenPhaseDomain → ℝ)
    (hc : HasCompactSupport f) : tsupport (phaseZeroExtension f) ⊆ rosenPhaseDomain := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := phaseZeroExtension_tsupport_subset_image f hc hp
  exact q.property

theorem phaseZeroExtension_hasCompactSupport (f : rosenPhaseDomain → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (phaseZeroExtension f) := by
  exact (compact_image_tsupport f hc).of_isClosed_subset isClosed_closure
    (phaseZeroExtension_tsupport_subset_image f hc)

theorem phaseZeroExtension_eventuallyEq_representative
    (f : rosenPhaseDomain → ℝ) (p : rosenPhaseDomain)
    (U : Set (Coordinate × Coordinate)) (F : Coordinate × Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : rosenPhaseDomain, q.val ∈ U → F q.val = f q) :
    phaseZeroExtension f =ᶠ[𝓝 p.val] F := by
  filter_upwards [rosenPhaseDomain_isOpen.mem_nhds p.property, hU.mem_nhds hpU]
    with q hq hqU
  rw [phaseZeroExtension, dif_pos hq]
  exact (hrep ⟨q, hq⟩ hqU).symm

theorem phaseZeroExtension_contDiff (f : rosenPhaseDomain → ℝ)
    (hs : HasLocalSmoothRepresentatives f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (phaseZeroExtension f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ rosenPhaseDomain
  · obtain ⟨U, F, hU, hpU, hF, hrep⟩ := hs ⟨p, hp⟩
    exact (hF.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
      (phaseZeroExtension_eventuallyEq_representative f ⟨p, hp⟩ U F hU hpU hrep)
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp
      (fun h => hp (phaseZeroExtension_tsupport_subset_domain f hc h))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coordinate × Coordinate => (0 : ℝ)) p)
      |>.congr_of_eventuallyEq hzero

theorem hasLocalSmoothRepresentatives_iff_zeroExtension_contDiff
    (f : rosenPhaseDomain → ℝ) (hc : HasCompactSupport f) :
    HasLocalSmoothRepresentatives f ↔ ContDiff ℝ ∞ (phaseZeroExtension f) := by
  refine ⟨fun hs => phaseZeroExtension_contDiff f hs hc, ?_⟩
  intro hext p
  exact ⟨Set.univ, phaseZeroExtension f, isOpen_univ, mem_univ _, hext.contDiffOn,
    fun q _ => phaseZeroExtension_on_subtype f q⟩

theorem exists_ambient_zero_extension (f : rosenPhaseDomain → ℝ)
    (hs : HasLocalSmoothRepresentatives f) (hc : HasCompactSupport f) :
    ∃ b : Coordinate × Coordinate → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ rosenPhaseDomain ∧
      (∀ p : rosenPhaseDomain, b p.val = f p) ∧
      (∀ p ∉ rosenPhaseDomain, b p = 0) :=
  ⟨phaseZeroExtension f, phaseZeroExtension_contDiff f hs hc,
    phaseZeroExtension_hasCompactSupport f hc, phaseZeroExtension_tsupport_subset_domain f hc,
    phaseZeroExtension_on_subtype f, fun _ hp => phaseZeroExtension_off_domain f hp⟩

theorem phaseZeroExtension_fderiv_eq_representative
    (f : rosenPhaseDomain → ℝ) (p : rosenPhaseDomain)
    (U : Set (Coordinate × Coordinate)) (F : Coordinate × Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : rosenPhaseDomain, q.val ∈ U → F q.val = f q) :
    fderiv ℝ (phaseZeroExtension f) p.val = fderiv ℝ F p.val :=
  (phaseZeroExtension_eventuallyEq_representative f p U F hU hpU hrep).fderiv_eq

theorem canonicalHamilton_congr_germ (g : Coordinate → CoordinateMetric)
    (A B : Coordinate × Coordinate → ℝ) (p : Coordinate × Coordinate)
    (h : A =ᶠ[𝓝 p] B) :
    canonicalHamilton g (fun x ξ => A (x, ξ)) p.1 p.2 =
      canonicalHamilton g (fun x ξ => B (x, ξ)) p.1 p.2 := by
  have hx : (fun x : Coordinate => A (x, p.2)) =ᶠ[𝓝 p.1]
      (fun x => B (x, p.2)) :=
    h.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have hξ : (fun ξ : Coordinate => A (p.1, ξ)) =ᶠ[𝓝 p.2]
      (fun ξ => B (p.1, ξ)) :=
    h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  simp only [canonicalHamilton, basePartial, momentumPartial,
    hx.fderiv_eq, hξ.fderiv_eq]

/-- The intrinsic Hamilton derivative is evaluated by the proved zero extension.
Its value agrees with every local smooth representative. -/
def intrinsicHamilton (pulled : Bool) (f : rosenPhaseDomain → ℝ) (p : rosenPhaseDomain) : ℝ :=
  canonicalHamilton (rosenLimitMetric pulled)
    (fun x ξ => phaseZeroExtension f (x, ξ)) p.val.1 p.val.2

theorem intrinsicHamilton_eq_representative
    (pulled : Bool) (f : rosenPhaseDomain → ℝ) (p : rosenPhaseDomain)
    (U : Set (Coordinate × Coordinate)) (F : Coordinate × Coordinate → ℝ)
    (hU : IsOpen U) (hpU : p.val ∈ U)
    (hrep : ∀ q : rosenPhaseDomain, q.val ∈ U → F q.val = f q) :
    intrinsicHamilton pulled f p = canonicalHamilton (rosenLimitMetric pulled)
      (fun x ξ => F (x, ξ)) p.val.1 p.val.2 :=
  canonicalHamilton_congr_germ _ _ _ _
    (phaseZeroExtension_eventuallyEq_representative f p U F hU hpU hrep)

theorem intrinsic_compact_test_transport (pulled : Bool) (f : rosenPhaseDomain → ℝ)
    (hs : HasLocalSmoothRepresentatives f) (hc : HasCompactSupport f) :
    Integrable (intrinsicHamilton pulled f) (rosenPhaseMeasure pulled) ∧
      (∫ p, intrinsicHamilton pulled f p ∂rosenPhaseMeasure pulled) = 0 := by
  exact rosenPhaseMeasure_transports_compact_test pulled (phaseZeroExtension f)
    (phaseZeroExtension_contDiff f hs hc).contDiffOn
    (phaseZeroExtension_hasCompactSupport f hc)
    (phaseZeroExtension_tsupport_subset_domain f hc)

end Burnett.RosenMultiscale.Transport.TestClass
