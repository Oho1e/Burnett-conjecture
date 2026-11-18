import Burnett.Counterexamples.Rosen.Einstein
import Burnett.Counterexamples.Rosen.TestClass

/-!
# Rosen multiscale example

The same explicit sequence satisfies the metric, coordinate and scale conclusions.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open scoped ContDiff

abbrev rosenExamplePhase (n : ℕ) : ℝ → ℝ := phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))

abbrev rosenExampleClosedInterval : Set ℝ := Icc (-(1 / 4) : ℝ) (1 / 4)

abbrev rosenExampleOpenInterval : Set ℝ := Ioo (-(1 / 4) : ℝ) (1 / 4)

abbrev rosenExampleExtension : Set ℝ := Ioo (-(1 / 3) : ℝ) (1 / 3)

def rosenExampleSlab (R : ℝ) : Set (Fin 4 → ℝ) :=
  {x | x 0 ∈ rosenExampleClosedInterval ∧ |x 1| ≤ R}

/-- One amplitude sequence gives both exact coordinate expressions. -/
structure RosenMultiscaleSequence (B : ℕ → ℝ → ℝ) : Prop where
  initial : ∀ n, B n 0 = 1 ∧ deriv (B n) 0 = 0
  ode : ∀ n, ContDiffOn ℝ ∞ (B n) rosenExampleExtension ∧ ∀ u ∈ rosenExampleExtension,
    deriv (deriv (B n)) u = -((deriv (rosenExamplePhase n) u)^2 * B n u)
  amplitudeBounds : ∀ n u, u ∈ rosenExampleClosedInterval →
    0 < Real.cos (2 * u) ∧ Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧
      |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4
  amplitudeLimit : TendstoUniformlyOn B Real.cos atTop rosenExampleClosedInterval ∧
    TendstoUniformlyOn (fun n => deriv (B n)) (deriv Real.cos) atTop rosenExampleClosedInterval
  metricSmooth : ∀ n pulled i j, ContDiffOn ℝ ∞
    (fun x => rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n) x i j)
      {x | x 0 ∈ rosenExampleOpenInterval}
  metricLorentz : ∀ n (pulled : Bool) (x : Fin 4 → ℝ), x 0 ∈ rosenExampleOpenInterval →
    let G := rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n) x
    ∃ E : CoordinateMetric, E.det ≠ 0 ∧ E.transpose * G * E = rosenStandardLorentz
  metricLimits : ∀ (pulled : Bool) (R : ℝ), 0 ≤ R →
    TendstoUniformlyOn
      (fun n (x : Fin 4 → ℝ) (i j : Fin 4) => rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n) x i j)
      (fun (x : Fin 4 → ℝ) (i j : Fin 4) => rosenMetricInCoordinates pulled Real.cos (fun _ => 0) x i j)
      atTop (rosenExampleSlab R)
  firstDerivativeBounds : ∀ (pulled : Bool) (R : ℝ), 0 ≤ R →
    ∀ (n : ℕ) (x : Fin 4 → ℝ), x ∈ rosenExampleSlab R →
      ∀ i j k : Fin 4, ∃ d : ℝ,
        HasDerivAt (fun t => rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n)
          (Function.update x k t) i j) d (x k) ∧ |d| ≤ 8 * R + 2 + 6 * Real.exp 4
  chart : ∀ n,
    let slab : Set (Fin 4 → ℝ) := {x | x 0 ∈ rosenExampleOpenInterval}
    MapsTo (rosenCoordinates (B n)) slab slab ∧ MapsTo (inverseRosenCoordinates (B n)) slab slab ∧
      InvOn (inverseRosenCoordinates (B n)) (rosenCoordinates (B n)) slab slab ∧
      ContDiffOn ℝ ∞ (rosenCoordinates (B n)) slab ∧ ContDiffOn ℝ ∞ (inverseRosenCoordinates (B n)) slab
  pullbackAndSource : ∀ n (x : Fin 4 → ℝ), x 0 ∈ rosenExampleClosedInterval →
    let J := coordinateJacobian (rosenCoordinates (B n)) x
    J.transpose * originalRosenField (B n) (rosenExamplePhase n) (rosenCoordinates (B n) x) * J =
      pulledRosenField (B n) (rosenExamplePhase n) x ∧ ∀ i, contractedSource (B n) (rosenExamplePhase n) x i = 0
  vacuum : ∀ (n : ℕ) (x : CoordinateSpace), x 0 ∈ rosenExampleOpenInterval →
    ∀ i j : Index, coordinateRicci (computedConnection (originalRosenBilinear (B n) (rosenExamplePhase n))) x i j = 0 ∧
      coordinateRicci (computedConnection (pulledScreenBilinear (B n)
        (fun u => screenX (B n u) (rosenExamplePhase n u))
        (fun u => screenZ (B n u) (rosenExamplePhase n u)))) x i j = 0
  quantitativeScale : ∀ (pulled : Bool) (left right : ℝ), left < 0 → 0 < right →
    Icc left right ⊆ rosenExampleClosedInterval →
    let F := rosenMetricInCoordinates pulled
    let μ := volume.restrict (rosenScaleBox left right)
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((Real.cos (1/2))^2 / (2 * ((n : ℝ) + 1))) ≤ eLpNormEssSup
        (fun x => ‖(fun i j => F (B n) (rosenExamplePhase n) x i j - F Real.cos (fun _ => 0) x i j)‖) μ ∧
      ENNReal.ofReal (2 * Real.exp (-4) * (Real.cos (1/2))^2 * Real.exp ((n : ℝ) + 1) - 42 * Real.exp 4) ≤
        eLpNormEssSup (fun x => ‖rosenCoordinateSecondPartials (F (B n) (rosenExamplePhase n)) x‖) μ
  noCommonScale : ∀ (pulled : Bool) (left right : ℝ), left < 0 → 0 < right →
    Icc left right ⊆ rosenExampleClosedInterval →
    let F := rosenMetricInCoordinates pulled
    let μ := volume.restrict (rosenScaleBox left right)
    ¬ ∃ δ : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      0 < δ n ∧
      eLpNormEssSup (fun x => ‖(fun i j => F (B n) (rosenExamplePhase n) x i j - F Real.cos (fun _ => 0) x i j)‖) μ ≤
        ENNReal.ofReal (δ n) ∧
      eLpNormEssSup (fun x => ‖rosenCoordinateSecondPartials (F (B n) (rosenExamplePhase n)) x‖) μ ≤
        ENNReal.ofReal (C / δ n)

theorem exists_rosen_multiscale_sequence : ∃ B, RosenMultiscaleSequence B := by
  obtain ⟨B, h0, h0', hs, ho, hb, hlim, hlim', hcoord, hc0, hc1, hpull, hvac, _⟩ :=
    exists_rosen_multiscale_vacuum_geometry
  have hsub : rosenExampleOpenInterval ⊆ rosenExampleExtension := by
    intro u hu
    exact ⟨lt_trans (by norm_num) hu.1, lt_trans hu.2 (by norm_num)⟩
  have hBu (n : ℕ) : ContDiffOn ℝ ∞ (B n) rosenExampleOpenInterval := (hs n).mono hsub
  have hBn (n : ℕ) (u : ℝ) (hu : u ∈ rosenExampleOpenInterval) : B n u ≠ 0 := by
    obtain ⟨hcos, hB, _⟩ := hb n u ⟨hu.1.le, hu.2.le⟩
    exact (hcos.trans_le hB).ne'
  have hB2 (n : ℕ) : ContDiffOn ℝ 2 (B n) rosenExampleExtension := (contDiffOn_infty.mp (hs n)) 2
  refine ⟨B, ⟨fun n => ⟨h0 n, h0' n⟩, fun n => ⟨hs n, ho n⟩, hb, ⟨hlim, hlim'⟩,
    ?_, ?_, ?_, ?_, ?_, hcoord, hvac, ?_, ?_⟩⟩
  · intro n pulled i j
    have hψ : ContDiff ℝ ∞ (rosenExamplePhase n) := by
      unfold rosenExamplePhase phase scaledSine
      fun_prop
    have hm := rosenMetricFields_smooth (B n) (rosenExamplePhase n) _ isOpen_Ioo (hBu n) hψ.contDiffOn
    cases pulled
    · exact hm.1 i j
    · exact hm.2 i j
  · intro n pulled x hx
    cases pulled
    · exact originalRosenField_lorentz (B n) (rosenExamplePhase n) x (hBn n _ hx)
    · have hd : DifferentiableAt ℝ (B n) (x 0) :=
        ((hB2 n).contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt (by norm_num)
      exact pulledRosenField_lorentz (B n) (rosenExamplePhase n) x hd (hBn n _ hx)
  · intro pulled R hR
    cases pulled
    · exact hc0.mono (fun _ hx => hx.1)
    · exact (hpull R hR).1
  · intro pulled R hR n x hx i j k
    cases pulled
    · obtain ⟨d, hd, hn⟩ := hc1 n x hx.1 i j k
      exact ⟨d, hd, hn.trans (by linarith)⟩
    · exact (hpull R hR).2 n x hx.1 hx.2 i j k
  · intro n
    have hi := rosenCoordinates_inverses_on_slab (B n) rosenExampleOpenInterval (hBn n)
    have hsmooth := rosenCoordinates_smooth_on_slab (B n) rosenExampleOpenInterval (hBu n) (hBn n)
    exact ⟨hi.1, hi.2.1, hi.2.2, hsmooth.1, hsmooth.2⟩
  · exact rosen_full_metric_essential_lower_bounds B hB2 (fun n u hu => (hb n u hu).2)
  · exact rosen_no_common_full_metric_scale B hB2 (fun n u hu => (hb n u hu).2)

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter Set Matrix
open scoped ContDiff

theorem RosenMultiscaleSequence.on_compact {B : ℕ → ℝ → ℝ} (h : RosenMultiscaleSequence B)
    (pulled : Bool) {K : Set (Fin 4 → ℝ)} (hK : IsCompact K)
    (hspace : K ⊆ {x | x 0 ∈ rosenExampleOpenInterval}) :
    TendstoUniformlyOn
      (fun n (x : Fin 4 → ℝ) (i j : Fin 4) => rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n) x i j)
      (fun (x : Fin 4 → ℝ) (i j : Fin 4) => rosenMetricInCoordinates pulled Real.cos (fun _ => 0) x i j)
      atTop K ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin 4 → ℝ), x ∈ K →
      ∀ i j k : Fin 4, ∃ d : ℝ,
        HasDerivAt (fun t => rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n)
          (Function.update x k t) i j) d (x k) ∧ |d| ≤ C := by
  obtain ⟨R0, hR0⟩ := (hK.image ((continuous_apply (1 : Fin 4)).abs)).bddAbove
  let R := max R0 0
  have hR : 0 ≤ R := le_max_right _ _
  have hslab : K ⊆ rosenExampleSlab R := by
    intro x hx
    have hu := hspace hx
    exact ⟨⟨hu.1.le, hu.2.le⟩, (hR0 (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  exact ⟨(h.metricLimits pulled R hR).mono hslab,
    ⟨8 * R + 2 + 6 * Real.exp 4, by positivity, fun n x hx => h.firstDerivativeBounds pulled R hR n x (hslab hx)⟩⟩

theorem rosen_limit_time_orientation (pulled : Bool) :
    let slab : Set (Fin 4 → ℝ) := {x | x 0 ∈ rosenExampleOpenInterval}
    ∃ T : (Fin 4 → ℝ) → Fin 4 → ℝ, ContDiffOn ℝ ∞ T slab ∧ ∀ x ∈ slab,
      dotProduct (T x) ((rosenMetricInCoordinates pulled Real.cos (fun _ => 0) x).mulVec (T x)) = -2 := by
  cases pulled
  · exact ⟨fun _ => originalRosenTimeDirection, contDiffOn_const,
      fun x _ => originalRosenTimeDirection_norm Real.cos (fun _ => 0) x⟩
  · have hc (u : ℝ) (hu : u ∈ rosenExampleOpenInterval) : Real.cos u ≠ 0 :=
      (Transport.rosenInterval_cos_pos u hu).ne'
    exact ⟨pulledRosenTimeDirection Real.cos,
      pulledRosenTimeDirection_smooth Real.cos rosenExampleOpenInterval isOpen_Ioo Real.contDiff_cos.contDiffOn hc,
      fun x hx => pulledRosenTimeDirection_norm Real.cos (fun _ => 0) x (hc _ hx)⟩

theorem rosen_limit_contracted_source_zero (x : Fin 4 → ℝ) (hx : x 0 ∈ rosenExampleOpenInterval) (i : Fin 4) :
    contractedSource Real.cos (fun _ => 0) x i = 0 :=
  pulledRosen_contractedSource_zero Real.cos (fun _ => 0) x (Real.differentiable_cos (x 0))
    (Transport.rosenInterval_cos_pos _ hx) i

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set Burnett.RicciSymbol
open Transport
open scoped BigOperators ENNReal ContDiff Topology

theorem rosenPhaseMeasure_null (pulled : Bool) :
    ∀ᵐ p ∂(rosenPhaseMeasure pulled), P (rosenLimitMetric pulled) p.1.1 p.1.2 = 0 := by
  have h : ∀ᵐ p ∂((rosenPhaseMeasure pulled).map Subtype.val),
      P (rosenLimitMetric pulled) p.1 p.2 = 0 := by
    rw [rosenPhaseMeasure_map]
    exact (rosenKineticMeasure_ae_nonzero_null pulled).mono fun _ hp => hp.2.2
  exact (MeasurableEmbedding.subtype_coe rosenPhaseDomain_isOpen.measurableSet).ae_map_iff.mp h

theorem rosenPhaseMeasure_compact_second_moment (pulled : Bool) {K : Set Coordinate} (hK : IsCompact K) :
    ∫⁻ p in {p : rosenPhaseDomain | p.1.1 ∈ K},
      ENNReal.ofReal (‖(WithLp.toLp 2 p.1.2 : EuclideanSpace ℝ Index)‖^2) ∂rosenPhaseMeasure pulled < (⊤ : ℝ≥0∞) := by
  let S : Set (Coordinate × Coordinate) := Prod.fst ⁻¹' K
  let e : rosenPhaseDomain → Coordinate × Coordinate := Subtype.val
  let d : Coordinate × Coordinate → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ Index)‖^2)
  have he : Measurable e := measurable_subtype_coe
  have hd : Measurable d := by fun_prop
  have hmap : ((rosenPhaseMeasure pulled).restrict (e ⁻¹' S)).map e = (rosenKineticMeasure pulled).restrict S := by
    rw [← Measure.restrict_map he (hK.isClosed.measurableSet.preimage measurable_fst), rosenPhaseMeasure_map]
  change (∫⁻ p in e ⁻¹' S, d (e p) ∂rosenPhaseMeasure pulled) < (⊤ : ℝ≥0∞)
  rw [← lintegral_map hd he, hmap]
  have heq : d =ᵐ[(rosenKineticMeasure pulled).restrict S]
      fun _ => ENNReal.ofReal (‖(WithLp.toLp 2 du : EuclideanSpace ℝ Index)‖^2) := by
    filter_upwards [ae_restrict_of_ae (rosenKineticMeasure_ae_graph pulled)] with p hp
    simp [d, hp.2]
  rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (rosenKineticMeasure_compact_base pulled hK)

theorem rosenPhaseMeasure_einstein_moment (pulled : Bool) (S : Coordinate → CoordinateMetric)
    (hS : ∀ i j, Continuous (fun x => S x i j) ∧ HasCompactSupport (fun x => S x i j)) :
    let l := fun p : rosenPhaseDomain => ∑ k : Index × Index, S p.1.1 k.1 k.2 * p.1.2 k.1 * p.1.2 k.2
    let r := fun x => ∑ k : Index × Index, S x k.1 k.2 * rosenLimitEinstein pulled x k.1 k.2 *
      Real.sqrt |(rosenLimitMetric pulled x).det|
    Integrable l (rosenPhaseMeasure pulled) ∧ Integrable r coordinateLebesgue ∧
    (∫ p, l p ∂rosenPhaseMeasure pulled) = ∫ x, r x ∂coordinateLebesgue := by
  have h := rosenKineticMeasure_tensor_moment_eq_einstein pulled S hS
  rw [← rosenPhaseMeasure_map pulled] at h
  have hcoe : Measurable (Subtype.val : rosenPhaseDomain → Coordinate × Coordinate) := measurable_subtype_coe
  exact ⟨(integrable_map_measure h.1.aestronglyMeasurable hcoe.aemeasurable).mp h.1, h.2.1,
    (integral_map hcoe.aemeasurable h.1.aestronglyMeasurable).symm.trans h.2.2⟩

/-- The same explicit Radon measure satisfies both full phase-space equations. -/
structure RosenFullKineticLimit (pulled : Bool) : Prop where
  regular : (rosenPhaseMeasure pulled).Regular
  nonzero : rosenPhaseMeasure pulled ≠ 0
  null : ∀ᵐ p ∂(rosenPhaseMeasure pulled), P (rosenLimitMetric pulled) p.1.1 p.1.2 = 0
  scalar : ∀ x : Coordinate, x 0 ∈ rosenInterval → rosenLimitScalarCurvature pulled x = 0
  localSecondMoments : ∀ K : Set Coordinate, IsCompact K →
    ∫⁻ p in {p : rosenPhaseDomain | p.1.1 ∈ K},
      ENNReal.ofReal (‖(WithLp.toLp 2 p.1.2 : EuclideanSpace ℝ Index)‖^2) ∂rosenPhaseMeasure pulled < (⊤ : ℝ≥0∞)
  moment : ∀ S : Coordinate → CoordinateMetric,
    (∀ i j, Continuous (fun x => S x i j) ∧ HasCompactSupport (fun x => S x i j)) →
    let l := fun p : rosenPhaseDomain => ∑ k : Index × Index, S p.1.1 k.1 k.2 * p.1.2 k.1 * p.1.2 k.2
    let r := fun x => ∑ k : Index × Index, S x k.1 k.2 * rosenLimitEinstein pulled x k.1 k.2 *
      Real.sqrt |(rosenLimitMetric pulled x).det|
    Integrable l (rosenPhaseMeasure pulled) ∧ Integrable r coordinateLebesgue ∧
    (∫ p, l p ∂rosenPhaseMeasure pulled) = ∫ x, r x ∂coordinateLebesgue
  transport : ∀ f : rosenPhaseDomain → ℝ, TestClass.HasLocalSmoothRepresentatives f → HasCompactSupport f →
    Integrable (TestClass.intrinsicHamilton pulled f) (rosenPhaseMeasure pulled) ∧
    (∫ p, TestClass.intrinsicHamilton pulled f p ∂rosenPhaseMeasure pulled) = 0

theorem rosen_full_kinetic_limit (pulled : Bool) : RosenFullKineticLimit pulled :=
  ⟨rosenPhaseMeasure_regular pulled, rosenPhaseMeasure_ne_zero pulled, rosenPhaseMeasure_null pulled,
    rosenLimitScalarCurvature_zero pulled, fun _ h => rosenPhaseMeasure_compact_second_moment pulled h,
    rosenPhaseMeasure_einstein_moment pulled, TestClass.intrinsic_compact_test_transport pulled⟩

theorem rosen_multiscale_example :
    (∃ B, RosenMultiscaleSequence B) ∧
    (∀ pulled, RosenFullKineticLimit pulled) ∧
    (∀ x : Coordinate, x 0 ∈ rosenInterval → ∀ i, contractedSource Real.cos (fun _ => 0) x i = 0) ∧
    (∀ n : ℕ, eLpNorm (fun u => (deriv (rosenExamplePhase n) u)^2) ⊤
      (volume.restrict rosenInterval) ≤ ENNReal.ofReal 4) ∧
    ∀ f : ℝ → ℝ, IntegrableOn f rosenInterval →
      (∀ n : ℕ, IntegrableOn (fun u => f u * (deriv (rosenExamplePhase n) u)^2) rosenInterval) ∧
      Tendsto (fun n : ℕ => ∫ u in rosenInterval, f u * (deriv (rosenExamplePhase n) u)^2) atTop
        (𝓝 (∫ u in rosenInterval, f u)) := by
  obtain ⟨hb, hw⟩ := rosen_phase_LInfinity_weakStar
  exact ⟨exists_rosen_multiscale_sequence, rosen_full_kinetic_limit, rosen_limit_contracted_source_zero, hb, hw⟩

end Burnett.RosenMultiscale
