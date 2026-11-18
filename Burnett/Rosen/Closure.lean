import Burnett.Rosen.Admissible
import Burnett.Rosen.Einstein
import Burnett.Rosen.WeakLimit

/-!
# General Rosen plane waves

The two-polarization closure and its single explicit full phase-space measure.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenPlaneWave

open MeasureTheory Set Filter Matrix Burnett.RicciSymbol Burnett.RosenScreen
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.CurvatureDifference Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.AuxiliaryConnection
open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open Burnett.RosenGeneralLSC Burnett.RosenGeneral.Transport AdmissibleLocal
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise

/-- The physical local hypotheses in the product chart of a general Rosen sequence. -/
structure ScreenPhysicalSequence (I : Set ℝ) (γn : ℕ → ℝ → Screen) (γ : ℝ → Screen)
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) : Prop where
  limit_smooth : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) I
  sequence_smooth : ∀ n i j, ContDiffOn ℝ ∞ (fun u => γn n u i j) I
  limit_positive : ∀ u ∈ I, (γ u).PosDef
  sequence_positive : ∀ n u, u ∈ I → (γn n u).PosDef
  auxiliary_regular : ∀ i j, ContDiffOn ℝ 1 (fun x => metricComponents r x i j) (screenSlab I)
  auxiliary_positive : ∀ x ∈ screenSlab I, Matrix.PosDef (metricComponents r x)
  convergence : ∀ K : Set CoordinateSpace, IsCompact K → K ⊆ screenSlab I →
    TendstoUniformlyOn (fun n x => norm2 (metricComponents r x)
      (metricComponents (screenBilinear (γn n)) x - metricComponents (screenBilinear γ) x))
      (fun _ => 0) atTop K
  derivative_bound : ∀ K : Set CoordinateSpace, IsCompact K → K ⊆ screenSlab I →
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (fun x => norm3 (metricComponents r x)
        (auxiliaryPerturbationJet r (screenBilinear γ) (screenBilinear (γn n)) x))
          ⊤ ((screenLimitMeasure γ).restrict K) ≤ ENNReal.ofReal D
  vacuum : ∀ n (x : CoordinateSpace), x 0 ∈ I → ∀ i j : Index,
    coordinateRicci (computedConnection (screenBilinear (γn n))) x i j = 0

/-- Vacuum, local uniform convergence and the physical first-derivative bound imply nonnegative density. -/
theorem ScreenPhysicalSequence.density_nonneg {I : Set ℝ} (hI : IsOpen I)
    {γn : ℕ → ℝ → Screen} {γ : ℝ → Screen}
    {r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace} (h : ScreenPhysicalSequence I γn γ r) :
    ∀ u ∈ I, 0 ≤ screenDefectDensity γ u := by
  have hw : LocalC1MatrixPairings I (fun n => screenShear (γn n)) (screenShear γ) := by
    intro l b hlb hK w hw i j
    obtain ⟨hU, C, hC, hD⟩ := screen_local_controls_of_physical_admissible I hI γ γn h.limit_smooth
      h.sequence_smooth h.limit_positive r h.auxiliary_regular h.auxiliary_positive
      h.convergence h.derivative_bound (Icc l b) isCompact_Icc hK
    have he := tendstoUniformlyOn_screen2_iff_entries.mp hU
    have hb (n : ℕ) (a c : Fin 2) (u : ℝ) (hu : u ∈ Icc l b) :
        ‖deriv (fun t => γn n t a c) u‖ ≤ C := by
      rw [Real.norm_eq_abs]
      exact (screenDerivative_entry_abs_le (γn n) u a c).trans (hD n u hu)
    exact tendsto_restrict_Icc_screenS_deriv_mul_test hlb hI hK h.sequence_smooth h.limit_smooth
      h.sequence_positive h.limit_positive he hC hb hw i j
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hv (n : ℕ) (u : ℝ) (hu : u ∈ I) :
      -deriv (traceField (screenShear (γn n))) u = frameEnergy (screenShear (γn n) u) := by
    rw [frameEnergy_eq_nested]
    exact screenVacuum_shearLaw (γn n) I hI (fun i j => (h.sequence_smooth n i j).of_le h2)
      (h.sequence_positive n) (h.vacuum n) u hu
  have hp := limitDensity_nonneg_of_vacuum hI (fun n => screenShear (γn n)) (screenShear γ)
    (fun n => screenS_deriv_entry_contDiffOn (γn n) I hI (h.sequence_smooth n) (h.sequence_positive n))
    (screenS_deriv_entry_contDiffOn γ I hI h.limit_smooth h.limit_positive) hw hv
  simpa only [limitDensity, traceField, frameEnergy_eq_nested, screenDefectDensity] using hp

/-- A single measure on the nonzero phase domain realizes all parts of the full representation. -/
structure ScreenFullKineticRepresentation (I : Set ℝ) (γ : ℝ → Screen)
    (ν : Measure (phaseDomain I)) : Prop where
  regular : ν.Regular
  null_carrier : ∃ K : Set (phaseDomain I), IsClosed K ∧ ν Kᶜ = 0 ∧
    ∀ p ∈ K, P (screenField γ) p.val.1 p.val.2 = 0
  locally_finite_over_base : ∀ K : Set Coordinate, IsCompact K → K ⊆ baseSlab I →
    ν {p : phaseDomain I | p.val.1 ∈ K} < ⊤
  second_moments : ∀ (K : Set Coordinate), IsCompact K → K ⊆ baseSlab I →
    ∀ r : Coordinate → CoordinateMetric, ContinuousOn r (baseSlab I) →
      (∀ x ∈ baseSlab I, (r x).PosDef) →
      (∫⁻ p in {p : phaseDomain I | p.val.1 ∈ K}, ENNReal.ofReal (auxiliaryCovectorSquare r p.val) ∂ν) < ⊤ ∧
      IntegrableOn (fun p : phaseDomain I => auxiliaryCovectorSquare r p.val) {p | p.val.1 ∈ K} ν
  einstein_moments : ∀ S : baseSlab I → CoordinateMetric,
    (∀ i j, HasLocalSmoothBaseTests (fun x => S x i j)) → HasCompactSupport S →
    let l := fun p : phaseDomain I =>
      ∑ k : Index × Index, S (screenPhaseBase p) k.1 k.2 * p.val.2 k.1 * p.val.2 k.2
    let r := fun x : baseSlab I =>
      ∑ k : Index × Index, S x k.1 k.2 * screenEinstein γ x.val k.1 k.2 * Real.sqrt |(screenField γ x.val).det|
    Integrable l ν ∧ Integrable r (screenSlabMeasure I) ∧
      (∫ p, l p ∂ν) = ∫ x, r x ∂screenSlabMeasure I
  transport : ∀ f : phaseDomain I → ℝ, Burnett.RosenGeneral.Transport.HasLocalSmoothRepresentatives f →
    HasCompactSupport f → Integrable (intrinsicHamilton (screenField γ) f) ν ∧
      (∫ p, intrinsicHamilton (screenField γ) f p ∂ν) = 0

/-- The direct two-polarization Rosen closure with the explicit null graph witness. -/
theorem two_polarization_rosen_closure (I : Set ℝ) (hI : IsOpen I) (γn : ℕ → ℝ → Screen)
    (γ : ℝ → Screen) (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (h : ScreenPhysicalSequence I γn γ r) :
    ScreenFullKineticRepresentation I γ (phaseMeasure I (screenKineticWeight γ)) := by
  have hρ := h.density_nonneg hI
  have hw := screenKineticWeight_continuousOn γ I hI h.limit_smooth h.limit_positive
  have hn : ∀ u ∈ I, 0 ≤ screenKineticWeight γ u :=
    fun u hu => mul_nonneg (hρ u hu) (Real.sqrt_nonneg _)
  have hinv (u : ℝ) (hu : u ∈ I) : IsUnit (γ u).det := isUnit_iff_ne_zero.mpr (h.limit_positive u hu).det_pos.ne'
  refine ⟨phaseMeasure_regular I hI _ hw hn,
    phaseMeasure_closed_null_carrier I hI _ _ (fun x hx => screenHamilton_du γ x (hinv _ hx)),
    fun _ hK hKI => phaseMeasure_compact_base I hI _ hw hn hK hKI,
    fun _ hK hKI a ha hp => ⟨phaseMeasure_compact_auxiliary_second_moment I hI _ hw hn hK hKI a ha hp,
      phaseMeasure_compact_auxiliary_second_moment_integrable I hI _ hw hn hK hKI a ha hp⟩,
    screenEinstein_intrinsic_moment γ I hI h.limit_smooth h.limit_positive hρ,
    phaseMeasure_intrinsic_transport I hI _ hw hn (screenField γ) ?_⟩
  intro a x hx
  exact screenHamilton_canonical_du γ I hI hinv a x hx

end Burnett.RosenPlaneWave
