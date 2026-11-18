import Burnett.Rosen.Geometry
import Burnett.Rosen.Screen
import Burnett.Rosen.Transport

/-!
# General Rosen plane waves

The scalar and Einstein curvatures and the intrinsic Einstein moment identity.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenPlaneWave

open Matrix Set Filter Burnett.RicciSymbol Burnett.RosenScreen
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Topology Matrix

/-- The symmetric optical matrix in the screen's positive definite metric. -/
def screenShear (γ : ℝ → Screen) (u : ℝ) : Screen :=
  screenS (γ u) (screenDerivative γ u)

theorem opticalMatrix_eq_screenL (γ : ℝ → Screen) (u : ℝ) :
    opticalMatrix γ u = screenL (γ u) (screenDerivative γ u) := by
  rw [screenL_eq_half_mul]
  ext i j
  simp [opticalMatrix, optical, Matrix.smul_apply, smul_eq_mul]
  ring

theorem opticalMatrix_trace_eq_shear (γ : ℝ → Screen) (u : ℝ) (hγ : (γ u).PosDef) :
    Matrix.trace (opticalMatrix γ u) = Matrix.trace (screenShear γ u) := by
  rw [opticalMatrix_eq_screenL, screenShear]
  exact trace_screenL_eq_trace_screenS _ _ hγ

set_option maxHeartbeats 600000 in
theorem opticalMatrix_trace_sq (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ u ∈ U, (γ u).PosDef) (u : ℝ) (hu : u ∈ U) :
    Matrix.trace (opticalMatrix γ u * opticalMatrix γ u) =
      ∑ i, ∑ j, (screenShear γ u i j)^2 := by
  rw [opticalMatrix_eq_screenL, screenShear]
  have hsym : (screenDerivative γ u).IsSymm := screenDeriv2_isSymm γ U hU hγ u hu
  simpa only [pow_two] using
    trace_screenL_sq_eq_sum_screenS_sq (γ u) (screenDerivative γ u) (hγ u hu) hsym

/-- Density of the null graph kinetic measure for the limiting Rosen metric. -/
def screenDefectDensity (γ : ℝ → Screen) (u : ℝ) : ℝ :=
  -deriv (fun t => Matrix.trace (screenShear γ t)) u - ∑ i, ∑ j, (screenShear γ u i j)^2

private theorem screen_symmetric_of_posDef {A : Screen} (hA : A.PosDef) : A.IsSymm := by
  change Aᵀ = A
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian

theorem coordinateRicci_screen_eq_density (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U)
    (hpos : ∀ u ∈ U, (γ u).PosDef) (x : CoordinateSpace) (hx : x 0 ∈ U) (b c : Index) :
    coordinateRicci (computedConnection (screenBilinear γ)) x b c =
      if b = 0 ∧ c = 0 then screenDefectDensity γ (x 0) else 0 := by
  have htrace : (fun t => Matrix.trace (opticalMatrix γ t)) =ᶠ[𝓝 (x 0)]
      (fun t => Matrix.trace (screenShear γ t)) := by
    filter_upwards [hU.mem_nhds hx] with u hu
    exact opticalMatrix_trace_eq_shear γ u (hpos u hu)
  rw [screenBilinear_coordinateRicci γ U hU hγ (fun u hu => (hpos u hu).det_pos.ne')
    (fun u hu => screen_symmetric_of_posDef (hpos u hu)) x hx b c, htrace.deriv_eq,
    opticalMatrix_trace_sq γ U hU hpos (x 0) hx, screenDefectDensity]
  congr 1
  ring

theorem screenVacuum_shearLaw (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U) (hpos : ∀ u ∈ U, (γ u).PosDef)
    (hVac : ∀ x : CoordinateSpace, x 0 ∈ U →
      ∀ b c : Index, coordinateRicci (computedConnection (screenBilinear γ)) x b c = 0)
    (u : ℝ) (hu : u ∈ U) :
    -deriv (fun t => Matrix.trace (screenShear γ t)) u = ∑ i, ∑ j, (screenShear γ u i j)^2 := by
  let x : CoordinateSpace := EuclideanSpace.single 0 u
  have hx : x 0 = u := by simp [x, EuclideanSpace.single_apply]
  have hxU : x 0 ∈ U := hx.symm ▸ hu
  have hv := hVac x hxU 0 0
  rw [coordinateRicci_screen_eq_density γ U hU hγ hpos x hxU, hx] at hv
  have hzero : screenDefectDensity γ u = 0 := by simpa using hv
  exact sub_eq_zero.mp hzero

end Burnett.RosenPlaneWave

namespace Burnett.RosenPlaneWave

open Matrix Set Burnett.RicciSymbol Burnett.RosenScreen
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open Burnett.RosenMultiscale.Transport
open scoped BigOperators ContDiff Matrix

def screenRicci (γ : ℝ → Screen) (x : Coordinate) : Matrix (Fin 4) (Fin 4) ℝ :=
  coordinateRicci (computedConnection (screenBilinear γ)) (WithLp.toLp 2 x)

def screenScalarCurvature (γ : ℝ → Screen) (x : Coordinate) : ℝ :=
  ∑ i, ∑ j, inverseMetric (screenField γ x) i j * screenRicci γ x i j

def screenEinstein (γ : ℝ → Screen) (x : Coordinate) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => screenRicci γ x i j - (screenScalarCurvature γ x / 2) * screenField γ x i j

theorem screenRicci_entries (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U)
    (hpos : ∀ u ∈ U, (γ u).PosDef) (x : Coordinate) (hx : x 0 ∈ U) (i j : Index) :
    screenRicci γ x i j = if i = 0 ∧ j = 0 then screenDefectDensity γ (x 0) else 0 :=
  coordinateRicci_screen_eq_density γ U hU hγ hpos (WithLp.toLp 2 x) hx i j

theorem screenScalarCurvature_zero (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U)
    (hpos : ∀ u ∈ U, (γ u).PosDef) (x : Coordinate) (hx : x 0 ∈ U) :
    screenScalarCurvature γ x = 0 := by
  have hi : inverseMetric (screenField γ x) = screenMetric (γ (x 0))⁻¹ :=
    screenMetric_inverse _ (isUnit_iff_ne_zero.mpr (hpos _ hx).det_pos.ne')
  have hz : inverseMetric (screenField γ x) 0 0 = 0 := by
    rw [hi]
    rfl
  unfold screenScalarCurvature
  simp only [screenRicci_entries γ U hU hγ hpos x hx, Fin.sum_univ_succ]
  simp [hz]

theorem screenEinstein_entries (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U)
    (hpos : ∀ u ∈ U, (γ u).PosDef) (x : Coordinate) (hx : x 0 ∈ U) (i j : Index) :
    screenEinstein γ x i j = if i = 0 ∧ j = 0 then screenDefectDensity γ (x 0) else 0 := by
  simp [screenEinstein, screenScalarCurvature_zero γ U hU hγ hpos x hx,
    screenRicci_entries γ U hU hγ hpos x hx]

theorem screenDefectDensity_contDiffOn (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) U) (hpos : ∀ u ∈ U, (γ u).PosDef) :
    ContDiffOn ℝ ∞ (screenDefectDensity γ) U := by
  have hs (i j : Fin 2) : ContDiffOn ℝ ∞ (fun u => screenShear γ u i j) U :=
    screenS_deriv_entry_contDiffOn γ U hU hγ hpos i j
  have ht : ContDiffOn ℝ ∞ (fun u => Matrix.trace (screenShear γ u)) U := by
    simp only [Matrix.trace, Matrix.diag]
    exact ContDiffOn.sum fun i _ => hs i i
  unfold screenDefectDensity
  exact ((ht.deriv_of_isOpen hU (by simp)).neg).sub
    (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hs i j).pow 2)

/-- Density relative to coordinate Lebesgue volume for the same kinetic measure. -/
def screenKineticWeight (γ : ℝ → Screen) (u : ℝ) : ℝ :=
  screenDefectDensity γ u * Real.sqrt (γ u).det

theorem screenKineticWeight_continuousOn (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) U) (hpos : ∀ u ∈ U, (γ u).PosDef) :
    ContinuousOn (screenKineticWeight γ) U := by
  have hdet : ContinuousOn (fun u => (γ u).det) U := by
    simp only [Matrix.det_fin_two]
    exact (((hγ 0 0).continuousOn.mul (hγ 1 1).continuousOn).sub
      ((hγ 0 1).continuousOn.mul (hγ 1 0).continuousOn))
  exact (screenDefectDensity_contDiffOn γ U hU hγ hpos).continuousOn.mul
    (Real.continuous_sqrt.comp_continuousOn hdet)

theorem screenKineticWeight_eq_geometric_density (γ : ℝ → Screen) (x : Coordinate)
    (hpos : (γ (x 0)).PosDef) :
    screenKineticWeight γ (x 0) =
      screenDefectDensity γ (x 0) * Real.sqrt |(screenField γ x).det| := by
  rw [screenKineticWeight, screenField, screenMetric_volumeDensity _ hpos.det_pos]

end Burnett.RosenPlaneWave

namespace Burnett.RosenPlaneWave

open MeasureTheory Set Filter Matrix Burnett.RicciSymbol
open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open Burnett.RosenGeneral.Transport
open scoped BigOperators ContDiff Topology

private theorem integrable_weighted_base_test (U : Set ℝ) (hU : IsOpen U)
    (w : ℝ → ℝ) (hw : ContinuousOn w U) (a : Coordinate → ℝ) (ha : Continuous a)
    (hc : HasCompactSupport a) (hsub : tsupport a ⊆ baseSlab U) :
    Integrable (fun x => w (x 0) * a x) (slabVolume U) := by
  have hcont : Continuous (fun x : Coordinate => w (x 0) * a x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ baseSlab U
    · have hwx : ContinuousAt w (x 0) := hw.continuousAt (hU.mem_nhds hx)
      have he : ContinuousAt (fun y : Coordinate => y 0) x := (continuous_apply 0).continuousAt
      exact (hwx.comp' (f := fun y : Coordinate => y 0) he).mul ha.continuousAt
    · have hn : x ∉ tsupport a := fun hh => hx (hsub hh)
      have hzero : a =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hn
      have he : (fun y : Coordinate => w (y 0) * a y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [hzero] with y hy
        simp [hy]
      exact (continuousAt_const : ContinuousAt (fun _ : Coordinate => (0 : ℝ)) x).congr he.symm
  exact (hcont.integrable_of_hasCompactSupport hc.mul_left).mono_measure Measure.restrict_le_self

def screenMomentPairing (S : Coordinate → CoordinateMetric) (p : Coordinate × Coordinate) : ℝ :=
  ∑ k : Index × Index, S p.1 k.1 k.2 * p.2 k.1 * p.2 k.2

def screenEinsteinPairing (γ : ℝ → Screen) (S : Coordinate → CoordinateMetric) (x : Coordinate) : ℝ :=
  ∑ k : Index × Index, S x k.1 k.2 * screenEinstein γ x k.1 k.2 * Real.sqrt |(screenField γ x).det|

theorem screenMomentPairing_at_du (S : Coordinate → CoordinateMetric) (x : Coordinate) :
    screenMomentPairing S (x, du) = S x 0 0 := by
  simp [screenMomentPairing, Fintype.sum_prod_type, du, Burnett.RosenMultiscale.Transport.coordinateBasis,
    Fin.sum_univ_succ]

theorem screenEinsteinPairing_eq_weight (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U) (hpos : ∀ u ∈ U, (γ u).PosDef)
    (S : Coordinate → CoordinateMetric) (x : Coordinate) (hx : x 0 ∈ U) :
    screenEinsteinPairing γ S x = screenKineticWeight γ (x 0) * S x 0 0 := by
  rw [screenKineticWeight_eq_geometric_density γ x (hpos _ hx)]
  simp [screenEinsteinPairing, Fintype.sum_prod_type, screenEinstein_entries γ U hU hγ hpos x hx,
    Fin.sum_univ_succ, mul_comm, mul_assoc]

/-- The Einstein second moment for the same positive Radon graph used for transport. -/
theorem screenEinstein_ambient_moment (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) U) (hpos : ∀ u ∈ U, (γ u).PosDef)
    (hn : ∀ u ∈ U, 0 ≤ screenDefectDensity γ u)
    (S : Coordinate → CoordinateMetric) (hS : Continuous fun x => S x 0 0)
    (hc : HasCompactSupport fun x => S x 0 0) (hsub : tsupport (fun x => S x 0 0) ⊆ baseSlab U) :
    let μ := phaseMeasure U (screenKineticWeight γ)
    Integrable (fun p : phaseDomain U => screenMomentPairing S p.val) μ ∧
    Integrable (screenEinsteinPairing γ S) (slabVolume U) ∧
      (∫ p : phaseDomain U, screenMomentPairing S p.val ∂μ) =
        ∫ x, screenEinsteinPairing γ S x ∂slabVolume U := by
  have hw := screenKineticWeight_continuousOn γ U hU hγ hpos
  have hn' : ∀ u ∈ U, 0 ≤ screenKineticWeight γ u :=
    fun u hu => mul_nonneg (hn u hu) (Real.sqrt_nonneg _)
  have hp := phaseMeasure_pairing U hU (screenKineticWeight γ) hw hn' (screenMomentPairing S)
  have hb := integrable_weighted_base_test U hU (screenKineticWeight γ) hw _ hS hc hsub
  have he : (fun x => screenKineticWeight γ (x 0) * S x 0 0) =ᵐ[slabVolume U]
      screenEinsteinPairing γ S := by
    filter_upwards [slabVolume_ae_mem U hU] with x hx
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
    exact (screenEinsteinPairing_eq_weight γ U hU (fun i j => (hγ i j).of_le h2) hpos S x hx).symm
  simp_rw [screenMomentPairing_at_du] at hp
  exact ⟨hp.1.mpr hb, hb.congr he, hp.2.trans (integral_congr_ae he)⟩

end Burnett.RosenPlaneWave

namespace Burnett.RosenPlaneWave

open MeasureTheory Set Filter Matrix Burnett.RicciSymbol
open Burnett.RosenMultiscale Burnett.RosenMultiscale.Transport
open Burnett.RosenGeneral.Transport
open scoped BigOperators ContDiff Topology

/-- Smooth tensor components in the open product chart around each intrinsic base point. -/
def HasLocalSmoothBaseTests {U : Set ℝ} (f : baseSlab U → ℝ) : Prop :=
  ∀ p : baseSlab U, ∃ (V : Set Coordinate) (F : Coordinate → ℝ),
    IsOpen V ∧ p.val ∈ V ∧ ContDiffOn ℝ ∞ F V ∧
      ∀ q : baseSlab U, q.val ∈ V → F q.val = f q

def screenBaseTestExtension {U : Set ℝ} (f : baseSlab U → ℝ) (x : Coordinate) : ℝ := by
  classical
  exact if hx : x ∈ baseSlab U then f ⟨x, hx⟩ else 0

private theorem screenBaseTestExtension_properties {U : Set ℝ} (hU : IsOpen U)
    (f : baseSlab U → ℝ) (hf : HasLocalSmoothBaseTests f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (screenBaseTestExtension f) ∧
      HasCompactSupport (screenBaseTestExtension f) ∧ tsupport (screenBaseTestExtension f) ⊆ baseSlab U := by
  have him : IsCompact (Subtype.val '' tsupport f : Set Coordinate) := hc.isCompact.image continuous_subtype_val
  have hsupp : Function.support (screenBaseTestExtension f) ⊆ Subtype.val '' tsupport f := by
    intro x hx
    by_cases h : x ∈ baseSlab U
    · refine ⟨⟨x, h⟩, subset_closure ?_, rfl⟩
      simpa [Function.mem_support, screenBaseTestExtension, h] using hx
    · exact False.elim (hx (by simp [screenBaseTestExtension, h]))
  have htsupp := closure_minimal hsupp him.isClosed
  have hsub : tsupport (screenBaseTestExtension f) ⊆ baseSlab U := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := htsupp hx
    exact y.property
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, him.of_isClosed_subset isClosed_closure htsupp, hsub⟩
  intro x
  by_cases hx : x ∈ baseSlab U
  · obtain ⟨V, F, hV, hxV, hF, hrep⟩ := hf ⟨x, hx⟩
    apply (hF.contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    filter_upwards [(baseSlab_isOpen hU).mem_nhds hx, hV.mem_nhds hxV] with y hy hyV
    rw [screenBaseTestExtension, dif_pos hy]
    exact (hrep ⟨y, hy⟩ hyV).symm
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsub h))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coordinate => (0 : ℝ)) x).congr_of_eventuallyEq hzero

/-- Lebesgue measure in the intrinsic base chart of the slab. -/
def screenSlabMeasure (U : Set ℝ) : Measure (baseSlab U) := (slabVolume U).comap Subtype.val

theorem screenSlabMeasure_map (U : Set ℝ) (hU : IsOpen U) :
    (screenSlabMeasure U).map Subtype.val = slabVolume U := by
  rw [screenSlabMeasure, map_comap_subtype_coe (baseSlab_isOpen hU).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (slabVolume_ae_mem U hU)

def screenPhaseBase {U : Set ℝ} (p : phaseDomain U) : baseSlab U := ⟨p.val.1, p.property.1⟩

/-- All compactly supported intrinsic base tensor tests use the same punctured phase measure. -/
theorem screenEinstein_intrinsic_moment (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun t => γ t i j) U) (hpos : ∀ u ∈ U, (γ u).PosDef)
    (hn : ∀ u ∈ U, 0 ≤ screenDefectDensity γ u) (S : baseSlab U → CoordinateMetric)
    (hS : ∀ i j, HasLocalSmoothBaseTests (fun x => S x i j)) (hc : HasCompactSupport S) :
    let μ := phaseMeasure U (screenKineticWeight γ)
    let l := fun p : phaseDomain U =>
      ∑ k : Index × Index, S (screenPhaseBase p) k.1 k.2 * p.val.2 k.1 * p.val.2 k.2
    let r := fun x : baseSlab U =>
      ∑ k : Index × Index, S x k.1 k.2 * screenEinstein γ x.val k.1 k.2 * Real.sqrt |(screenField γ x.val).det|
    Integrable l μ ∧ Integrable r (screenSlabMeasure U) ∧
      (∫ p, l p ∂μ) = ∫ x, r x ∂screenSlabMeasure U := by
  let E : Coordinate → CoordinateMetric := fun x i j => screenBaseTestExtension (fun y => S y i j) x
  have h00 : HasCompactSupport (fun x => S x 0 0) := hc.comp_left (g := fun A : CoordinateMetric => A 0 0) rfl
  have hprops := screenBaseTestExtension_properties hU (fun x => S x 0 0) (hS 0 0) h00
  have h := screenEinstein_ambient_moment γ U hU hγ hpos hn E hprops.1.continuous hprops.2.1 hprops.2.2
  have hE (x : baseSlab U) : E x.val = S x := by
    ext i j
    simp [E, screenBaseTestExtension, x.property]
  have hL : (fun p : phaseDomain U => screenMomentPairing E p.val) =
      (fun p : phaseDomain U => ∑ k : Index × Index, S (screenPhaseBase p) k.1 k.2 * p.val.2 k.1 * p.val.2 k.2) := by
    funext p
    unfold screenMomentPairing
    rw [show E p.val.1 = S (screenPhaseBase p) from hE (screenPhaseBase p)]
  have hR : (fun x : baseSlab U => screenEinsteinPairing γ E x.val) =
      (fun x : baseSlab U => ∑ k : Index × Index, S x k.1 k.2 * screenEinstein γ x.val k.1 k.2 *
        Real.sqrt |(screenField γ x.val).det|) := by
    funext x
    rw [screenEinsteinPairing, hE]
  have hcoe : Measurable (Subtype.val : baseSlab U → Coordinate) := measurable_subtype_coe
  have hm : Integrable (screenEinsteinPairing γ E) ((screenSlabMeasure U).map Subtype.val) := by
    rw [screenSlabMeasure_map U hU]
    exact h.2.1
  have hi : Integrable (fun x : baseSlab U => screenEinsteinPairing γ E x.val) (screenSlabMeasure U) :=
    (integrable_map_measure hm.aestronglyMeasurable hcoe.aemeasurable).mp hm
  have heq := integral_map hcoe.aemeasurable hm.aestronglyMeasurable
  rw [screenSlabMeasure_map U hU, hR] at heq
  rw [hR] at hi
  dsimp only at h ⊢
  rw [hL] at h
  exact ⟨h.1, hi, h.2.2.trans heq⟩

end Burnett.RosenPlaneWave
