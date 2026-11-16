import Burnett.Geometry.AuxiliaryPhysicalBound
import Burnett.Analysis.PositiveDensity

/-!
# An actual coordinate Riemannian volume density

The density is computed from the covariant auxiliary metric matrix as
sqrt(det R). Positivity and measurability are derived locally. This is a
coordinate measure, not a construction of a manifold volume or its pullback.
-/

noncomputable section

namespace Burnett.Geometry.RiemannianVolume

open MeasureTheory Filter
open scoped Topology ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.AuxiliaryConnection
open Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.ConnectionError

/-- The actual nonnegative coordinate density. Only its values on the chosen
coordinate domain are given geometric meaning. -/
def rho {X : Type*} (R : X → Matrix Index Index ℝ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (Matrix.det (R x)))

theorem continuousOn_rho {X : Type*} [TopologicalSpace X]
    (R : X → Matrix Index Index ℝ) (U : Set X) (hc : ContinuousOn R U) :
    ContinuousOn (rho R) U := by
  have hd : ContinuousOn (fun x => Matrix.det (R x)) U := by
    intro x hx
    exact continuous_id.matrix_det.continuousAt.comp_continuousWithinAt (hc x hx)
  exact ENNReal.continuous_ofReal.comp_continuousOn hd.sqrt

/-- The total field need not be measurable away from U. A measurable local
extension and a.e. equality on the restriction supply the required input. -/
theorem aemeasurable_rho_restrict {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) (R : X → Matrix Index Index ℝ)
    (U : Set X) (hU : MeasurableSet U) (hc : ContinuousOn R U) :
    AEMeasurable (rho R) (μ.restrict U) := by
  classical
  let q : X → ℝ≥0∞ := U.piecewise (rho R) (fun _ => 0)
  have hq : Measurable q := (continuousOn_rho R U hc).measurable_piecewise continuousOn_const hU
  apply hq.aemeasurable.congr
  filter_upwards [ae_restrict_mem hU] with x hx
  exact Set.piecewise_eq_of_mem U _ _ hx

theorem rho_pos {X : Type*} (R : X → Matrix Index Index ℝ) (x : X)
    (hx : (R x).PosDef) : 0 < rho R x :=
  ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hx.det_pos)

theorem rho_ne_top {X : Type*} (R : X → Matrix Index Index ℝ) (x : X) :
    rho R x ≠ ∞ := ENNReal.ofReal_ne_top

theorem withDensity_rho_open_pos {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (R : X → Matrix Index Index ℝ) (U : Set X) (hU : MeasurableSet U)
    (hc : ContinuousOn R U) (hp : ∀ x ∈ U, (R x).PosDef)
    {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < μ.withDensity (rho R) V :=
  Burnett.Analysis.PositiveDensity.withDensity_open_pos_of_forall hU
    (aemeasurable_rho_restrict μ R U hU hc) (fun x hx => rho_pos R x (hp x hx))
    hV hne hVU

/-- Euclidean coordinate volume weighted by the actual auxiliary density. -/
def coordinateMeasure (R : CoordinateSpace → Matrix Index Index ℝ) : Measure CoordinateSpace :=
  volume.withDensity (rho R)

theorem coordinateMeasure_open_pos
    (R : CoordinateSpace → Matrix Index Index ℝ) (U : Set CoordinateSpace) (hU : IsOpen U)
    (hc : ContinuousOn R U) (hp : ∀ x ∈ U, (R x).PosDef)
    {V : Set CoordinateSpace} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < coordinateMeasure R V :=
  withDensity_rho_open_pos volume R U hU.measurableSet hc hp hV hne hVU

/-- In particular, the local essential-supremum convention is unchanged by
this actual positive density. No finite mass or function measurability is needed. -/
theorem eLpNorm_top_coordinateMeasure_eq_volume {F : Type*} [ENorm F]
    (R : CoordinateSpace → Matrix Index Index ℝ) (U S : Set CoordinateSpace)
    (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hc : ContinuousOn R U) (hp : ∀ x ∈ U, (R x).PosDef) (f : CoordinateSpace → F) :
    eLpNorm f ∞ ((coordinateMeasure R).restrict S) = eLpNorm f ∞ (volume.restrict S) := by
  apply Burnett.Analysis.PositiveDensity.eLpNorm_top_restrict_withDensity_eq hS hSU
    (aemeasurable_rho_restrict volume R U hU.measurableSet hc)
  exact ae_restrict_of_forall_mem hU.measurableSet (fun x hx => rho_pos R x (hp x hx))

/-- The coordinate volume constructed from a genuine auxiliary bilinear field. -/
def metricMeasure (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) :
    Measure CoordinateSpace := coordinateMeasure (metricComponents r)

theorem metricMeasure_open_pos
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrp : ∀ x ∈ U, Matrix.PosDef (metricComponents r x))
    {V : Set CoordinateSpace} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < metricMeasure r V :=
  coordinateMeasure_open_pos (metricComponents r) U hU
    (BackgroundConnection.continuousOn_components_of_contDiffOn (metricComponents r) U hrc)
    hrp hV hne hVU

/-- The actual coordinate Riemannian measure supplies local open-set positivity.
All physical auxiliary-derivative bounds remain explicit, with their original
local quantifiers; neither an arbitrary measure nor its positivity is an input. -/
theorem metricConnectionError_uniform_and_LInfinity
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (r g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrp : ∀ x ∈ U, Matrix.PosDef (metricComponents r x))
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc : ∀ n a b, ContDiffOn ℝ 1 (fun y => metricComponents (g n) y a b) U)
    (hb : ∀ S : Set CoordinateSpace, IsCompact S → S ⊆ U → ∃ D : ℝ, 0 ≤ D ∧
      ∀ n, eLpNorm
        (fun x => norm3 (metricComponents r x) (auxiliaryPerturbationJet r g₀ (g n) x))
        ∞ ((metricMeasure r).restrict S) ≤ ENNReal.ofReal D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    (TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K) ∧
    ∃ hf : ∀ n, MemLp (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)) ∞
        ((metricMeasure r).restrict K),
      Tendsto (fun n => (hf n).toLp (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)))
        atTop (𝓝 0) := by
  exact AuxiliaryPhysicalBound.metricConnectionError_uniform_and_LInfinity_of_local_physical_bounds
    (metricMeasure r) U K hU hKU hK
    (fun V hV hVU hne => (metricMeasure_open_pos r U hU hrc hrp hV hne hVU).ne')
    r g₀ g hrc hrp hn₀ hn hs₀ hs hc₀ hc hb hconv

end Burnett.Geometry.RiemannianVolume
