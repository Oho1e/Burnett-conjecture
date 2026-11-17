import Burnett.Geometry.MixedTensorNorm
import Burnett.Geometry.RiemannianVolume

/-! The physical (1,2) auxiliary norm of the actual coordinate connection
error. L-infinity is represented by the scalar physical norm function, not
by assuming an unconstructed normed space of bundle-valued sections. -/

noncomputable section

namespace Burnett.Geometry.MixedConnectionError

open Filter MeasureTheory
open scoped Topology ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.MixedTensorNorm
open Burnett.Geometry.AuxiliaryConnection
open Burnett.Geometry.CovariantTensorNorm

theorem mixedNorm_uniform_of_uniform_zero {ι : Type*} {l : Filter ι}
    (R : CoordinateSpace → Matrix Index Index ℝ) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hcR : ContinuousOn R K) (hR : ∀ x ∈ K, (R x).PosDef)
    (f : ι → CoordinateSpace → Connection)
    (hu : TendstoUniformlyOn f (fun _ => 0) l K) :
    TendstoUniformlyOn (fun i x => mixedNorm (R x) (f i x)) (fun _ => 0) l K := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mixedNorm_control R K hK hcR hR
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / C) (div_pos hε hC)] with i hi
  intro x hx
  have hh : ‖f i x‖ < ε / C := by simpa only [dist_zero_left, dist_zero_right] using hi x hx
  have hmul : C * ‖f i x‖ < ε := by nlinarith [(lt_div_iff₀ hC).mp hh]
  have hbound := (hb x hx (f i x)).trans_lt hmul
  simpa only [dist_zero_left, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (mixedNorm_nonneg (R x) (f i x))] using hbound

/-- Compact-range continuity constructs the scalar physical-norm L∞
representatives. No MemLp or representative choice is a caller input. -/
theorem mixedNorm_exists_tendstoLp {ι : Type*} {l : Filter ι}
    (μ : Measure CoordinateSpace)
    (R : CoordinateSpace → Matrix Index Index ℝ) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hcR : ContinuousOn R K) (hR : ∀ x ∈ K, (R x).PosDef)
    (f : ι → CoordinateSpace → Connection) (hc : ∀ i, ContinuousOn (f i) K)
    (hu : TendstoUniformlyOn f (fun _ => 0) l K) :
    ∃ hf : ∀ i, MemLp (fun x => mixedNorm (R x) (f i x)) ∞ (μ.restrict K),
      Tendsto (fun i => (hf i).toLp (fun x => mixedNorm (R x) (f i x))) l (𝓝 0) := by
  let hf := fun i => Burnett.Analysis.LocalAeBound.memLp_top_restrict_of_continuousOn_isCompact
    μ hK hK.measurableSet (continuousOn_mixedNorm R (f i) K hcR (hc i) hR)
  exact ⟨hf, Burnett.Analysis.tendsto_toLp_top_of_uniformlyOn_zero hK.measurableSet _ hf
    (mixedNorm_uniform_of_uniform_zero R K hK hcR hR f hu)⟩

/-- The same locally bounded physical covariant derivative that controls
the actual connection error now gives its physical (1,2) norm convergence,
in the actual auxiliary coordinate measure. Manifold chart naturality and
intrinsic Levi-Civita/volume identification are separate geometric tasks. -/
theorem physicalError_uniform_and_LInfinity
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
        ∞ ((RiemannianVolume.metricMeasure r).restrict S) ≤ ENNReal.ofReal D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    (TendstoUniformlyOn (fun n x => mixedNorm (metricComponents r x)
      (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n) x)) (fun _ => 0) atTop K) ∧
    ∃ hf : ∀ n, MemLp (fun x => mixedNorm (metricComponents r x)
        (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n) x)) ∞
        ((RiemannianVolume.metricMeasure r).restrict K),
      Tendsto (fun n => (hf n).toLp (fun x => mixedNorm (metricComponents r x)
        (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n) x))) atTop (𝓝 0) := by
  have hu := (RiemannianVolume.metricConnectionError_uniform_and_LInfinity
    U K hU hKU hK r g₀ g hrc hrp hn₀ hn hs₀ hs hc₀ hc hb hconv).1
  have hcR := (BackgroundConnection.continuousOn_components_of_contDiffOn
    (metricComponents r) U hrc).mono hKU
  have hRK : ∀ x ∈ K, Matrix.PosDef (metricComponents r x) := fun x hx => hrp x (hKU hx)
  have hcE : ∀ n, ContinuousOn (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)) K := by
    intro n
    exact ConnectionErrorLInfinity.continuousOn_metricConnectionErrorOn U K hU hKU
      g₀ (g n) hn₀ (hn n) (fun x hx => (hs₀ x hx).self_of_nhds)
      (fun x hx => (hs n x hx).self_of_nhds) hc₀ (hc n)
  exact ⟨mixedNorm_uniform_of_uniform_zero _ K hK hcR hRK _ hu,
    mixedNorm_exists_tendstoLp _ _ K hK hcR hRK _ hcE hu⟩

end Burnett.Geometry.MixedConnectionError
