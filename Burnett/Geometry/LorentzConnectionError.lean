import Burnett.Geometry.LorentzVolume
import Burnett.Geometry.MixedConnectionError

/-! The physical auxiliary norm of the connection error, measured with the
background geometric coordinate density sqrt(abs(det g_0)), as in the paper.
The measure is fixed in n. Intrinsic connection/chart identification remains
separate; no Lorentz matrix is put into the positive-only sqrt(det R) density. -/

noncomputable section

namespace Burnett.Geometry.LorentzConnectionError

open Filter MeasureTheory
open scoped Topology ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.AuxiliaryConnection
open Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.MixedTensorNorm

theorem det_metricComponents_ne_zero
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hg : (g x).Nondegenerate) : Matrix.det (metricComponents g x) ≠ 0 := by
  have hd : (BilinForm.toMatrix coordinateBasis (g x)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero coordinateBasis).mp hg
  have hm : BilinForm.toMatrix coordinateBasis (g x) = metricComponents g x := by
    ext i j
    simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
  simpa only [hm] using hd

/-- The local physical derivative bound and both conclusions use the actual
background g-volume, whose nonzero density follows from metric nondegeneracy. -/
theorem physicalError_uniform_and_LInfinity
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (r g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrp : ∀ x ∈ U, Matrix.PosDef (metricComponents r x))
    (hn₀ : ∀ x ∈ U, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc : ∀ n a b, ContDiffOn ℝ 1 (fun y => metricComponents (g n) y a b) U)
    (hb : ∀ S : Set CoordinateSpace, IsCompact S → S ⊆ U → ∃ D : ℝ, 0 ≤ D ∧
      ∀ n, eLpNorm
        (fun x => norm3 (metricComponents r x) (auxiliaryPerturbationJet r g₀ (g n) x))
        ∞ ((LorentzVolume.coordinateMeasure (metricComponents g₀)).restrict S) ≤ ENNReal.ofReal D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    let hn₀K : ∀ x ∈ K, (g₀ x).Nondegenerate := fun x hx => hn₀ x (hKU hx)
    (TendstoUniformlyOn (fun n x => mixedNorm (metricComponents r x)
      (metricConnectionErrorOn K g₀ (g n) hn₀K (hn n) x)) (fun _ => 0) atTop K) ∧
    ∃ hf : ∀ n, MemLp (fun x => mixedNorm (metricComponents r x)
        (metricConnectionErrorOn K g₀ (g n) hn₀K (hn n) x)) ∞
        ((LorentzVolume.coordinateMeasure (metricComponents g₀)).restrict K),
      Tendsto (fun n => (hf n).toLp (fun x => mixedNorm (metricComponents r x)
        (metricConnectionErrorOn K g₀ (g n) hn₀K (hn n) x))) atTop (𝓝 0) := by
  let hn₀K : ∀ x ∈ K, (g₀ x).Nondegenerate := fun x hx => hn₀ x (hKU hx)
  have hcG := BackgroundConnection.continuousOn_components_of_contDiffOn (metricComponents g₀) U hc₀
  have hdet : ∀ x ∈ U, Matrix.det (metricComponents g₀ x) ≠ 0 :=
    fun x hx => det_metricComponents_ne_zero g₀ x (hn₀ x hx)
  have hpos : ∀ V : Set CoordinateSpace, IsOpen V → V ⊆ U → V.Nonempty →
      LorentzVolume.coordinateMeasure (metricComponents g₀) V ≠ 0 := by
    intro V hV hVU hne
    exact (LorentzVolume.coordinateMeasure_open_pos (metricComponents g₀) U hU hcG hdet hV hne hVU).ne'
  have hu := (AuxiliaryPhysicalBound.metricConnectionError_uniform_and_LInfinity_of_local_physical_bounds
    (LorentzVolume.coordinateMeasure (metricComponents g₀)) U K hU hKU hK hpos r g₀ g hrc hrp
    hn₀K hn hs₀ hs hc₀ hc hb hconv).1
  have hcR := (BackgroundConnection.continuousOn_components_of_contDiffOn (metricComponents r) U hrc).mono hKU
  have hRK : ∀ x ∈ K, Matrix.PosDef (metricComponents r x) := fun x hx => hrp x (hKU hx)
  have hcE : ∀ n, ContinuousOn (metricConnectionErrorOn K g₀ (g n) hn₀K (hn n)) K := by
    intro n
    exact ConnectionErrorLInfinity.continuousOn_metricConnectionErrorOn U K hU hKU
      g₀ (g n) hn₀K (hn n) (fun x hx => (hs₀ x hx).self_of_nhds)
      (fun x hx => (hs n x hx).self_of_nhds) hc₀ (hc n)
  exact ⟨MixedConnectionError.mixedNorm_uniform_of_uniform_zero _ K hK hcR hRK _ hu,
    MixedConnectionError.mixedNorm_exists_tendstoLp _ _ K hK hcR hRK _ hcE hu⟩

end Burnett.Geometry.LorentzConnectionError
