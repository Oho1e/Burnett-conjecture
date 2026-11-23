import Burnett.Analysis.Microlocal.Overlap.CovariantGradient
import Burnett.Analysis.Microlocal.Overlap.KernelGeometry
import Burnett.Analysis.Microlocal.Overlap.Localization

/-!
# One localized tensor gradient on a preferred-chart overlap

The transported cutoff multiplies the same intrinsic covariant derivative
of the same perturbation. The three covariant indices pull back by the
actual chart Jacobian, and the background half-density supplies its
absolute determinant to the power one half.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovariantGradient

open Filter Set
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricSequence
open Burnett.Geometry.IntrinsicDhMeasure (coordinateDerivativeTensor intrinsic_components)
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.ChartVolumeBridge
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.OverlapGradient
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem originalCovariantGradientSchwartz_intrinsic (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace c).target) :
    originalCovariantGradientSchwartz r B g hB hg hn c χ hχ n i x =
      let m := (chartAt CoordinateSpace c).symm x
      let H : Field (M := M) := fun m' => g n m' - B m'
      ((((χ : CoordinateSpace → ℝ) x * chartHalfDensity B c x) *
        ManifoldCov3Norm.frameComponents3 (IntrinsicCov2.tensor r.inner H) c m i.1 i.2.1 i.2.2 : ℝ) : ℂ) := by
  dsimp only
  rw [intrinsic_components r _ (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB) c _
    ((chartAt CoordinateSpace c).symm_mapsTo hx), (chartAt CoordinateSpace c).right_inv hx]
  exact originalCovariantGradientSchwartz_apply r B g hB hg hn c χ hχ n i x

theorem coordinateDerivativeTensor_overlap (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source) :
    coordinateDerivativeTensor r H c x =
      TensorCoordinateChange.pullback3 (derivativeMatrix (fderiv ℝ (chartTransition c d) x))
        (coordinateDerivativeTensor r H d (chartTransition c d x)) :=
  CovariantJetNaturality.coordinate_covariantJet_change r.inner H (isSmooth_inner r) r.symm
    (GlobalLeviCivita.inner_nondegenerate r) hH c d x hx

/-- Pull back all three covariant slots and carry the Jacobian half-density. -/
def overlapJetPullback (c d : M) (x : CoordinateSpace) (u : JetSlot → ℂ) (i : JetSlot) : ℂ :=
  let J := derivativeMatrix (fderiv ℝ (chartTransition c d) x)
  (overlapJacobianWeight c d x : ℂ) * ∑ a : Index, ∑ b : Index, ∑ e : Index,
    ((J a i.1 * J b i.2.1 * J e i.2.2 : ℝ) : ℂ) * u (a, b, e)

theorem originalCovariantGradientSchwartz_overlap (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c d : M)
    (χ η : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target)
    (hCut : ∀ x ∈ (chartTransition c d).source, (η : CoordinateSpace → ℝ) (chartTransition c d x) =
      (χ : CoordinateSpace → ℝ) x)
    (n : ℕ) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source) (i : JetSlot) :
    originalCovariantGradientSchwartz r B g hB hg hn c χ hχ n i x =
      overlapJetPullback c d x
        (fun k => originalCovariantGradientSchwartz r B g hB hg hn d η hη n k (chartTransition c d x)) i := by
  let H : Field (M := M) := fun m => g n m - B m
  let y := chartTransition c d x
  let J := derivativeMatrix (fderiv ℝ (chartTransition c d) x)
  let V := coordinateDerivativeTensor r H d y
  have hT := congrFun (congrFun (congrFun
    (coordinateDerivativeTensor_overlap r H (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB)
      c d hx) i.1) i.2.1) i.2.2
  rw [TensorCoordinateChange.pullback3_apply] at hT
  change coordinateDerivativeTensor r H c x i.1 i.2.1 i.2.2 =
    ∑ a, ∑ b, ∑ e, J a i.1 * J b i.2.1 * J e i.2.2 * V a b e at hT
  have hReal : ((χ : CoordinateSpace → ℝ) x * chartHalfDensity B c x) *
      coordinateDerivativeTensor r H c x i.1 i.2.1 i.2.2 =
    overlapJacobianWeight c d x * ∑ a, ∑ b, ∑ e, (J a i.1 * J b i.2.1 * J e i.2.2) *
      (((η : CoordinateSpace → ℝ) y * chartHalfDensity B d y) * V a b e) := by
    rw [← hCut x hx, chartHalfDensity_transition B c d hx, hT, overlapJacobianWeight_eq c d hx]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp_rw [overlapJetPullback, originalCovariantGradientSchwartz_apply]
  exact_mod_cast hReal

/-- The original cutoff has a single transported cutoff. Both true covariant
inputs obey the exact overlap relation and are asymptotically equal in L²
to their respective original coordinate-gradient inputs. -/
theorem exists_originalCovariantGradient_overlap_inputs (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c d : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartTransition c d).source) :
    let hc := hχ.trans (overlapSource_subset_chartTarget c d)
    ∃ η : D, ∃ hd : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target,
      tsupport (η : CoordinateSpace → ℝ) ⊆ (chartTransition c d) '' tsupport (χ : CoordinateSpace → ℝ) ∧
      (∀ x ∈ (chartTransition c d).source, (η : CoordinateSpace → ℝ) (chartTransition c d x) =
        (χ : CoordinateSpace → ℝ) x) ∧
      (∀ n x, x ∈ (chartTransition c d).source → ∀ i,
        originalCovariantGradientSchwartz r B g hB hg hn c χ hc n i x =
          overlapJetPullback c d x
            (fun k => originalCovariantGradientSchwartz r B g hB hg hn d η hd n k (chartTransition c d x)) i) ∧
      (∀ i, Tendsto (fun n => originalGradient_volumeWeightedL2 B g hB hg hn c χ hc n i -
        originalCovariantGradientL2 r B g hB hg hn c χ hc n i) atTop (𝓝 0)) ∧
      (∀ i, Tendsto (fun n => originalGradient_volumeWeightedL2 B g hB hg hn d η hd n i -
        originalCovariantGradientL2 r B g hB hg hn d η hd n i) atTop (𝓝 0)) := by
  dsimp only
  obtain ⟨η, hη, hCut⟩ := exists_transportOverlapCutoff c d χ hχ
  have hc := hχ.trans (overlapSource_subset_chartTarget c d)
  have hd : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target := by
    apply hη.trans
    rintro y ⟨x, hx, rfl⟩
    exact ((chartTransition c d).mapsTo (hχ hx)).1
  exact ⟨η, hd, hη, hCut,
    fun n x hx i => originalCovariantGradientSchwartz_overlap r B g hB hg hn c d χ η hc hd hCut n hx i,
    originalGradient_sub_covariantGradient_tendsto_zero r B g hB hg hn hconv c χ hc,
    originalGradient_sub_covariantGradient_tendsto_zero r B g hB hg hn hconv d η hd⟩

end Burnett.F05.OverlapCovariantGradient
