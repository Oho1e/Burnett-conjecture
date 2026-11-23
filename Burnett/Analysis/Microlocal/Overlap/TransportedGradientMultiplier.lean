import Burnett.Analysis.Microlocal.Overlap.TransportedJetCoefficients
import Burnett.Analysis.Microlocal.BesselLocalization

/-!
# Physical multiplier form of the transported gradient

The pointwise formula becomes an exact `L²` identity. Replacing the target
covariant slots by the original coordinate slots preserves convergence,
since all coefficient multipliers are fixed and bounded.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovariantGradient

open Filter MeasureTheory Set
open Burnett.RicciSymbol Burnett.Fourier Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem transportedCovariantGradient_toLp_eq_sum (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ η : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K)
    (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target)
    (hηK : tsupport (η : CoordinateSpace → ℝ) ⊆ chartTransition c d '' K)
    (hCut : ∀ x ∈ (chartTransition c d).source,
      (η : CoordinateSpace → ℝ) (chartTransition c d x) = (χ : CoordinateSpace → ℝ) x)
    (w : JetSlot → JetSlot → D)
    (hw : ∀ i j, EqOn (w i j : CoordinateSpace → ℝ) (overlapJetCoefficient c d i j)
      (chartTransition c d '' K)) (n : ℕ) (i : JetSlot) :
    (transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume =
      ∑ j : JetSlot, symbolCLM (physicalCoefficient (w i j))
        (originalCovariantGradientL2 r B g hB hg hn d η hη n j) := by
  let u := transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i
  let v j := originalCovariantGradientSchwartz r B g hB hg hn d η hη n j
  let a j := coeffMul (w i j) (v j)
  have hSum : u = ∑ j, a j := by
    apply SchwartzMap.ext
    intro y
    let eval : SchwartzMap CoordinateSpace ℂ →+ ℂ :=
      { toFun := fun f => f y, map_zero' := rfl, map_add' := fun _ _ => rfl }
    change u y = eval (∑ j, a j)
    rw [map_sum]
    exact transportedCovariantGradientSchwartz_eq_sum r B g hB hg hn c d K hK hKU
      χ η hχ hη hηK hCut w hw n i y
  let L := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure CoordinateSpace)
  change L u = _
  rw [hSum, map_sum]
  exact Finset.sum_congr rfl fun j _ => coeffMul_toLp (w i j) (v j)

/-- The actual transported coordinate gradient and the coefficient combination
of the original target-coordinate gradients have the same `L²` limit error. -/
theorem transportedOriginalVolumeGradient_sub_target_sum_tendsto_zero (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ η : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K)
    (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace d).target)
    (hηK : tsupport (η : CoordinateSpace → ℝ) ⊆ chartTransition c d '' K)
    (hCut : ∀ x ∈ (chartTransition c d).source,
      (η : CoordinateSpace → ℝ) (chartTransition c d x) = (χ : CoordinateSpace → ℝ) x)
    (w : JetSlot → JetSlot → D)
    (hw : ∀ i j, EqOn (w i j : CoordinateSpace → ℝ) (overlapJetCoefficient c d i j)
      (chartTransition c d '' K)) (i : JetSlot) :
    Tendsto (fun n =>
      (transportedOriginalVolumeGradientSchwartz B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume -
        ∑ j : JetSlot, symbolCLM (physicalCoefficient (w i j))
          (originalGradient_volumeWeightedL2 B g hB hg hn d η hη n j)) atTop (𝓝 0) := by
  let L j := symbolCLM (physicalCoefficient (w i j))
  let a n := (transportedOriginalVolumeGradientSchwartz B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume
  let u n j := originalGradient_volumeWeightedL2 B g hB hg hn d η hη n j
  let v n j := originalCovariantGradientL2 r B g hB hg hn d η hη n j
  have hTarget (j : JetSlot) : Tendsto (fun n => L j (u n j - v n j)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, map_zero] using ((L j).continuous.tendsto 0).comp
      (originalGradient_sub_covariantGradient_tendsto_zero r B g hB hg hn hconv d η hη j)
  have hTargetSum : Tendsto (fun n => ∑ j, L j (u n j - v n j)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hTarget j)
  have hSource : Tendsto (fun n => a n - ∑ j, L j (v n j)) atTop (𝓝 0) := by
    refine (transportedOriginalVolumeGradient_sub_covariant_tendsto_zero r B g hB hg hn hconv
      c d K hK hKU χ hχ i).congr ?_
    intro n
    exact congrArg (fun b => a n - b)
      (transportedCovariantGradient_toLp_eq_sum r B g hB hg hn c d K hK hKU
        χ η hχ hη hηK hCut w hw n i)
  change Tendsto (fun n => a n - ∑ j, L j (u n j)) atTop (𝓝 0)
  have hDiff := hSource.sub hTargetSum
  simp only [sub_zero] at hDiff
  refine hDiff.congr ?_
  intro n
  simp only [map_sub, Finset.sum_sub_distrib, sub_sub_sub_cancel_right]

end Burnett.F05.OverlapCovariantGradient
