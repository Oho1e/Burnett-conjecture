import Burnett.Geometry.Causality.ChartChronologicalNull
import Burnett.Geometry.Causality.TimelikeOrthogonalLevels
import Burnett.Geometry.ChartVectorField

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CotangentHamiltonCauchySlice

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A smooth choice of future timelike direction in the actual tangent bundle. -/
structure TimeOrientation (g : Field (M := M)) where
  vector : ChartVectorField.Field (M := M)
  smooth : ChartVectorField.IsSmooth vector
  timelike : ∀ m, g m (vector m) (vector m) < 0

/-- Joint continuity of the actual metric acting on two chart velocities. -/
theorem continuousAt_actual_chart_pairing {X : Type*} [TopologicalSpace X]
    (g : Field (M := M)) (hg : IsSmooth g) (c : M) (p : X)
    (y u v : X → CoordinateSpace) (hy : ContinuousAt y p) (hu : ContinuousAt u p)
    (hv : ContinuousAt v p) (hchart : y p ∈ (chartAt CoordinateSpace c).target) :
    ContinuousAt (fun q => coordinateBilinear g c (y q) (u q) (v q)) p := by
  let B := coordinateBilinear g c
  have hEntries (i j : Index) : ContinuousAt (fun q => B (y q) (coordinateBasis i) (coordinateBasis j)) p := by
    have hB := (contDiffOn_coordinateBilinear_apply g hg c (coordinateBasis i) (coordinateBasis j)).continuousOn
      |>.continuousAt ((chartAt CoordinateSpace c).open_target.mem_nhds hchart)
    exact ContinuousAt.comp' (f := y) hB hy
  have hexpand (q : X) : B (y q) (u q) (v q) =
      ∑ i, ∑ j, B (y q) (coordinateBasis i) (coordinateBasis j) * (u q i * v q j) := by
    have huq : u q = ∑ i, u q i • coordinateBasis i := (coordinateBasis.sum_repr (u q)).symm
    have hvq : v q = ∑ j, v q j • coordinateBasis j := (coordinateBasis.sum_repr (v q)).symm
    calc
      _ = B (y q) (∑ i, u q i • coordinateBasis i) (∑ j, v q j • coordinateBasis j) :=
        congrArg₂ (fun a b => B (y q) a b) huq hvq
      _ = _ := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  change ContinuousAt (fun q => B (y q) (u q) (v q)) p
  simp_rw [hexpand]
  unfold ContinuousAt
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  have hui : ContinuousAt (fun q => u q i) p := ContinuousAt.comp' (f := u)
    (EuclideanSpace.proj i).continuous.continuousAt hu
  have hvj : ContinuousAt (fun q => v q j) p := ContinuousAt.comp' (f := v)
    (EuclideanSpace.proj j).continuous.continuousAt hv
  exact ((hEntries i j).mul (hui.mul hvj)).tendsto

/-- Future timelike coordinate velocities, evaluated with the original metric
and the chosen intrinsic future direction. -/
def futureChartVelocities {g : Field (M := M)} (orientation : TimeOrientation g) (c : M) :
    Set (CoordinateSpace × CoordinateSpace) :=
  {z | z.1 ∈ (chartAt CoordinateSpace c).target ∧
    coordinateBilinear g c z.1 z.2 z.2 < 0 ∧
    coordinateBilinear g c z.1 (ChartVectorField.coordinateVector orientation.vector c z.1) z.2 < 0}

theorem isOpen_futureChartVelocities {g : Field (M := M)} (hg : IsSmooth g)
    (orientation : TimeOrientation g) (c : M) : IsOpen (futureChartVelocities orientation c) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have htarget := (chartAt CoordinateSpace c).open_target.mem_nhds hz.1
  have htime : ContinuousAt (fun q : CoordinateSpace × CoordinateSpace =>
      ChartVectorField.coordinateVector orientation.vector c q.1) z :=
    ContinuousAt.comp' (f := Prod.fst)
      ((ChartVectorField.contDiffOn_coordinateVector orientation.vector orientation.smooth c).continuousOn
        |>.continuousAt htarget) continuous_fst.continuousAt
  have hself := continuousAt_actual_chart_pairing g hg c z Prod.fst Prod.snd Prod.snd
    continuous_fst.continuousAt continuous_snd.continuousAt continuous_snd.continuousAt hz.1
  have hmix := continuousAt_actual_chart_pairing g hg c z Prod.fst
    (fun q => ChartVectorField.coordinateVector orientation.vector c q.1) Prod.snd
    continuous_fst.continuousAt htime continuous_snd.continuousAt hz.1
  exact inter_mem (continuous_fst.continuousAt.preimage_mem_nhds htarget)
    (inter_mem (hself.preimage_mem_nhds (Iio_mem_nhds hz.2.1))
      (hmix.preimage_mem_nhds (Iio_mem_nhds hz.2.2)))

/-- A timelike velocity cannot have zero pairing with the actual future time
direction. This applies at every point of a preferred chart. -/
theorem chart_time_pairing_ne_zero {g : Field (M := M)} (hL : HasLorentzSignature g)
    (orientation : TimeOrientation g) (c : M) {y v : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) (hv : coordinateBilinear g c y v v < 0) :
    coordinateBilinear g c y (ChartVectorField.coordinateVector orientation.vector c y) v ≠ 0 := by
  let x := (chartAt CoordinateSpace c).symm y
  let w := tangentFrame c x v
  let B : LinearMap.BilinForm ℝ (TangentSpace Model x) :=
    LinearMap.mk₂ ℝ (fun u z => g x u z) (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])
  have hw : B w w < 0 := hv
  have hwne : w ≠ 0 := by
    intro hwz
    rw [hwz, map_zero] at hw
    exact lt_irrefl _ hw
  intro hpair
  have hOrth : B (orientation.vector x) w = 0 := by
    change g x (tangentFrame c x (ChartVectorField.coordinateVector orientation.vector c y)) w = 0 at hpair
    rw [ChartVectorField.tangentFrame_coordinateVector orientation.vector c hy] at hpair
    exact hpair
  obtain ⟨b, hb⟩ := hL x
  exact (not_lt_of_gt hw) (positive_of_timelike_orthogonal B b hb (orientation.timelike x) hwne hOrth)

end Burnett.Geometry.FiniteCausalVolume
