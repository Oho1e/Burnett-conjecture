import Burnett.Analysis.TransportWard.Weyl.PalatiniBoundaryDivergence
import Burnett.Analysis.TransportWard.Weyl.EHCompactVariation

/-! The Palatini boundary term has integral zero for compact lower variations. -/

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators ContDiff Topology

open private coordinateJet_eq_of_eventuallyEq indicator_smooth_and_compact integral_coordinatePartial_eq_zero
  from Burnett.Analysis.TransportWard.Weyl.EHCompactVariation

local notation "E" => CoordinateSpace

theorem coordinateConnectionVariation_zero_of_germ (g h : E → Mat) (x : E)
    (hz : h =ᶠ[𝓝 x] (fun _ : E => (0 : Mat))) :
    coordinateConnectionVariation g h x = 0 := by
  have h0 : h x = 0 := hz.self_of_nhds
  have hj := coordinateJet_eq_of_eventuallyEq hz
  have hj0 : coordinateJet (fun _ : E => (0 : Mat)) x = 0 := by
    funext a b c
    simp [coordinateJet]
  rw [hj0] at hj
  funext a b c
  simp [coordinateConnectionVariation, h0, hj, connectionVariation, inverseVariation, christoffel, koszul]

private theorem palatiniBoundaryVector_zero_off_compact (g h : E → Mat) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hSupport : ∀ y ∈ U \ K, h y = 0)
    (x : E) (hx : x ∈ U \ K) (a : Index) :
    palatiniBoundaryVector g (coordinateConnectionVariation g h) x a = 0 := by
  have hz : h =ᶠ[𝓝 x] (fun _ : E => (0 : Mat)) := by
    filter_upwards [(hU.sdiff hK.isClosed).mem_nhds hx] with y hy
    exact hSupport y hy
  simp only [palatiniBoundaryVector, coordinateConnectionVariation_zero_of_germ g h x hz,
    contractedConnection, connectionTrace, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

/-- Integration of the ordinary divergence of the actual Palatini vector
density over the compact support of the variation has no boundary term. -/
theorem integral_coordinateDivergence_palatini_compact_variation (g h : E → Mat) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hSupport : ∀ y ∈ U \ K, h y = 0) :
    (∫ x in K, coordinateDivergence (palatiniBoundaryVector g (coordinateConnectionVariation g h)) x) = 0 := by
  let F (x : E) := palatiniBoundaryVector g (coordinateConnectionVariation g h) x
  let V (a : Index) := U.indicator (fun y => F y a)
  let D (y : E) := ∑ a, coordinatePartial (V a) y a
  have hV (a : Index) : (∀ x ∉ K, V a x = 0) ∧ ContDiff ℝ ∞ (V a) ∧ HasCompactSupport (V a) := by
    refine indicator_smooth_and_compact hU hK hKU _ (contDiffOn_palatiniBoundaryVector g
      (coordinateConnectionVariation g h) hg hn
      (contDiffOn_coordinateConnectionVariation g h hU hg hh hn) a) ?_
    intro x hx
    exact palatiniBoundaryVector_zero_off_compact g h hU hK hSupport x hx a
  have hDi (a : Index) : Integrable (fun y => coordinatePartial (V a) y a) := by
    let v : E := EuclideanSpace.single a 1
    exact (Burnett.X02.CompactIBP.continuous_directional (hV a).2.1 v).integrable_of_hasCompactSupport
      ((hV a).2.2.fderiv_apply ℝ v)
  have hDZero : (∫ y, D y) = 0 := by
    rw [show D = (fun y => ∑ a, coordinatePartial (V a) y a) from rfl,
      integral_finset_sum Finset.univ (fun a _ => hDi a)]
    simp only [fun a => integral_coordinatePartial_eq_zero (V a) (hV a).2.1 (hV a).2.2 a,
      Finset.sum_const_zero]
  have hEq : EqOn (coordinateDivergence F) D K := by
    intro x hx
    unfold coordinateDivergence D
    apply Finset.sum_congr rfl
    intro a _
    have heq : V a =ᶠ[𝓝 x] fun y => F y a := by
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      exact indicator_of_mem hy _
    exact (DFunLike.congr_fun heq.fderiv_eq (EuclideanSpace.single a 1)).symm
  have hDout (x : E) (hx : x ∉ K) : D x = 0 := by
    have hzero (a : Index) : V a =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact (hV a).1 y hy
    unfold D
    apply Finset.sum_eq_zero
    intro a _
    rw [coordinatePartial, (hzero a).fderiv_eq]
    simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply]
  calc
    (∫ x in K, coordinateDivergence F x) = ∫ x in K, D x :=
      setIntegral_congr_fun hK.measurableSet hEq
    _ = ∫ x, D x := setIntegral_eq_integral_of_forall_compl_eq_zero hDout
    _ = 0 := hDZero

end Burnett.V03.Palatini
