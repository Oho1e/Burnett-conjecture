import Burnett.Counterexamples.Rosen.Transport

/-!
# Rosen multiscale example

The zero scalar curvature and the Einstein moment of the same kinetic measure.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open scoped BigOperators

def rosenLimitCoordinateBilinear (pulled : Bool) : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace :=
  if pulled then pulledScreenBilinear Real.cos (fun u => screenX (Real.cos u) 0)
    (fun u => screenZ (Real.cos u) 0)
  else originalRosenBilinear Real.cos (fun _ => 0)

def rosenLimitRicci (pulled : Bool) (x : Coordinate) : CoordinateMetric :=
  coordinateRicci (computedConnection (rosenLimitCoordinateBilinear pulled)) (WithLp.toLp 2 x)

def rosenLimitScalarCurvature (pulled : Bool) (x : Coordinate) : ℝ :=
  ∑ i, ∑ j, inverseMetric (rosenLimitMetric pulled x) i j * rosenLimitRicci pulled x i j

def rosenLimitEinstein (pulled : Bool) (x : Coordinate) : CoordinateMetric := fun i j =>
  rosenLimitRicci pulled x i j - (rosenLimitScalarCurvature pulled x / 2) * rosenLimitMetric pulled x i j

theorem rosenLimitRicci_entries (pulled : Bool) (x : Coordinate) (hx : x 0 ∈ rosenInterval) (i j : Index) :
    rosenLimitRicci pulled x i j = if i = 0 ∧ j = 0 then 2 else 0 := by
  cases pulled
  · exact coordinateRicci_originalRosen_cos rosenInterval isOpen_Ioo
      (fun u hu => (rosenInterval_cos_pos u hu).ne') (WithLp.toLp 2 x) hx i j
  · exact coordinateRicci_pulledRosen_cos (WithLp.toLp 2 x) hx i j

theorem rosenLimitScalarCurvature_zero (pulled : Bool) (x : Coordinate) (hx : x 0 ∈ rosenInterval) :
    rosenLimitScalarCurvature pulled x = 0 := by
  have hz : inverseMetric (rosenLimitMetric pulled x) 0 0 = 0 := by
    cases pulled
    · exact inverseMetric_originalRosen_du_du Real.cos (fun _ => 0) x
    · exact inverseMetric_pulledRosen_du_du Real.cos (fun _ => 0) x
  unfold rosenLimitScalarCurvature
  simp only [rosenLimitRicci_entries pulled x hx, Fin.sum_univ_succ]
  simp [hz]

theorem rosenLimitEinstein_eq_ricci (pulled : Bool) (x : Coordinate) (hx : x 0 ∈ rosenInterval) :
    rosenLimitEinstein pulled x = rosenLimitRicci pulled x := by
  funext i j
  simp [rosenLimitEinstein, rosenLimitScalarCurvature_zero pulled x hx]

theorem rosenKineticMeasure_moment_eq_einstein (pulled : Bool) (a : Coordinate → ℝ)
    (ha : Continuous a) (hcompact : HasCompactSupport a) (i j : Index) :
    Integrable (fun p : Coordinate × Coordinate => a p.1 * p.2 i * p.2 j) (rosenKineticMeasure pulled) ∧
    (∫ p, a p.1 * p.2 i * p.2 j ∂rosenKineticMeasure pulled) =
      ∫ x, a x * rosenLimitEinstein pulled x i j * Real.sqrt |(rosenLimitMetric pulled x).det|
        ∂coordinateLebesgue := by
  have h := rosenKineticMeasure_moment_eq_limit_ricci pulled a ha hcompact i j
  refine ⟨h.1, h.2.trans ?_⟩
  apply integral_congr_ae
  filter_upwards [coordinateLebesgue_ae_mem] with x hx
  rw [rosenLimitEinstein_eq_ricci pulled x hx]
  rfl

theorem rosenKineticMeasure_tensor_moment_eq_einstein (pulled : Bool) (S : Coordinate → CoordinateMetric)
    (hS : ∀ i j, Continuous (fun x => S x i j) ∧ HasCompactSupport (fun x => S x i j)) :
    let l := fun p : Coordinate × Coordinate => ∑ k : Index × Index, S p.1 k.1 k.2 * p.2 k.1 * p.2 k.2
    let r := fun x => ∑ k : Index × Index, S x k.1 k.2 * rosenLimitEinstein pulled x k.1 k.2 *
      Real.sqrt |(rosenLimitMetric pulled x).det|
    Integrable l (rosenKineticMeasure pulled) ∧ Integrable r coordinateLebesgue ∧
    (∫ p, l p ∂rosenKineticMeasure pulled) = ∫ x, r x ∂coordinateLebesgue := by
  let l := fun k : Index × Index => fun p : Coordinate × Coordinate => S p.1 k.1 k.2 * p.2 k.1 * p.2 k.2
  let r := fun k : Index × Index => fun x : Coordinate =>
    S x k.1 k.2 * rosenLimitEinstein pulled x k.1 k.2 * Real.sqrt |(rosenLimitMetric pulled x).det|
  let d := fun x : Coordinate => if pulled then pulledLimitDensity x else originalLimitDensity x
  have hmatch (k : Index × Index) := rosenKineticMeasure_moment_eq_einstein pulled (fun x => S x k.1 k.2)
    (hS k.1 k.2).1 (hS k.1 k.2).2 k.1 k.2
  have hl (k : Index × Index) : Integrable (l k) (rosenKineticMeasure pulled) := (hmatch k).1
  have hright (k : Index × Index) : Integrable (r k) coordinateLebesgue := by
    by_cases hk : k.1 = 0 ∧ k.2 = 0
    · have hd : Continuous d := by
        cases pulled
        · exact continuous_const.mul ((Real.continuous_cos.comp (continuous_apply 0)).pow 2)
        · exact continuous_const.mul ((Real.continuous_cos.comp (continuous_apply 0)).pow 3)
      have hc : HasCompactSupport (fun x => d x * S x k.1 k.2) := (hS k.1 k.2).2.mul_left
      have h := ((hd.mul (hS k.1 k.2).1).integrable_of_hasCompactSupport hc).mono_measure
        (show coordinateLebesgue ≤ (volume : Measure Coordinate) from Measure.restrict_le_self)
      apply h.congr
      filter_upwards [coordinateLebesgue_ae_mem] with x hx
      rw [show d x = 2 * Real.sqrt |(rosenLimitMetric pulled x).det| from
        rosenLimitDensity_is_twice_metric_volume pulled x hx]
      unfold r
      rw [rosenLimitEinstein_eq_ricci pulled x hx, rosenLimitRicci_entries pulled x hx, if_pos hk]
      ring
    · apply (integrable_zero Coordinate ℝ coordinateLebesgue).congr
      filter_upwards [coordinateLebesgue_ae_mem] with x hx
      simp [r, rosenLimitEinstein_eq_ricci pulled x hx, rosenLimitRicci_entries pulled x hx, hk]
  dsimp only
  refine ⟨integrable_finset_sum Finset.univ (fun k _ => hl k),
    integrable_finset_sum Finset.univ (fun k _ => hright k), ?_⟩
  calc
    _ = ∑ k, ∫ p, l k p ∂rosenKineticMeasure pulled := integral_finset_sum Finset.univ (fun k _ => hl k)
    _ = ∑ k, ∫ x, r k x ∂coordinateLebesgue := Finset.sum_congr rfl (fun k _ => (hmatch k).2)
    _ = _ := (integral_finset_sum Finset.univ (fun k _ => hright k)).symm

end Burnett.RosenMultiscale.Transport
