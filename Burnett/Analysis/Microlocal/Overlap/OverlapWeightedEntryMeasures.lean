import Burnett.Analysis.Microlocal.Overlap.RoundOverlapTests
import Burnett.Analysis.Microlocal.Overlap.SeparableSetIntegralExt
import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.SeparablePositive (conjugateSymbol conjugateSymbol_apply productSymbol productSymbol_apply)
open Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.SmoothBaseTests
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private def windowRoundPoint (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall)
    (p : Chart q.ball) : roundOverlap q d :=
  ⟨p, hKU p.1.property, hMap p.1.property⟩

/-- The round phase space map on a source window whose image lies in
the target window. -/
def roundChartWindowMap (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall)
    (p : Chart q.ball) : Chart d.ball :=
  (roundOverlapTransition q d (windowRoundPoint q d hKU hMap p)).1

theorem continuous_roundChartWindowMap (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall) :
    Continuous (roundChartWindowMap q d hKU hMap) := by
  have hIn : Continuous (windowRoundPoint q d hKU hMap) := continuous_id.subtype_mk _
  exact continuous_subtype_val.comp ((continuous_roundOverlapTransition q d).comp hIn)

/-- Identical tests imply equality of the weighted entries on every target
Borel set, evaluated on its round overlap preimage in the source window. -/
theorem weighted_setIntegral_roundChart_eq_of_overlap_tests
    (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (i j : JetSlot) (α β : JetSlot → BoundedSymbol E)
    (hα : ∀ k, Continuous (α k : E → ℂ)) (hβ : ∀ l, Continuous (β l : E → ℂ))
    (hTests : ∀ (b m : BoundedSymbol E) (_ : ContDiff ℝ ∞ (b : E → ℂ))
      (_ : tsupport (b : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
      (_ : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (_ : DegreeZero (m : E → ℂ)),
      ∃ a : BoundedSymbol E, (∀ x ∈ q.ball.closedBall, a x = b (chartTransition q.center d.center x)) ∧
        (∫ p : Chart q.ball, movingChartAngularSymbol q.center d.center a m (p.1,p.2) *
          density νq hfq p i j ∂traceMeasure νq) =
        ∑ k : JetSlot, ∑ l : JetSlot, ∫ p : Chart d.ball,
          b p.1 * conj (α k p.1) * β l p.1 * m p.2 * density νd hfd p k l ∂traceMeasure νd)
    (ζ : BoundedSymbol E) (hζ : ContDiff ℝ ∞ (ζ : E → ℂ))
    (hζS : tsupport (ζ : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    let T := roundChartWindowMap q d hKU hMap
    (∫ p in T ⁻¹' S, ζ (T p).1 * density νq hfq p i j ∂traceMeasure νq) =
      ∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot, ζ y.1 * conj (α k y.1) * β l y.1 *
        density νd hfd y k l ∂traceMeasure νd := by
  intro T
  let τq := traceMeasure νq
  let τd := traceMeasure νd
  let f (p : Chart q.ball) := ζ (T p).1 * density νq hfq p i j
  let B (k l : JetSlot) := productSymbol (productSymbol ζ (conjugateSymbol (α k))) (β l)
  let G (k l : JetSlot) (y : Chart d.ball) := B k l y.1 * density νd hfd y k l
  let g (y : Chart d.ball) := ∑ k, ∑ l, G k l y
  have hT : Continuous T := continuous_roundChartWindowMap q d hKU hMap
  have hBase : Continuous (fun y : Chart d.ball => (y.1 : E)) :=
    continuous_subtype_val.comp continuous_fst
  have hf : Integrable f τq := (integrable_density_entry νq hfq i j).bdd_mul
    (hζ.continuous.comp (hBase.comp hT)).measurable.aestronglyMeasurable ⟨ζ.bound, fun x => ζ.norm_le (T x).1⟩
  have hG (k l : JetSlot) : Integrable (G k l) τd := by
    have hBc : Continuous (B k l : E → ℂ) := by
      change Continuous (fun x : E => ζ x * conj (α k x) * β l x)
      exact (hζ.continuous.mul (Complex.continuous_conj.comp (hα k))).mul (hβ l)
    exact (integrable_density_entry νd hfd k l).bdd_mul
      (hBc.comp hBase).measurable.aestronglyMeasurable ⟨_, fun y => (B k l).norm_le y.1⟩
  have hg : Integrable g τd :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hG k l
  apply setIntegral_preimage_eq_of_weightedChartTerms d.ball τq τd T hT.measurable f g hf hg _ S hS
  intro t
  let m := complexRationalAngularSymbol t.2
  let b := productSymbol ζ (baseSymbol d.ball t.1)
  let Q (y : Chart d.ball) := baseSymbol d.ball t.1 y.1 * m y.2
  have hb : ContDiff ℝ ∞ (b : E → ℂ) := hζ.mul (complexBase_contDiff d.ball t.1)
  have hbs : tsupport (b : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall :=
    tsupport_mul_subset_left.trans hζS
  have hd : DegreeZero (m : E → ℂ) := complexRationalAngular_degreeZero t.2
  obtain ⟨a, hPull, hEq⟩ := hTests b m hb hbs (complexRationalAngular_contDiffOn t.2) hd
  have hQc : Continuous Q := (separableRestriction d.ball [t]).continuous.congr (by
    rintro ⟨y, ξ⟩
    simp only [separableRestriction_apply, separableValue, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Q, m])
  have hQb (y : Chart d.ball) : ‖Q y‖ ≤ (baseSymbol d.ball t.1).bound * m.bound := by
    change ‖baseSymbol d.ball t.1 y.1 * m y.2‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul ((baseSymbol d.ball t.1).norm_le y.1) (m.norm_le y.2)
      (norm_nonneg _) (baseSymbol d.ball t.1).bound_nonneg
  have hJ (k l : JetSlot) : Integrable (fun y => Q y * G k l y) τd :=
    (hG k l).bdd_mul hQc.measurable.aestronglyMeasurable ⟨_, hQb⟩
  have hSum : (∫ y, Q y * g y ∂τd) = ∑ k, ∑ l, ∫ y, Q y * G k l y ∂τd := by
    simp only [g, Finset.mul_sum]
    exact (integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hJ k l))).trans
      (Finset.sum_congr rfl (fun k _ => integral_finset_sum _ (fun l _ => hJ k l)))
  change (∫ p, Q (T p) * f p ∂τq) = ∫ y, Q y * g y ∂τd
  calc
    _ = ∫ p : Chart q.ball, movingChartAngularSymbol q.center d.center a m (p.1,p.2) *
        density νq hfq p i j ∂τq := by
      apply integral_congr_ae
      filter_upwards with p
      have he := movingChartAngularSymbol_eq_targetRoundTest q d a b m hPull hd
        (windowRoundPoint q d hKU hMap p)
      change movingChartAngularSymbol q.center d.center a m (p.1,p.2) = b (T p).1 * m (T p).2 at he
      rw [he]
      dsimp only [Q, f, b, productSymbol_apply]
      ring
    _ = ∑ k, ∑ l, ∫ p : Chart d.ball,
        b p.1 * conj (α k p.1) * β l p.1 * m p.2 * density νd hfd p k l ∂τd := hEq
    _ = _ := by
      rw [hSum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply integral_congr_ae
      filter_upwards with p
      simp only [b, Q, G, B, productSymbol_apply, conjugateSymbol_apply]
      ring

end Burnett.Microlocal.Overlap
