import Burnett.Counterexamples.Bianchi.RayIdentification
import Burnett.Analysis.TransportClosure.IntrinsicCotangentAntipodal

/-! Reflection of the actual canonical derivatives in a cotangent chart. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.C04

open Function Filter Set Bundle Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere antipode antipode_val)
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Bianchi.RayIdentification (canonicalBracket canonicalBracket_congr basePartial_radial)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped ContDiff Manifold Topology BigOperators

local notation "E" => CoordinateSpace

private theorem momentumPartial_reflect_apply (a : E → Covector → ℝ) (i : Index)
    (x : E) (ξ : Covector) :
    momentumPartial i (fun y η => a y ((-1 : ℝ) • η)) x ξ =
      -momentumPartial i a x ((-1 : ℝ) • ξ) := by
  unfold momentumPartial
  rw [fderiv_comp_smul]
  simp

/-- Pulling back a scalar test by fiber reflection changes the sign of its
canonical Hamilton derivative composed with that reflection. -/
theorem canonicalBracket_reflect (U : Set E) (hU : IsOpen U)
    (P a : E → Covector → ℝ) (x : E) (hx : x ∈ U) (ξ : Covector)
    (hP : ∀ y ∈ U, ∀ η : Covector, P y ((-1 : ℝ) • η) = P y η) :
    canonicalBracket P (fun y η => a y ((-1 : ℝ) • η)) x ξ =
      -canonicalBracket P a x ((-1 : ℝ) • ξ) := by
  have hBase (i : Index) : basePartial i P x ((-1 : ℝ) • ξ) = basePartial i P x ξ := by
    simpa only [one_mul] using
      basePartial_radial U hU P i x hx ξ (-1) 1 (fun y hy => (hP y hy ξ).trans (one_mul _).symm)
  have hMom (i : Index) : momentumPartial i P x ξ = -momentumPartial i P x ((-1 : ℝ) • ξ) := by
    have hFun : (fun y η => P y ((-1 : ℝ) • η)) x = P x := funext (hP x hx)
    have hm := momentumPartial_reflect_apply P i x ξ
    change fderiv ℝ ((fun y η => P y ((-1 : ℝ) • η)) x) ξ _ = _ at hm
    rw [hFun] at hm
    exact hm
  unfold canonicalBracket
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [momentumPartial_reflect_apply, hMom i, hBase i]
  change _ * basePartial i a x ((-1 : ℝ) • ξ) - _ = _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Chart inversion commutes with actual fiber scaling throughout the base chart. -/
theorem cotangentChartInverse_scale (c : M) (x : E) (hx : x ∈ (chartAt E c).target)
    (ξ : Covector) (t : ℝ) :
    cotangentChartInverse c (x, t • ξ) = cotangentScale t (cotangentChartInverse c (x, ξ)) := by
  let y := (chartAt E c).symm x
  have hy : y ∈ (chartAt E c).source := (chartAt E c).symm_mapsTo hx
  let p := cotangentAssemble c (y, ξ)
  have hp : (cotangentScale t p).proj ∈ (chartAt E c).source := hy
  have h := cotangentAssemble_coords c (cotangentScale t p) hp
  rw [cotangentScale_projection, cotangentScale_coords,
    show cotangentCoords c p = ξ from cotangentCoords_assemble c (y, ξ) hy] at h
  exact h

/-- The background Hamiltonian in the actual canonical chart. -/
def chartHamiltonian (c : M) (B : Field (M := M)) (hn : IsNondegenerate B)
    (x : E) (ξ : Covector) : ℝ :=
  dualEnergy B hn (cotangentChartInverse c (x, ξ)) / 2

/-- The pre-restriction Hamilton derivative in the preferred chart with center `c`.
Each evaluation below uses a point over that chart source. -/
def chartHamiltonDerivative (c : M) (B : Field (M := M)) (hn : IsNondegenerate B)
    (a : CotangentBundle M → ℝ) (p : CotangentBundle M) : ℝ :=
  canonicalBracket (chartHamiltonian c B hn) (fun x ξ => a (cotangentChartInverse c (x, ξ)))
    (chartAt E c p.proj) (cotangentCoords c p)

theorem chartHamiltonian_reflect (c : M) (B : Field (M := M)) (hn : IsNondegenerate B)
    (x : E) (hx : x ∈ (chartAt E c).target) (ξ : Covector) :
    chartHamiltonian c B hn x ((-1 : ℝ) • ξ) = chartHamiltonian c B hn x ξ := by
  rw [chartHamiltonian, cotangentChartInverse_scale c x hx, dualEnergy_cotangentScale, chartHamiltonian]
  norm_num

theorem chartHamiltonDerivative_reflect (c : M) (B : Field (M := M)) (hn : IsNondegenerate B)
    (a : CotangentBundle M → ℝ) (p : CotangentBundle M) (hp : p.proj ∈ (chartAt E c).source) :
    chartHamiltonDerivative c B hn (a ∘ cotangentScale (-1)) p =
      -chartHamiltonDerivative c B hn a (cotangentScale (-1) p) := by
  let x := chartAt E c p.proj
  let ξ := cotangentCoords c p
  let U := (chartAt E c).target
  have hx : x ∈ U := (chartAt E c).mapsTo hp
  have hU : IsOpen U := (chartAt E c).open_target
  let P := chartHamiltonian c B hn
  let f (y : E) (η : Covector) := a (cotangentChartInverse c (y, η))
  let fR (y : E) (η : Covector) := a (cotangentScale (-1) (cotangentChartInverse c (y, η)))
  have hBR : canonicalBracket P fR x ξ = canonicalBracket P (fun y η => f y ((-1 : ℝ) • η)) x ξ := by
    apply canonicalBracket_congr x ξ .rfl ?_ rfl ?_
    · filter_upwards [hU.mem_nhds hx] with y hy
      simp only [fR, f, cotangentChartInverse_scale c y hy]
    · funext η
      simp only [fR, f, cotangentChartInverse_scale c x hx]
  rw [chartHamiltonDerivative, chartHamiltonDerivative, cotangentScale_projection, cotangentScale_coords]
  exact hBR.trans (canonicalBracket_reflect U hU P f x hx ξ (chartHamiltonian_reflect c B hn))

/-- A preferred chart at the actual base point reads the Hamilton derivative.
This definition chooses the same chart at a point and its fiber reflection. -/
def basePointHamiltonDerivative (B : Field (M := M)) (hn : IsNondegenerate B)
    (a : CotangentBundle M → ℝ) (p : CotangentBundle M) : ℝ :=
  chartHamiltonDerivative p.proj B hn a p

theorem basePointHamiltonDerivative_reflect (B : Field (M := M)) (hn : IsNondegenerate B)
    (a : CotangentBundle M → ℝ) (p : CotangentBundle M) :
    basePointHamiltonDerivative B hn (a ∘ cotangentScale (-1)) p =
      -basePointHamiltonDerivative B hn a (cotangentScale (-1) p) :=
  chartHamiltonDerivative_reflect p.proj B hn a p (mem_chart_source E p.proj)

theorem hamiltonDerivativeOnCosphere_reflect (r : Metric (M := M))
    (B : Field (M := M)) (hn : IsNondegenerate B) (a : CotangentBundle M → ℝ) (p : Cosphere r) :
    basePointHamiltonDerivative B hn (a ∘ cotangentScale (-1)) p.val =
      -basePointHamiltonDerivative B hn a (antipode r p).val := by
  simpa only [antipode_val] using basePointHamiltonDerivative_reflect B hn a p.val

end Burnett.C04
