import Burnett.Analysis.GaugeProjection.WholeSpaceProjectedVacuumSource
import Burnett.Analysis.LocalWeakDerivative
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.P01

open Set Filter Metric
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open scoped Topology ContDiff Manifold Matrix


private theorem cutoffCoordinateMetric_smooth {η : CoordinateSpace → ℝ}
    {g : CoordinateSpace → Tensor2} {U : Set CoordinateSpace} (hU : IsOpen U)
    (hη : ContDiff ℝ ∞ η) (hηU : tsupport η ⊆ U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U) :
    SmoothCoordinateComponents (cutoffCoordinateMetric η g) :=
  fun i j => Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hη hηU (hg i j)

private theorem cutoffCoordinateMetric_eqOn {η : CoordinateSpace → ℝ} {g : CoordinateSpace → Tensor2}
    {V : Set CoordinateSpace} (hη : EqOn η 1 V) :
    EqOn (cutoffCoordinateMetric η g) g V := by
  intro x hx
  funext i j
  simp only [cutoffCoordinateMetric, hη hx, Pi.one_apply, one_mul]

private theorem cutoffCoordinateMetric_symmetric {η : CoordinateSpace → ℝ}
    {g : CoordinateSpace → Tensor2} {U : Set CoordinateSpace} (hηU : tsupport η ⊆ U)
    (hg : ∀ x ∈ U, IsSymmetricTensor (g x)) (x : CoordinateSpace) :
    IsSymmetricTensor (cutoffCoordinateMetric η g x) := by
  intro i j
  by_cases hx : x ∈ U
  · exact congrArg (η x * ·) (hg x hx i j)
  · have hη : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηU h))
    simp only [cutoffCoordinateMetric, hη, zero_mul]

theorem projectedChart_coordinateJet_eq_of_eventuallyEq {g g' : CoordinateSpace → Tensor2}
    {x : CoordinateSpace} (he : g =ᶠ[𝓝 x] g') : coordinateJet g x = coordinateJet g' x := by
  funext d i j
  have h := (he.fun_comp fun G : Tensor2 => G i j).fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (EuclideanSpace.single d 1)) h

private theorem projectedChart_coordinateConnectionJet_eq_of_eventuallyEq
    {Γ Γ' : CoordinateSpace → Connection} {x : CoordinateSpace} (he : Γ =ᶠ[𝓝 x] Γ') :
    coordinateConnectionJet Γ x = coordinateConnectionJet Γ' x := by
  funext d a b c
  have h := (he.fun_comp fun G : Connection => G a b c).fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (EuclideanSpace.single d 1)) h

private theorem projectedChart_coordinateRicci_eq_of_eventuallyEq
    {Γ Γ' : CoordinateSpace → Connection} {x : CoordinateSpace} (he : Γ =ᶠ[𝓝 x] Γ')
    (i j : Index) : coordinateRicci Γ x i j = coordinateRicci Γ' x i j := by
  rw [coordinateRicci, coordinateRicci, he.eq_of_nhds,
    projectedChart_coordinateConnectionJet_eq_of_eventuallyEq he]

/-- The matrix inverse of the original coordinate components at the given point.
The chosen globally Lipschitz coefficient agrees with this array near the
localization set. -/
def projectedChartInverse (g : CoordinateSpace → Tensor2) (x : CoordinateSpace) : Tensor2 :=
  fun i j => ((Matrix.of (g x))⁻¹) i j

private theorem projectedChartInverse_symmetric (g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hs : IsSymmetricTensor (g x)) : IsSymmetricTensor (projectedChartInverse g x) := by
  have ht : (Matrix.of (g x))ᵀ = Matrix.of (g x) := by
    ext i j
    exact hs j i
  have h : ((Matrix.of (g x))⁻¹)ᵀ = (Matrix.of (g x))⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, ht]
  intro i j
  exact congrArg (fun A : Matrix Index Index ℝ => A j i) h

private theorem projectedChartInverse_left (g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hd : (Matrix.of (g x)).det ≠ 0) (a b : Index) :
    (∑ k, projectedChartInverse g x a k * g x k b) = if a = b then 1 else 0 := by
  have h := congrArg (fun A : Matrix Index Index ℝ => A a b)
    (Matrix.nonsing_inv_mul (Matrix.of (g x)) (isUnit_iff_ne_zero.mpr hd))
  simpa only [projectedChartInverse, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using h

private theorem projectedChartInverse_right (g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hd : (Matrix.of (g x)).det ≠ 0) (a b : Index) :
    (∑ k, g x a k * projectedChartInverse g x k b) = if a = b then 1 else 0 := by
  have h := congrArg (fun A : Matrix Index Index ℝ => A a b)
    (Matrix.mul_nonsing_inv (Matrix.of (g x)) (isUnit_iff_ne_zero.mpr hd))
  simpa only [projectedChartInverse, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] using h

/-- Global smooth representatives and the local geometric data actually used
by the whole-space projected-source estimate. The coefficient is unchanged. -/
structure ProjectedChartRepresentatives
    (g inv : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (K : Set CoordinateSpace) where
  metric : ℕ → CoordinateSpace → Tensor2
  background : CoordinateSpace → Tensor2
  metric_smooth : ∀ n, SmoothCoordinateComponents (metric n)
  background_smooth : SmoothCoordinateComponents background
  metric_agrees : ∀ n, metric n =ᶠ[𝓝ˢ K] g n
  background_agrees : background =ᶠ[𝓝ˢ K] g₀
  metric_symmetric : ∀ n x, IsSymmetricTensor (metric n x)
  inverse_symmetric : ∀ n x, x ∈ K → IsSymmetricTensor (inv n x)
  inverse_left : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, ∀ a b,
    (∑ k, inv n y a k * metric n y k b) = if a = b then 1 else 0
  inverse_right : ∀ n x, x ∈ K → ∀ a b,
    (∑ k, metric n x a k * inv n x k b) = if a = b then 1 else 0
  vacuum : ∀ n x, x ∈ K → ∀ i j,
    coordinateRicci (fun y => christoffel (inv n y) (coordinateJet (metric n) y)) x i j = 0

/-- Genuine passage from open-chart metric data to the whole-space fields.
Only the original metric is assumed nondegenerate, and only on the open chart. -/
theorem exists_projectedChartRepresentatives {K U : Set CoordinateSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (g inv : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (hs : ∀ n x, x ∈ U → IsSymmetricTensor (g n x))
    (hdet : ∀ n x, x ∈ U → (Matrix.of (g n x)).det ≠ 0)
    (hInv : ∀ n, inv n =ᶠ[𝓝ˢ K] projectedChartInverse (g n))
    (hVac : ∀ n x, x ∈ K → ∀ i j, coordinateRicci
      (fun y => christoffel (projectedChartInverse (g n) y) (coordinateJet (g n) y)) x i j = 0) :
    Nonempty (ProjectedChartRepresentatives g inv g₀ K) := by
  obtain ⟨η, hη, _, hηU, V, hV, hKV, hVU, hηV⟩ := exists_projectedChartCutoff hK hU hKU
  let G (n : ℕ) := cutoffCoordinateMetric η (g n)
  let G₀ := cutoffCoordinateMetric η g₀
  have agree (n : ℕ) : EqOn (G n) (g n) V := cutoffCoordinateMetric_eqOn hηV
  have agree₀ : EqOn G₀ g₀ V := cutoffCoordinateMetric_eqOn hηV
  have hVn : V ∈ 𝓝ˢ K := hV.mem_nhdsSet.mpr hKV
  have invNear (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) :
      inv n =ᶠ[𝓝 x] projectedChartInverse (g n) := (hInv n).filter_mono (nhds_le_nhdsSet hx)
  have sameJet (n : ℕ) (y : CoordinateSpace) (hy : y ∈ V) :
      coordinateJet (G n) y = coordinateJet (g n) y :=
    projectedChart_coordinateJet_eq_of_eventuallyEq
      (eventually_of_mem (hV.mem_nhds hy) fun _ hz => agree n hz)
  refine ⟨{
    metric := G
    background := G₀
    metric_smooth := fun n => cutoffCoordinateMetric_smooth hU hη hηU (hg n)
    background_smooth := cutoffCoordinateMetric_smooth hU hη hηU hg₀
    metric_agrees := fun n => eventually_of_mem hVn fun _ hy => agree n hy
    background_agrees := eventually_of_mem hVn fun _ hy => agree₀ hy
    metric_symmetric := fun n => cutoffCoordinateMetric_symmetric hηU (hs n)
    inverse_symmetric := ?_
    inverse_left := ?_
    inverse_right := ?_
    vacuum := ?_ }⟩
  · intro n x hx
    rw [(invNear n x hx).eq_of_nhds]
    exact projectedChartInverse_symmetric _ _ (hs n x (hKU hx))
  · intro n x hx
    filter_upwards [hV.mem_nhds (hKV hx), invNear n x hx] with y hy hi
    intro a b
    rw [hi, agree n hy]
    exact projectedChartInverse_left _ _ (hdet n y (hVU hy)) a b
  · intro n x hx a b
    rw [(invNear n x hx).eq_of_nhds, agree n (hKV hx)]
    exact projectedChartInverse_right _ _ (hdet n x (hKU hx)) a b
  · intro n x hx i j
    have hΓ :
        (fun y => christoffel (inv n y) (coordinateJet (G n) y)) =ᶠ[𝓝 x]
        (fun y => christoffel (projectedChartInverse (g n) y) (coordinateJet (g n) y)) := by
      filter_upwards [hV.mem_nhds (hKV hx), invNear n x hx] with y hy hi
      rw [hi, sameJet n y hy]
    rw [projectedChart_coordinateRicci_eq_of_eventuallyEq hΓ i j]
    exact hVac n x hx i j

end Burnett.P01
