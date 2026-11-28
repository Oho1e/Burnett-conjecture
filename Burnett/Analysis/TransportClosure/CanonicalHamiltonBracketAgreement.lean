import Burnett.Counterexamples.Bianchi.RayIdentification
import Burnett.Geometry.Cotangent.WeightedMomentumTransport
import Burnett.Geometry.Cotangent.CanonicalTrajectories

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.Geometry.ActualTestLift

open Set Filter
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentHamiltonLocalFlow (cotangentChart_mem_punctured)
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Bianchi.RayIdentification (canonicalBracket canonicalBracket_congr)

local notation "E" => CoordinateSpace

private theorem fderiv_basePart (a : Phase → ℝ) (q : Phase) (ha : DifferentiableAt ℝ a q) (i : Index) :
    basePartial a q i = fderiv ℝ a q (coordinateBasis i, 0) := by
  have hA := (hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have h := (ha.hasFDerivAt.comp q.1 hA).fderiv
  simpa only [basePartial, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L (coordinateBasis i)) h

private theorem fderiv_momentumPart (a : Phase → ℝ) (q : Phase) (ha : DifferentiableAt ℝ a q) (i : Index) :
    momentumPartial a q i = fderiv ℝ a q (0, Pi.single i 1) := by
  have hA := (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2)
  have h := (ha.hasFDerivAt.comp q.2 hA).fderiv
  simpa only [momentumPartial, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using
    congrArg (fun L : Covector →L[ℝ] ℝ => L (Pi.single i 1)) h

/-- The actual Fréchet derivative paired with the canonical phase velocity
equals the sum of the coordinate Poisson brackets used by the original residual. -/
theorem hamiltonVector_fderiv_eq_canonicalBracket (G : E → Tensor2) (a : Phase → ℝ) (q : Phase)
    (ha : DifferentiableAt ℝ a q) :
    fderiv ℝ a q (hamiltonVector G q) =
      canonicalBracket (fun x ξ => coordinateP G (x, ξ)) (fun x ξ => a (x, ξ)) q.1 q.2 := by
  let v := hamiltonVector G q
  let D := fderiv ℝ a q
  have hx : v.1 = ∑ i, v.1 i • coordinateBasis i := (coordinateBasis.sum_repr v.1).symm
  have hξ : v.2 = ∑ i, v.2 i • (Pi.single i 1 : Covector) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  let I₁ : E →L[ℝ] Phase := (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] Covector)
  let I₂ : Covector →L[ℝ] Phase := (0 : Covector →L[ℝ] E).prod (ContinuousLinearMap.id ℝ Covector)
  have hDx : D (v.1, 0) = ∑ i, v.1 i * basePartial a q i := by
    change (D.comp I₁) v.1 = _
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_basePart a q ha i]
    rfl
  have hDξ : D (0, v.2) = ∑ i, v.2 i * momentumPartial a q i := by
    change (D.comp I₂) v.2 = _
    conv_lhs => rw [hξ]
    simp only [map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_momentumPart a q ha i]
    rfl
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  change D v = _
  calc
    D v = D ((v.1, 0) + (0, v.2)) := congrArg D hv
    _ = D (v.1, 0) + D (0, v.2) := map_add _ _ _
    _ = _ := by
      rw [hDx, hDξ, ← Finset.sum_add_distrib]
      unfold canonicalBracket
      apply Finset.sum_congr rfl
      intro i _
      have hBasis : Burnett.CubicExplicit.basis i = coordinateBasis i := by
        change EuclideanSpace.single i 1 = EuclideanSpace.basisFun Index ℝ i
        exact (EuclideanSpace.basisFun_apply Index ℝ i).symm
      simp only [Burnett.RotatingNullMoments.CanonicalHamilton.basePartial,
        Burnett.RotatingNullMoments.CanonicalHamilton.momentumPartial,
        Burnett.RotatingNullMoments.CanonicalHamilton.momentumBasis, hBasis]
      change momentumPartial (coordinateP G) q i * basePartial a q i +
          (-basePartial (coordinateP G) q i) * momentumPartial a q i =
        momentumPartial (coordinateP G) q i * basePartial a q i -
          basePartial (coordinateP G) q i * momentumPartial a q i
      ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Both formulations use the exact same half-quadratic Hamiltonian before
restriction to the cosphere or its null subset. -/
theorem chartHamiltonDerivative_eq_actual_canonicalBracket
    (g : Field (M := M)) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (c : M) (a : CotangentBundle M → ℝ) (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    {p : CotangentBundle M} (hp : p ∈ cotangentSource c) (hpun : p ∈ puncturedCotangent) :
    chartHamiltonDerivative g c a p =
      canonicalBracket (fun x ξ => dualEnergy g hn (cotangentChartInverse c (x, ξ)) / 2)
        (fun x ξ => a (cotangentChartInverse c (x, ξ))) (cotangentChart c p).1 (cotangentChart c p).2 := by
  let q := cotangentChart c p
  let A := a ∘ cotangentChartInverse c
  let G := chartInverse g c
  have hq : q ∈ puncturedPhaseTarget c := cotangentChart_mem_punctured c p hp hpun
  have hAt : DifferentiableAt ℝ A q :=
    ((contDiffOn_cotangent_test_chart c a ha).contDiffAt ((isOpen_puncturedPhaseTarget c).mem_nhds hq)).differentiableAt (by simp)
  have hP (x : E) (hx : x ∈ (chartAt E c).target) (ξ : Covector) :
      coordinateP G (x, ξ) = dualEnergy g hn (cotangentChartInverse c (x, ξ)) / 2 := by
    have hz : (x, ξ) ∈ phaseTarget c := ⟨hx, trivial⟩
    let b := cotangentChartInverse c (x, ξ)
    have hb : b ∈ cotangentSource c := cotangentChartInverse_mapsTo c hz
    have hchart := cotangentChart_right_inv c hz
    change symbolNorm (G x) ξ / 2 = dualEnergy g hn b / 2
    rw [dualEnergy_chart g hn hs c b hb]
    have hx' : chartAt E c b.1 = x := congrArg Prod.fst hchart
    have hξ' : cotangentCoords c b = ξ := congrArg Prod.snd hchart
    rw [hx', hξ']
    rfl
  unfold chartHamiltonDerivative
  rw [hamiltonVector_fderiv_eq_canonicalBracket G A q hAt]
  apply canonicalBracket_congr q.1 q.2 ?_ Filter.EventuallyEq.rfl ?_ rfl
  · filter_upwards [(chartAt E c).open_target.mem_nhds hq.1.1] with x hx
    exact hP x hx q.2
  · exact funext (hP q.1 hq.1.1)

end Burnett.Geometry.ActualTestLift
