import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeCoordinates
import Burnett.Geometry.IntrinsicScalarEinstein

/-! Intrinsic scalar contractions of the complex amplitude covariance. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

noncomputable section
namespace Burnett.F07.IntrinsicAmplitude

open Module
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.Geometry.ContravariantTensor (dualBilinearContraction_eq_sum tensorTangentBasis)
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open Burnett.Microlocal.CurlDensity (Pair)
open scoped BigOperators ContDiff Manifold

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private abbrev FourForm (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  MultilinearMap ℝ (fun _ : Fin 4 => V) ℝ

private def tailPair (J : FourForm V) (a b : V) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun c d => J ![a, b, c, d])
    (fun c c' d => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        J.map_update_add ![a, b, 0, d] (0 : Fin 2).succ.succ c c')
    (fun t c d => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        J.map_update_smul ![a, b, 0, d] (0 : Fin 2).succ.succ t c)
    (fun c d d' => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        J.map_update_add ![a, b, c, 0] (0 : Fin 1).succ.succ.succ d d')
    (fun t c d => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        J.map_update_smul ![a, b, c, 0] (0 : Fin 1).succ.succ.succ t d)

private def swapPairs (J : FourForm V) : FourForm V :=
  J.domDomCongr ((Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap 1 3))

private theorem swapPairs_apply (J : FourForm V) (a b c d : V) :
    swapPairs J ![a,b,c,d] = J ![c,d,a,b] := by
  unfold swapPairs
  rw [MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

private def swapMiddle (J : FourForm V) : FourForm V := J.domDomCongr (Equiv.swap 1 2)

private theorem swapMiddle_apply (J : FourForm V) (a b c d : V) :
    swapMiddle J ![a,b,c,d] = J ![a,c,b,d] := by
  unfold swapMiddle
  rw [MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

private def pairSum (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (J : FourForm V)
    (b e : Basis Index ℝ V) : ℝ :=
  ∑ i : Index × Index, ∑ j : Index × Index,
    (Q (b.dualBasis i.1) (b.dualBasis i.2) * Q (e.dualBasis j.1) (e.dualBasis j.2)) *
      J ![b i.1, b i.2, e j.1, e j.2]

private theorem pairSum_change_right (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (J : FourForm V)
    (b e f : Basis Index ℝ V) : pairSum Q J b e = pairSum Q J b f := by
  letI : FiniteDimensional ℝ V := Module.Finite.of_basis b
  unfold pairSum
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  let R := tailPair J (b i) (b j)
  simp only [Fintype.sum_prod_type]
  change (∑ k, ∑ l, Q (e.dualBasis k) (e.dualBasis l) * R (e k) (e l)) =
    (∑ k, ∑ l, Q (f.dualBasis k) (f.dualBasis l) * R (f k) (f l))
  rw [← dualBilinearContraction_eq_sum e Q R, ← dualBilinearContraction_eq_sum f Q R]

private theorem pairSum_swap (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (J : FourForm V)
    (b e : Basis Index ℝ V) : pairSum Q J b e = pairSum Q (swapPairs J) e b := by
  unfold pairSum
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [swapPairs_apply, mul_comm (Q (b.dualBasis i.1) (b.dualBasis i.2))]

private theorem pairSum_change_basis
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (J : FourForm V) (b e : Basis Index ℝ V) :
    pairSum Q J b b = pairSum Q J e e :=
  (pairSum_change_right Q J b b e).trans ((pairSum_swap Q J b e).trans
    ((pairSum_change_right Q (swapPairs J) e b e).trans (pairSum_swap Q J e e).symm))

/-- Equation `eq:mu-invariant`, using the ordered four covariant slots and a basis of their fiber. -/
def quarterContractionInBasis (b : Basis Index ℝ V) (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V))
    (J : MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ) : ℝ :=
  let G := fun i j => Q (b.dualBasis i) (b.dualBasis j)
  (∑ a : Index, ∑ b' : Index, ∑ c : Index, ∑ d : Index,
    (G a c * G b' d - G a b' * G c d / 2) * (J ![b a, b b', b c, b d]).re) / 4

private theorem quarterContractionInBasis_eq_pairSums (b : Basis Index ℝ V)
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V))
    (J : MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ) :
    quarterContractionInBasis b Q J =
      (pairSum Q (swapMiddle (Complex.reLm.compMultilinearMap J)) b b -
        pairSum Q (Complex.reLm.compMultilinearMap J) b b / 2) / 4 := by
  let G := fun i j => Q (b.dualBasis i) (b.dualBasis j)
  let F := Complex.reLm.compMultilinearMap J
  change (∑ a : Index, ∑ j : Index, ∑ c : Index, ∑ d : Index,
    (G a c * G j d - G a j * G c d / 2) * F ![b a, b j, b c, b d]) / 4 =
    (pairSum Q (swapMiddle F) b b - pairSum Q F b b / 2) / 4
  have hcross : (∑ a : Index, ∑ j : Index, ∑ c : Index, ∑ d : Index,
      (G a c * G j d) * F ![b a, b j, b c, b d]) = pairSum Q (swapMiddle F) b b := by
    simp only [pairSum, Fintype.sum_prod_type, swapMiddle_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have htrace : (∑ a : Index, ∑ j : Index, ∑ c : Index, ∑ d : Index,
      (G a j * G c d / 2) * F ![b a, b j, b c, b d]) = pairSum Q F b b / 2 := by
    simp only [pairSum, Fintype.sum_prod_type, Finset.sum_div, div_mul_eq_mul_div, G]
  simp only [sub_mul, Finset.sum_sub_distrib, hcross, htrace]

/-- The ordered amplitude contraction is the same in every real basis of the fiber. -/
theorem quarterContractionInBasis_eq (b e : Basis Index ℝ V)
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V))
    (J : MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ) :
    quarterContractionInBasis b Q J = quarterContractionInBasis e Q J := by
  rw [quarterContractionInBasis_eq_pairSums, quarterContractionInBasis_eq_pairSums,
    pairSum_change_basis Q (swapMiddle (Complex.reLm.compMultilinearMap J)) b e,
    pairSum_change_basis Q (Complex.reLm.compMultilinearMap J) b e]

end LinearAlgebra

/-- Contraction with both inverse auxiliary metric factors, over ordered pairs. -/
def auxiliaryTraceLinear (R : Tensor2) : Matrix Pair Pair ℂ →ₗ[ℝ] ℝ where
  toFun A := ∑ i : Pair, ∑ j : Pair, (R i.1 j.1 * R i.2 j.2) * (A i j).re
  map_add' A B := by
    simp only [Matrix.add_apply, Complex.add_re, mul_add, Finset.sum_add_distrib]
  map_smul' t A := by
    simp only [Matrix.smul_apply, Complex.smul_re, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem auxiliaryTraceLinear_apply (R : Tensor2) (A : Matrix Pair Pair ℂ) :
    auxiliaryTraceLinear R A = ∑ i : Pair, ∑ j : Pair, (R i.1 j.1 * R i.2 j.2) * (A i j).re := rfl

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The two inverse-metric contractions in a real basis, with the original order of the four slots. -/
def auxiliaryTraceInBasis (b : Basis Index ℝ V) (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V))
    (J : MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ) : ℝ :=
  auxiliaryTraceLinear (fun i j => Q (b.dualBasis i) (b.dualBasis j))
    (fun i j => J ![b i.1, b i.2, b j.1, b j.2])

private theorem auxiliaryTraceInBasis_eq_pairSum (b : Basis Index ℝ V)
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (J : MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ) :
    auxiliaryTraceInBasis b Q J = pairSum Q (swapMiddle (Complex.reLm.compMultilinearMap J)) b b := by
  simp only [auxiliaryTraceInBasis, auxiliaryTraceLinear_apply, pairSum, Fintype.sum_prod_type,
    swapMiddle_apply, LinearMap.compMultilinearMap_apply, Complex.reLm_coe]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- The auxiliary trace is independent of the real basis at the same point. -/
theorem auxiliaryTraceInBasis_eq (b e : Basis Index ℝ V)
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (J : MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ) :
    auxiliaryTraceInBasis b Q J = auxiliaryTraceInBasis e Q J := by
  rw [auxiliaryTraceInBasis_eq_pairSum, auxiliaryTraceInBasis_eq_pairSum, pairSum_change_basis]

end LinearAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The Lorentzian quarter contraction of the intrinsic amplitude before the null restriction. -/
def intrinsicPhysicalWeight {r : Metric (M := M)} (B : Field (M := M))
    (hn : IsNondegenerate B) (J : AmplitudeCovarianceDensity r) (p : Cosphere r) : ℝ :=
  let x := projection p
  quarterContractionInBasis (tensorTangentBasis x x (mem_chart_source CoordinateSpace x))
    (inverseMetricTensor B hn x) (J p)

theorem intrinsicPhysicalWeight_eq_basis {r : Metric (M := M)}
    (B : Field (M := M)) (hn : IsNondegenerate B) (J : AmplitudeCovarianceDensity r)
    (p : Cosphere r) (b : Basis Index ℝ (TangentSpace Model (projection p))) :
    intrinsicPhysicalWeight B hn J p =
      quarterContractionInBasis b (inverseMetricTensor B hn (projection p)) (J p) :=
  quarterContractionInBasis_eq (tensorTangentBasis (projection p) (projection p)
    (mem_chart_source CoordinateSpace (projection p))) b (inverseMetricTensor B hn (projection p)) (J p)

/-- The real auxiliary trace on the actual unit cosphere. -/
def intrinsicAuxiliaryTrace (r : Metric (M := M)) (J : AmplitudeCovarianceDensity r) (p : Cosphere r) : ℝ :=
  let x := projection p
  let b := tensorTangentBasis x x (mem_chart_source CoordinateSpace x)
  auxiliaryTraceInBasis b (inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x) (J p)

theorem intrinsicAuxiliaryTrace_eq_basis (r : Metric (M := M)) (J : AmplitudeCovarianceDensity r)
    (p : Cosphere r) (b : Basis Index ℝ (TangentSpace Model (projection p))) :
    intrinsicAuxiliaryTrace r J p = auxiliaryTraceInBasis b
      (inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) (projection p)) (J p) :=
  auxiliaryTraceInBasis_eq _ b _ _

end Burnett.F07.IntrinsicAmplitude
