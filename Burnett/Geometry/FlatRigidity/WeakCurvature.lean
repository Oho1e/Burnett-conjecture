import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UrysohnsLemma
import Burnett.Analysis.LocalWeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Burnett.Geometry.CurvatureDifference
import Burnett.Geometry.SmoothMetricConnection
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FlatRigidity

open Filter Matrix Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.SmoothMetricConnection
open scoped BigOperators ContDiff Topology

abbrev FrameMatrix := Matrix Index Index ℝ

def connectionMatrix (Γ : Connection) (d : Index) : FrameMatrix := fun a b => Γ a d b

def connectionMatrixDerivative (Γ : CoordinateSpace → Connection) (x : CoordinateSpace)
    (d e : Index) : FrameMatrix := fun a b => coordinateConnectionJet Γ x d a e b

def frameCoordinateJet (E : CoordinateSpace → FrameMatrix) (x : CoordinateSpace)
    (d : Index) : FrameMatrix := coordinateJet E x d

/-- The full curvature in directions `d,e`, as a map on vector components. -/
def coordinateRiemann (Γ : CoordinateSpace → Connection) (x : CoordinateSpace)
    (d e : Index) : FrameMatrix :=
  connectionMatrixDerivative Γ x d e - connectionMatrixDerivative Γ x e d +
    connectionMatrix (Γ x) d * connectionMatrix (Γ x) e -
    connectionMatrix (Γ x) e * connectionMatrix (Γ x) d

theorem coordinateRicci_eq_riemann_contract (Γ : CoordinateSpace → Connection) (x : CoordinateSpace)
    (hT : ∀ᶠ y in 𝓝 x, ∀ a b c, Γ y a b c = Γ y a c b) (b c : Index) :
    coordinateRicci Γ x b c = ∑ a, coordinateRiemann Γ x a c a b := by
  have hJ (d i j k : Index) : coordinateConnectionJet Γ x d i j k = coordinateConnectionJet Γ x d i k j := by
    have he : (fun y => Γ y i j k) =ᶠ[𝓝 x] (fun y => Γ y i k j) := hT.mono fun _ h => h i j k
    exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (EuclideanSpace.single d 1)) he.fderiv_eq
  have hs := hT.self_of_nhds
  simp only [coordinateRicci, ricci, coordinateRiemann, connectionMatrixDerivative, connectionMatrix,
    Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hJ a a c b, hJ c a a b, Finset.sum_sub_distrib]
  simp_rw [hs _ c b, hs _ a b]
  ring

private theorem scalar_directional_fderiv (f : CoordinateSpace → ℝ) (x v w : CoordinateSpace)
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

theorem frame_mixed_coordinateJet_comm (E : CoordinateSpace → FrameMatrix) (x : CoordinateSpace)
    (hE : ∀ a b, ContDiffAt ℝ 2 (fun y => E y a b) x) (d e : Index) :
    frameCoordinateJet (fun y => frameCoordinateJet E y e) x d =
      frameCoordinateJet (fun y => frameCoordinateJet E y d) x e := by
  ext a i
  let f := fun y => E y a i
  let v := (EuclideanSpace.single d 1 : CoordinateSpace)
  let w := (EuclideanSpace.single e 1 : CoordinateSpace)
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x w
  rw [scalar_directional_fderiv f x v w (hE a i), scalar_directional_fderiv f x w v (hE a i)]
  exact (hE a i).isSymmSndFDerivAt (by simp) v w

theorem frame_mixed_coordinateJet_of_parallel {U : Set CoordinateSpace} (hU : IsOpen U)
    (E : CoordinateSpace → FrameMatrix) (Γ : CoordinateSpace → Connection)
    (hE : ∀ a b, ContDiffOn ℝ 2 (fun y => E y a b) U)
    (hΓ : ∀ a b c, ContDiffOn ℝ 1 (fun y => Γ y a b c) U)
    (hPar : ∀ x ∈ U, ∀ e, frameCoordinateJet E x e = -(connectionMatrix (Γ x) e * E x))
    (x : CoordinateSpace) (hx : x ∈ U) (d e : Index) :
    frameCoordinateJet (fun y => frameCoordinateJet E y e) x d =
      -(connectionMatrixDerivative Γ x d e * E x + connectionMatrix (Γ x) e * frameCoordinateJet E x d) := by
  ext a i
  have hg (k : Index) : DifferentiableAt ℝ (fun y => Γ y a e k) x :=
    ((hΓ a e k).contDiffAt (hU.mem_nhds hx)).differentiableAt le_rfl
  have hf (k : Index) : DifferentiableAt ℝ (fun y => E y k i) x :=
    ((hE k i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hprod : (fun y => frameCoordinateJet E y e a i) =ᶠ[𝓝 x]
      (fun y => -(∑ k, Γ y a e k * E y k i)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [Matrix.neg_apply, Matrix.mul_apply, connectionMatrix] using
      congrArg (fun A : FrameMatrix => A a i) (hPar y hy e)
  change fderiv ℝ (fun y => frameCoordinateJet E y e a i) x (EuclideanSpace.single d 1) = _
  rw [hprod.fderiv_eq]
  simp only [frameCoordinateJet, coordinateJet, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply, connectionMatrixDerivative,
    coordinateConnectionJet, connectionMatrix]
  congr 1
  have ht (k : Index) : DifferentiableAt ℝ (fun y => Γ y a e k * E y k i) x := (hg k).mul (hf k)
  rw [fderiv_fun_sum (u := Finset.univ) (fun k _ => ht k), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (hg k) (hf k), ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

private theorem coordinateRiemann_eq_zero_of_commuting_parallel_products
    (Γ : CoordinateSpace → Connection) (x : CoordinateSpace) (E : FrameMatrix) (d e : Index)
    (hInv : IsUnit E.det)
    (hmix : -(connectionMatrixDerivative Γ x d e * E +
        connectionMatrix (Γ x) e * (-(connectionMatrix (Γ x) d * E))) =
      -(connectionMatrixDerivative Γ x e d * E +
        connectionMatrix (Γ x) d * (-(connectionMatrix (Γ x) e * E)))) :
    coordinateRiemann Γ x d e = 0 := by
  have he : coordinateRiemann Γ x d e * E = 0 := by
    calc
      _ = -(connectionMatrixDerivative Γ x e d * E +
          connectionMatrix (Γ x) d * (-(connectionMatrix (Γ x) e * E))) -
          (-(connectionMatrixDerivative Γ x d e * E +
            connectionMatrix (Γ x) e * (-(connectionMatrix (Γ x) d * E)))) := by
        unfold coordinateRiemann
        noncomm_ring
      _ = 0 := by rw [hmix, sub_self]
  have hmul : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv _ hInv
  calc
    coordinateRiemann Γ x d e = coordinateRiemann Γ x d e * 1 := by rw [Matrix.mul_one]
    _ = coordinateRiemann Γ x d e * (E * E⁻¹) := by rw [hmul]
    _ = (coordinateRiemann Γ x d e * E) * E⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = 0 := by rw [he, Matrix.zero_mul]

theorem coordinateRiemann_eq_zero_of_parallel_frame {U : Set CoordinateSpace} (hU : IsOpen U)
    (E : CoordinateSpace → FrameMatrix) (Γ : CoordinateSpace → Connection)
    (hE : ∀ a b, ContDiffOn ℝ 2 (fun y => E y a b) U)
    (hΓ : ∀ a b c, ContDiffOn ℝ 1 (fun y => Γ y a b c) U)
    (hInv : ∀ x ∈ U, IsUnit (E x).det)
    (hPar : ∀ x ∈ U, ∀ d, frameCoordinateJet E x d = -(connectionMatrix (Γ x) d * E x))
    (x : CoordinateSpace) (hx : x ∈ U) (d e : Index) : coordinateRiemann Γ x d e = 0 := by
  have hmix := frame_mixed_coordinateJet_comm E x (fun a b => (hE a b).contDiffAt (hU.mem_nhds hx)) d e
  rw [frame_mixed_coordinateJet_of_parallel hU E Γ hE hΓ hPar x hx d e,
    frame_mixed_coordinateJet_of_parallel hU E Γ hE hΓ hPar x hx e d,
    hPar x hx d, hPar x hx e] at hmix
  exact coordinateRiemann_eq_zero_of_commuting_parallel_products Γ x (E x) d e (hInv x hx) hmix

theorem coordinateRiemann_computedConnection_eq_zero_of_parallel_frame
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => metricComponents g y i j) U)
    (hn : ∀ x ∈ U, (g x).Nondegenerate) (E : CoordinateSpace → FrameMatrix)
    (hE : ∀ i j, ContDiffOn ℝ 2 (fun y => E y i j) U) (hInv : ∀ x ∈ U, IsUnit (E x).det)
    (hPar : ∀ x ∈ U, ∀ d, frameCoordinateJet E x d = -(connectionMatrix (computedConnection g x) d * E x))
    (x : CoordinateSpace) (hx : x ∈ U) (d e : Index) : coordinateRiemann (computedConnection g) x d e = 0 :=
  coordinateRiemann_eq_zero_of_parallel_frame hU E (computedConnection g) hE
    (fun a b c => (contDiffOn_computedConnection g U hU hg hn a b c).of_le (by simp)) hInv hPar x hx d e

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Analysis.LocalWeakDerivative
open scoped BigOperators ContDiff Topology

def directionalDerivative (d : Index) (f : CoordinateSpace → ℝ) (x : CoordinateSpace) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single d 1)

/-- Actual distributional differentiation in the fixed Euclidean chart. -/
def WeakCoordinateDerivativeOn (U : Set CoordinateSpace) (d : Index)
    (f F : CoordinateSpace → ℝ) : Prop :=
  ∀ ψ : CoordinateSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    (∫ x, directionalDerivative d ψ x * f x) = -(∫ x, ψ x * F x)

private theorem continuous_test_mul_continuousOn {U : Set CoordinateSpace} (hU : IsOpen U)
    {ψ f : CoordinateSpace → ℝ} (hψ : Continuous ψ) (hs : tsupport ψ ⊆ U)
    (hf : ContinuousOn f U) : Continuous (fun x => ψ x * f x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hψ.continuousAt.mul (hf.continuousAt (hU.mem_nhds hx))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    have heq : (fun y => ψ y * f y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hzero] with y hy
      simp [hy]
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem integrable_test_mul_continuousOn {U : Set CoordinateSpace} (hU : IsOpen U)
    {ψ f : CoordinateSpace → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) (hf : ContinuousOn f U) : Integrable (fun x => ψ x * f x) :=
  (continuous_test_mul_continuousOn hU hψ hs hf).integrable_of_hasCompactSupport hc.mul_right

private theorem directionalDerivative_contDiff {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (d : Index) : ContDiff ℝ ∞ (directionalDerivative d ψ) :=
  (hψ.fderiv_right (by simp)).clm_apply contDiff_const

private theorem directionalDerivative_contDiffOn {U : Set CoordinateSpace} (hU : IsOpen U)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U) (d : Index) :
    ContDiffOn ℝ ∞ (directionalDerivative d ψ) U :=
  (hψ.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem directionalDerivative_hasCompactSupport {ψ : CoordinateSpace → ℝ}
    (hc : HasCompactSupport ψ) (d : Index) : HasCompactSupport (directionalDerivative d ψ) :=
  hc.fderiv_apply ℝ (EuclideanSpace.single d 1)

private theorem directionalDerivative_tsupport_subset (ψ : CoordinateSpace → ℝ) (d : Index) :
    tsupport (directionalDerivative d ψ) ⊆ tsupport ψ :=
  tsupport_directional_subset ψ (EuclideanSpace.single d 1)

theorem WeakCoordinateDerivativeOn.mul_smooth {U : Set CoordinateSpace} (hU : IsOpen U)
    {d : Index} {f F A : CoordinateSpace → ℝ} (h : WeakCoordinateDerivativeOn U d f F)
    (hf : ContinuousOn f U) (hF : ContinuousOn F U) (hA : ContDiffOn ℝ ∞ A U) :
    WeakCoordinateDerivativeOn U d (fun x => A x * f x)
      (fun x => directionalDerivative d A x * f x + A x * F x) := by
  intro ψ hψ hc hs
  have hh := h (fun x => ψ x * A x) (contDiff_test_mul_local hU hψ hs hA)
    hc.mul_right (tsupport_mul_subset_left.trans hs)
  have hψD := directionalDerivative_contDiff hψ d
  have hA' := directionalDerivative_contDiffOn hU hA d
  have hL := integrable_test_mul_continuousOn hU hψD.continuous (directionalDerivative_hasCompactSupport hc d)
    ((directionalDerivative_tsupport_subset ψ d).trans hs) (hA.continuousOn.mul hf)
  have hR := integrable_test_mul_continuousOn hU hψ.continuous hc hs (hA'.continuousOn.mul hf)
  have hG := integrable_test_mul_continuousOn hU hψ.continuous hc hs (hA.continuousOn.mul hF)
  have he (x : CoordinateSpace) :
      directionalDerivative d (fun x => ψ x * A x) x * f x =
        directionalDerivative d ψ x * (A x * f x) + ψ x * (directionalDerivative d A x * f x) := by
    unfold directionalDerivative
    rw [fderiv_test_mul_local hU hψ hs hA]
    ring
  simp_rw [he, mul_assoc] at hh
  rw [integral_add hL hR] at hh
  simp_rw [mul_add]
  rw [integral_add hR hG]
  linarith

theorem WeakCoordinateDerivativeOn.neg {U : Set CoordinateSpace} {d : Index} {f F : CoordinateSpace → ℝ}
    (h : WeakCoordinateDerivativeOn U d f F) :
    WeakCoordinateDerivativeOn U d (fun x => -f x) (fun x => -F x) := by
  intro ψ hψ hc hs
  simp only [mul_neg, integral_neg, neg_neg]
  exact neg_eq_iff_eq_neg.mpr (h ψ hψ hc hs)

theorem WeakCoordinateDerivativeOn.sum {U : Set CoordinateSpace} (hU : IsOpen U)
    {d : Index} {ι : Type*} (s : Finset ι) {f F : ι → CoordinateSpace → ℝ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) U) (hF : ∀ i ∈ s, ContinuousOn (F i) U)
    (h : ∀ i ∈ s, WeakCoordinateDerivativeOn U d (f i) (F i)) :
    WeakCoordinateDerivativeOn U d (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, F i x) := by
  intro ψ hψ hc hs
  have hψD := directionalDerivative_contDiff hψ d
  have hL (i : ι) (hi : i ∈ s) := integrable_test_mul_continuousOn hU hψD.continuous
    (directionalDerivative_hasCompactSupport hc d) ((directionalDerivative_tsupport_subset ψ d).trans hs) (hf i hi)
  have hR (i : ι) (hi : i ∈ s) := integrable_test_mul_continuousOn hU hψ.continuous hc hs (hF i hi)
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum s hL, integral_finset_sum s hR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => h i hi ψ hψ hc hs

private theorem continuousOn_nonneg_of_tests {U : Set CoordinateSpace} (hU : IsOpen U)
    {f : CoordinateSpace → ℝ} (hf : ContinuousOn f U)
    (h : ∀ ψ : CoordinateSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      0 ≤ ∫ x, ψ x * f x) : ∀ x ∈ U, 0 ≤ f x := by
  intro x hx
  by_contra hn
  have hn' : f x < 0 := lt_of_not_ge hn
  have hnear : {y | y ∈ U ∧ f y < 0} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hx,
      (hf.continuousAt (hU.mem_nhds hx)).eventually (Iio_mem_nhds hn')] with y hy hny
    exact ⟨hy, hny⟩
  obtain ⟨ψ, hs, hc, hψ, hRange, hx1⟩ := exists_smooth_tsupport_subset hnear
  have hsU : tsupport ψ ⊆ U := fun y hy => (hs hy).1
  have hnn (y : CoordinateSpace) : 0 ≤ -(ψ y * f y) := by
    by_cases hy : ψ y = 0
    · simp [hy]
    · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hRange (mem_range_self y)).1
        ((hs (subset_tsupport ψ hy)).2.le))
  have hne : -(ψ x * f x) ≠ 0 := by rw [hx1, one_mul]; exact neg_ne_zero.mpr hn'.ne
  have hw := (continuous_test_mul_continuousOn hU hψ.continuous hsU hf).neg
  have hwc : HasCompactSupport (fun y => -(ψ y * f y)) := hc.mul_right.neg
  have hp := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hwc hnn hne
  rw [integral_neg] at hp
  linarith [h ψ hψ hc hsU]

private theorem continuousOn_eq_of_equal_tests {U : Set CoordinateSpace} (hU : IsOpen U)
    {f g : CoordinateSpace → ℝ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (h : ∀ ψ : CoordinateSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ x, ψ x * f x) = ∫ x, ψ x * g x) : EqOn f g U := by
  have hle (f g : CoordinateSpace → ℝ) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
      (h : ∀ ψ : CoordinateSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        (∫ x, ψ x * f x) = ∫ x, ψ x * g x) : ∀ x ∈ U, g x ≤ f x := by
    refine fun x hx => sub_nonneg.mp (continuousOn_nonneg_of_tests hU (hf.sub hg) ?_ x hx)
    intro ψ hψ hc hs
    have hi := integrable_test_mul_continuousOn hU hψ.continuous hc hs hf
    have hj := integrable_test_mul_continuousOn hU hψ.continuous hc hs hg
    change 0 ≤ ∫ y, ψ y * (f y - g y)
    simp only [mul_sub]
    rw [integral_sub hi hj, h ψ hψ hc hs, sub_self]
  intro x hx
  exact le_antisymm (hle g f hg hf (fun ψ hs hc hsub => (h ψ hs hc hsub).symm) x hx) (hle f g hf hg h x hx)

theorem weak_coordinate_derivatives_commute {U : Set CoordinateSpace} (hU : IsOpen U) {d e : Index}
    {f Fd Fe Gde Ged : CoordinateSpace → ℝ}
    (hd : WeakCoordinateDerivativeOn U d f Fd) (he : WeakCoordinateDerivativeOn U e f Fe)
    (hde : WeakCoordinateDerivativeOn U d Fe Gde) (hed : WeakCoordinateDerivativeOn U e Fd Ged)
    (hGde : ContinuousOn Gde U) (hGed : ContinuousOn Ged U) : EqOn Gde Ged U := by
  apply continuousOn_eq_of_equal_tests hU hGde hGed
  intro ψ hψ hc hs
  have h1 := he (directionalDerivative d ψ) (directionalDerivative_contDiff hψ d)
    (directionalDerivative_hasCompactSupport hc d) ((directionalDerivative_tsupport_subset ψ d).trans hs)
  have h2 := hd (directionalDerivative e ψ) (directionalDerivative_contDiff hψ e)
    (directionalDerivative_hasCompactSupport hc e) ((directionalDerivative_tsupport_subset ψ e).trans hs)
  have hEq : directionalDerivative e (directionalDerivative d ψ) =
      directionalDerivative d (directionalDerivative e ψ) := by
    funext x
    have hC : ContDiffAt ℝ 2 ψ x := ((contDiff_infty.mp hψ) 2).contDiffAt
    unfold directionalDerivative
    rw [scalar_directional_fderiv _ _ _ _ hC, scalar_directional_fderiv _ _ _ _ hC]
    exact hC.isSymmSndFDerivAt (by simp) _ _
  rw [hEq, h2, hed ψ hψ hc hs, hde ψ hψ hc hs] at h1
  linarith

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter Matrix Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.SmoothMetricConnection
open scoped BigOperators ContDiff Topology

def parallelFrameVelocity (Γ : CoordinateSpace → Connection) (E : CoordinateSpace → FrameMatrix)
    (d : Index) (x : CoordinateSpace) : FrameMatrix := -(connectionMatrix (Γ x) d * E x)

def IsWeakParallelFrameOn (U : Set CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (E : CoordinateSpace → FrameMatrix) : Prop :=
  ∀ d a i : Index, WeakCoordinateDerivativeOn U d (fun x => E x a i)
    (fun x => parallelFrameVelocity Γ E d x a i)

private def parallelFrameSecondField (Γ : CoordinateSpace → Connection) (E : CoordinateSpace → FrameMatrix)
    (d e : Index) (x : CoordinateSpace) : FrameMatrix :=
  -(connectionMatrixDerivative Γ x d e * E x + connectionMatrix (Γ x) e * parallelFrameVelocity Γ E d x)

private theorem parallelFrameVelocity_entry_continuousOn {U : Set CoordinateSpace}
    (Γ : CoordinateSpace → Connection) (E : CoordinateSpace → FrameMatrix)
    (hΓ : ∀ a b c, ContinuousOn (fun x => Γ x a b c) U)
    (hE : ∀ a b, ContinuousOn (fun x => E x a b) U) (d a i : Index) :
    ContinuousOn (fun x => parallelFrameVelocity Γ E d x a i) U := by
  simp only [parallelFrameVelocity, Matrix.neg_apply, Matrix.mul_apply, connectionMatrix]
  exact (continuousOn_finset_sum _ (fun k _ => (hΓ a d k).mul (hE k i))).neg

private theorem weakParallelFrameSecondField {U : Set CoordinateSpace} (hU : IsOpen U)
    (Γ : CoordinateSpace → Connection) (E : CoordinateSpace → FrameMatrix)
    (hΓ : ∀ a b c, ContDiffOn ℝ ∞ (fun x => Γ x a b c) U)
    (hE : ∀ a b, ContinuousOn (fun x => E x a b) U) (hPar : IsWeakParallelFrameOn U Γ E)
    (d e a i : Index) :
    WeakCoordinateDerivativeOn U d (fun x => parallelFrameVelocity Γ E e x a i)
      (fun x => parallelFrameSecondField Γ E d e x a i) ∧
      ContinuousOn (fun x => parallelFrameSecondField Γ E d e x a i) U := by
  have hVel (k : Index) := parallelFrameVelocity_entry_continuousOn Γ E
    (fun a b c => (hΓ a b c).continuousOn) hE d k i
  have hg (k : Index) : ContinuousOn (fun x => Γ x a e k * E x k i) U := (hΓ a e k).continuousOn.mul (hE k i)
  have hh (k : Index) : ContinuousOn (fun x => directionalDerivative d (fun y => Γ y a e k) x * E x k i +
      Γ x a e k * parallelFrameVelocity Γ E d x k i) U :=
    (((directionalDerivative_contDiffOn hU (hΓ a e k) d).continuousOn).mul (hE k i)).add
      ((hΓ a e k).continuousOn.mul (hVel k))
  have hsum := WeakCoordinateDerivativeOn.sum hU (d := d) Finset.univ
    (fun k _ => hg k) (fun k _ => hh k)
    (fun k _ => (hPar d k i).mul_smooth hU (hE k i) (hVel k) (hΓ a e k))
  have hcontinuous := (continuousOn_finset_sum Finset.univ (fun k _ => hh k)).neg
  constructor
  · simpa only [parallelFrameVelocity, parallelFrameSecondField, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.add_apply, connectionMatrix, connectionMatrixDerivative, coordinateConnectionJet,
      directionalDerivative, Finset.sum_add_distrib] using hsum.neg
  · simpa only [parallelFrameVelocity, parallelFrameSecondField, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.add_apply, connectionMatrix, connectionMatrixDerivative, coordinateConnectionJet,
      directionalDerivative, Finset.sum_add_distrib] using hcontinuous

theorem coordinateRiemann_eq_zero_of_weak_parallel_frame {U : Set CoordinateSpace} (hU : IsOpen U)
    (E : CoordinateSpace → FrameMatrix) (Γ : CoordinateSpace → Connection)
    (hE : ∀ a b, ContinuousOn (fun x => E x a b) U)
    (hΓ : ∀ a b c, ContDiffOn ℝ ∞ (fun x => Γ x a b c) U)
    (hInv : ∀ x ∈ U, IsUnit (E x).det) (hPar : IsWeakParallelFrameOn U Γ E)
    (x : CoordinateSpace) (hx : x ∈ U) (d e : Index) : coordinateRiemann Γ x d e = 0 := by
  have hEq : parallelFrameSecondField Γ E d e x = parallelFrameSecondField Γ E e d x := by
    ext a i
    have hde := weakParallelFrameSecondField hU Γ E hΓ hE hPar d e a i
    have hed := weakParallelFrameSecondField hU Γ E hΓ hE hPar e d a i
    exact weak_coordinate_derivatives_commute hU (hPar d a i) (hPar e a i)
      hde.1 hed.1 hde.2 hed.2 hx
  exact coordinateRiemann_eq_zero_of_commuting_parallel_products Γ x (E x) d e (hInv x hx) hEq

theorem coordinateRiemann_computedConnection_eq_zero_of_weak_parallel_frame
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => metricComponents g y i j) U)
    (hn : ∀ x ∈ U, (g x).Nondegenerate) (E : CoordinateSpace → FrameMatrix)
    (hE : ∀ i j, ContinuousOn (fun y => E y i j) U) (hInv : ∀ x ∈ U, IsUnit (E x).det)
    (hPar : IsWeakParallelFrameOn U (computedConnection g) E)
    (x : CoordinateSpace) (hx : x ∈ U) (d e : Index) : coordinateRiemann (computedConnection g) x d e = 0 :=
  coordinateRiemann_eq_zero_of_weak_parallel_frame hU E (computedConnection g) hE
    (contDiffOn_computedConnection g U hU hg hn) hInv hPar x hx d e

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter Matrix MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection
open Burnett.Analysis.LocalWeakDerivative
open scoped BigOperators ContDiff Topology

def LocalWeakStarOn (U : Set CoordinateSpace) (fₙ : ℕ → CoordinateSpace → ℝ)
    (f : CoordinateSpace → ℝ) : Prop :=
  ∀ K : Set CoordinateSpace, IsCompact K → K ⊆ U → ∀ w : CoordinateSpace → ℝ,
    IntegrableOn w K → Tendsto (fun n => ∫ x in K, w x * fₙ n x) atTop (𝓝 (∫ x in K, w x * f x))

theorem IsWeakParallelFrameOn.of_smooth {U : Set CoordinateSpace} (hU : IsOpen U)
    (Γ : CoordinateSpace → Connection) (E : CoordinateSpace → FrameMatrix)
    (hE : ∀ a i, ContDiffOn ℝ ∞ (fun x => E x a i) U)
    (hPar : ∀ x ∈ U, ∀ d, frameCoordinateJet E x d = parallelFrameVelocity Γ E d x) :
    IsWeakParallelFrameOn U Γ E := by
  intro d a i ψ hψ hc hs
  have h := integral_test_directional_local hU hψ hc hs (hE a i) (EuclideanSpace.single d 1)
  have he : (∫ x, ψ x * directionalDerivative d (fun y => E y a i) x) =
      ∫ x, ψ x * parallelFrameVelocity Γ E d x a i := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ U
      · exact congrArg (fun M : FrameMatrix => ψ x * M a i) (hPar x hx d)
      · have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
        simp [hzero]
  change (∫ x, ψ x * directionalDerivative d (fun y => E y a i) x) =
    -(∫ x, directionalDerivative d ψ x * E x a i) at h
  rw [he] at h
  linarith

private theorem integral_supported_uniform_error {ψ f : CoordinateSpace → ℝ}
    {fₙ Aₙ : ℕ → CoordinateSpace → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hf : TendstoUniformlyOn fₙ f atTop (tsupport ψ)) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ n x, x ∈ tsupport ψ → ‖Aₙ n x‖ ≤ C) :
    Tendsto (fun n => ∫ x, ψ x * (fₙ n x - f x) * Aₙ n x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let J := ∫ x, ‖ψ x‖
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  have hd : 0 < C * J + 1 := by positivity
  let δ := ε / (C * J + 1)
  have hδ : 0 < δ := div_pos hε hd
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf δ hδ] with n hn
  rw [dist_zero_right]
  have hbound (x : CoordinateSpace) : ‖ψ x * (fₙ n x - f x) * Aₙ n x‖ ≤ δ * C * ‖ψ x‖ := by
    by_cases hx : x ∈ tsupport ψ
    · have hdiff : ‖fₙ n x - f x‖ ≤ δ := by
        rw [← dist_eq_norm, dist_comm]
        exact (hn x hx).le
      rw [norm_mul, norm_mul]
      calc
        _ ≤ (‖ψ x‖ * δ) * C := mul_le_mul (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _))
          (hA n x hx) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hδ.le)
        _ = _ := by ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hpi : Integrable ψ (volume : Measure CoordinateSpace) := hψ.integrable_of_hasCompactSupport hc
  have hp := hpi.norm.const_mul (δ * C)
  calc
    _ ≤ ∫ x, δ * C * ‖ψ x‖ := norm_integral_le_of_norm_le hp (Eventually.of_forall hbound)
    _ = δ * (C * J) := by rw [integral_const_mul, mul_assoc]
    _ < δ * (C * J + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = ε := div_mul_cancel₀ _ hd.ne'

theorem tendsto_mixed_pairing_of_uniform_and_weakStar {U : Set CoordinateSpace} (hU : IsOpen U)
    {ψ f A : CoordinateSpace → ℝ} {fₙ Aₙ : ℕ → CoordinateSpace → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U)
    (hf : ContinuousOn f U) (hfₙ : ∀ n, ContinuousOn (fₙ n) U)
    (hAₙ : ∀ n, ContinuousOn (Aₙ n) U)
    (hfu : TendstoUniformlyOn fₙ f atTop (tsupport ψ)) (hAw : LocalWeakStarOn U Aₙ A)
    {C : ℝ} (hC : 0 ≤ C) (hAb : ∀ n x, x ∈ tsupport ψ → ‖Aₙ n x‖ ≤ C) :
    Tendsto (fun n => ∫ x, ψ x * fₙ n x * Aₙ n x) atTop (𝓝 (∫ x, ψ x * f x * A x)) := by
  have herr := integral_supported_uniform_error hψ hc hfu hC hAb
  have hw : IntegrableOn (fun x => ψ x * f x) (tsupport ψ) :=
    (integrable_test_mul_continuousOn hU hψ hc hs hf).integrableOn
  have he (G : CoordinateSpace → ℝ) :
      (∫ x in tsupport ψ, ψ x * f x * G x) = ∫ x, ψ x * f x * G x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hfix := hAw (tsupport ψ) hc hs _ hw
  have hfixSeq : (fun n => ∫ x in tsupport ψ, ψ x * f x * Aₙ n x) =
      (fun n => ∫ x, ψ x * f x * Aₙ n x) := funext fun n => he (Aₙ n)
  rw [hfixSeq, he A] at hfix
  have hsum (n : ℕ) : (∫ x, ψ x * (fₙ n x - f x) * Aₙ n x) + (∫ x, ψ x * f x * Aₙ n x) =
      ∫ x, ψ x * fₙ n x * Aₙ n x := by
    have hi : Integrable (fun x => ψ x * (fₙ n x - f x) * Aₙ n x) := by
      have hj := integrable_test_mul_continuousOn hU hψ hc hs (((hfₙ n).sub hf).mul (hAₙ n))
      simpa only [← mul_assoc] using hj
    have hj : Integrable (fun x => ψ x * f x * Aₙ n x) := by
      simpa only [← mul_assoc] using integrable_test_mul_continuousOn hU hψ hc hs (hf.mul (hAₙ n))
    rw [← integral_add hi hj]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  simpa only [hsum, zero_add] using herr.add hfix

private theorem tendsto_single_pairing_of_uniform {U : Set CoordinateSpace} (hU : IsOpen U)
    {ψ f : CoordinateSpace → ℝ} {fₙ : ℕ → CoordinateSpace → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U)
    (hf : ContinuousOn f U) (hfₙ : ∀ n, ContinuousOn (fₙ n) U)
    (hfu : TendstoUniformlyOn fₙ f atTop (tsupport ψ)) :
    Tendsto (fun n => ∫ x, ψ x * fₙ n x) atTop (𝓝 (∫ x, ψ x * f x)) := by
  have hA : LocalWeakStarOn U (fun _ _ => 1) (fun _ => 1) := fun _ _ _ _ _ => tendsto_const_nhds
  simpa only [mul_one] using tendsto_mixed_pairing_of_uniform_and_weakStar hU hψ hc hs hf hfₙ
    (fun _ => continuousOn_const) hfu hA zero_le_one (fun _ _ _ => by simp)

theorem isWeakParallelFrameOn_of_local_uniform_limit {U : Set CoordinateSpace} (hU : IsOpen U)
    (Γₙ : ℕ → CoordinateSpace → Connection) (Γ : CoordinateSpace → Connection)
    (Eₙ : ℕ → CoordinateSpace → FrameMatrix) (E : CoordinateSpace → FrameMatrix)
    (hEₙ : ∀ n a i, ContDiffOn ℝ ∞ (fun x => Eₙ n x a i) U)
    (hE : ∀ a i, ContinuousOn (fun x => E x a i) U)
    (hΓₙ : ∀ n a d k, ContinuousOn (fun x => Γₙ n x a d k) U)
    (hΓ : ∀ a d k, ContinuousOn (fun x => Γ x a d k) U)
    (hPar : ∀ n x, x ∈ U → ∀ d, frameCoordinateJet (Eₙ n) x d = parallelFrameVelocity (Γₙ n) (Eₙ n) d x)
    (hUniform : ∀ K : Set CoordinateSpace, IsCompact K → K ⊆ U → ∀ a i,
      TendstoUniformlyOn (fun n x => Eₙ n x a i) (fun x => E x a i) atTop K)
    (hWeak : ∀ a d k, LocalWeakStarOn U (fun n x => Γₙ n x a d k) (fun x => Γ x a d k))
    (hBound : ∀ K : Set CoordinateSpace, IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ K → ∀ a d k, ‖Γₙ n x a d k‖ ≤ C) : IsWeakParallelFrameOn U Γ E := by
  intro d a i ψ hψ hc hs
  obtain ⟨C, hC, hCΓ⟩ := hBound (tsupport ψ) hc hs
  have hψd := directionalDerivative_contDiff hψ d
  have hcd := directionalDerivative_hasCompactSupport hc d
  have hsd := (directionalDerivative_tsupport_subset ψ d).trans hs
  have hL := tendsto_single_pairing_of_uniform hU hψd.continuous hcd hsd (hE a i)
    (fun n => (hEₙ n a i).continuousOn) (hUniform _ hcd hsd a i)
  have hTerm (k : Index) := tendsto_mixed_pairing_of_uniform_and_weakStar hU hψ.continuous hc hs
    (hE k i) (fun n => (hEₙ n k i).continuousOn) (fun n => hΓₙ n a d k)
    (hUniform _ hc hs k i) (hWeak a d k) hC (fun n x hx => hCΓ n x hx a d k)
  have hsum := tendsto_finset_sum (Finset.univ : Finset Index) (fun k _ => hTerm k)
  have he (A : CoordinateSpace → Connection) (F : CoordinateSpace → FrameMatrix)
      (hA : ∀ a d k, ContinuousOn (fun x => A x a d k) U)
      (hF : ∀ a i, ContinuousOn (fun x => F x a i) U) :
      -(∫ x, ψ x * parallelFrameVelocity A F d x a i) =
      ∑ k, ∫ x, ψ x * F x k i * A x a d k := by
    simp only [parallelFrameVelocity, Matrix.neg_apply, Matrix.mul_apply, connectionMatrix,
      mul_neg, integral_neg, neg_neg, Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    · intro k _
      exact integrable_test_mul_continuousOn hU hψ.continuous hc hs ((hA a d k).mul (hF k i))
  have hR : Tendsto (fun n => -(∫ x, ψ x * parallelFrameVelocity (Γₙ n) (Eₙ n) d x a i)) atTop
      (𝓝 (-(∫ x, ψ x * parallelFrameVelocity Γ E d x a i))) := by
    simpa only [he Γ E hΓ hE, he (Γₙ _) (Eₙ _) (hΓₙ _) (fun b j => (hEₙ _ b j).continuousOn)] using hsum
  have hEq (n : ℕ) : (∫ x, directionalDerivative d ψ x * Eₙ n x a i) =
      -(∫ x, ψ x * parallelFrameVelocity (Γₙ n) (Eₙ n) d x a i) :=
    IsWeakParallelFrameOn.of_smooth hU (Γₙ n) (Eₙ n) (hEₙ n) (hPar n) d a i ψ hψ hc hs
  exact tendsto_nhds_unique (hL.congr hEq) hR

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter MeasureTheory Set
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology

theorem exists_smooth_cutoff_on_compact_chart {K U : Set CoordinateSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set CoordinateSpace, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
      ∃ χ : CoordinateSpace → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ L ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, hfc, _⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  obtain ⟨g, hg, hclose⟩ := (hfc.uniformContinuous_of_continuous f.continuous).exists_contDiff_dist_le
    (show 0 < (1 / 8 : ℝ) by norm_num)
  let η : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let χ : CoordinateSpace → ℝ := fun x => η (g x)
  have hout (x : CoordinateSpace) (hx : x ∉ L) : χ x = 0 := by
    have hfzero : f x = 0 := hf0 (fun h => hx (interior_subset h))
    have hgz : dist (g x) 0 < 1 / 8 := by simpa only [hfzero] using hclose x
    have hd : (1 / 2 : ℝ) ≤ dist (g x) 1 := by
      have hh := dist_triangle (0 : ℝ) (g x) 1
      rw [dist_comm (0 : ℝ) (g x)] at hh
      norm_num [Real.dist_eq] at hh
      rw [Real.dist_eq, sub_zero] at hgz
      rw [Real.dist_eq]
      linarith
    exact η.zero_of_le_dist hd
  have hsupport : tsupport χ ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hnot
    exact hx (hout x hnot)
  refine ⟨L, hL, hKL, hLU, χ, η.contDiff.comp hg, hL.of_isClosed_subset isClosed_closure hsupport,
    hsupport, fun x => ⟨η.nonneg' (g x), η.le_one⟩, ?_⟩
  intro x hx
  apply η.one_of_mem_closedBall
  change dist (g x) 1 ≤ 1 / 4
  have hnear : dist (g x) 1 < 1 / 8 := by simpa only [show f x = 1 from hf1 hx] using hclose x
  linarith

private theorem exists_smooth_L1_approx_with_cutoff {L : Set CoordinateSpace} (hL : IsCompact L)
    {χ w : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ L) (hχB : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχw : ∀ x, χ x * w x = w x)
    (hw : Integrable w (volume : Measure CoordinateSpace)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : CoordinateSpace → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ L ∧
      Integrable ψ (volume : Measure CoordinateSpace) ∧ (∫ x in L, ‖w x - ψ x‖) ≤ ε := by
  let μ : Measure CoordinateSpace := volume.restrict L
  have hfinite : μ Set.univ < ⊤ := by
    change (volume.restrict L) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact hL.measure_lt_top
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  obtain ⟨g₀, hcompact, happrox₀, hcont, hg₀⟩ :=
    hw.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  have happ : (∫ x, ‖w x - g₀ x‖ ∂μ) ≤ ε / 2 :=
    (setIntegral_le_integral (hw.sub hg₀).norm (Eventually.of_forall fun _ => norm_nonneg _)).trans happrox₀
  let V := μ.real univ
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let δ := (ε / 2) / (V + 1)
  have hden : 0 < V + 1 := by positivity
  have hδ : 0 < δ := div_pos (half_pos hε) hden
  obtain ⟨g, hg, hclose⟩ := (hcompact.uniformContinuous_of_continuous hcont).exists_contDiff_dist_le hδ
  have hgr : Integrable g μ := hg.continuous.continuousOn.integrableOn_compact hL
  have hw' : Integrable w μ := hw.mono_measure Measure.restrict_le_self
  have hg₀' : Integrable g₀ μ := hg₀.mono_measure Measure.restrict_le_self
  have herr : (∫ x, ‖g₀ x - g x‖ ∂μ) ≤ ε / 2 := by
    have hpoint (x : CoordinateSpace) : ‖g₀ x - g x‖ ≤ δ := by
      rw [← dist_eq_norm, dist_comm]
      exact (hclose x).le
    calc
      (∫ x, ‖g₀ x - g x‖ ∂μ) ≤ ∫ _ : CoordinateSpace, δ ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const _) (Eventually.of_forall hpoint)
      _ = V * δ := by rw [integral_const, smul_eq_mul]
      _ ≤ (V + 1) * δ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
      _ = ε / 2 := by rw [mul_comm]; exact div_mul_cancel₀ _ hden.ne'
  have hsum : (∫ x, ‖w x - g x‖ ∂μ) ≤ (∫ x, ‖w x - g₀ x‖ ∂μ) + ∫ x, ‖g₀ x - g x‖ ∂μ := by
    have h₁ : Integrable (fun x => ‖w x - g₀ x‖) μ := (hw'.sub hg₀').norm
    have h₂ : Integrable (fun x => ‖g₀ x - g x‖) μ := (hg₀'.sub hgr).norm
    rw [← integral_add h₁ h₂]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (h₁.add h₂)
    exact Eventually.of_forall fun x => by
      simpa only [← dist_eq_norm] using dist_triangle (w x) (g₀ x) (g x)
  let ψ : CoordinateSpace → ℝ := fun x => χ x * g x
  have hψ : ContDiff ℝ ∞ ψ := hχ.mul hg
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψs : tsupport ψ ⊆ L := tsupport_mul_subset_left.trans hχs
  have hψi : Integrable ψ (volume : Measure CoordinateSpace) := hψ.continuous.integrable_of_hasCompactSupport hψc
  refine ⟨ψ, hψ, hψc, hψs, hψi, ?_⟩
  have hpoint (x : CoordinateSpace) : ‖w x - ψ x‖ ≤ ‖w x - g x‖ := by
    have hprod : w x - ψ x = χ x * (w x - g x) := by rw [mul_sub, hχw]
    rw [hprod, norm_mul, Real.norm_of_nonneg (hχB x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχB x).2
  have hi : (∫ x, ‖w x - ψ x‖ ∂μ) ≤ ∫ x, ‖w x - g x‖ ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hw'.sub hgr).norm
      (Eventually.of_forall hpoint)
  exact hi.trans (hsum.trans (by linarith))

end Burnett.Geometry.FlatRigidity

namespace Burnett.Geometry.FlatRigidity

open Filter MeasureTheory Set
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology

private theorem bounded_test_pairing_error {μ : Measure CoordinateSpace} {f g q : CoordinateSpace → ℝ}
    {C : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hm : AEStronglyMeasurable q μ) (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ C) :
    dist (∫ x, f x * q x ∂μ) (∫ x, g x * q x ∂μ) ≤ C * ∫ x, ‖f x - g x‖ ∂μ := by
  have hfi : Integrable (fun x => f x * q x) μ := by simpa only [mul_comm] using hf.bdd_mul' hm hb
  have hgi : Integrable (fun x => g x * q x) μ := by simpa only [mul_comm] using hg.bdd_mul' hm hb
  rw [dist_eq_norm, ← integral_sub hfi hgi, ← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hf.sub hg).norm.const_mul C)
  filter_upwards [hb] with x hx
  rw [← sub_mul, norm_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

theorem LocalWeakStarOn.of_compact_smooth_tests {U : Set CoordinateSpace} (hU : IsOpen U)
    {fₙ : ℕ → CoordinateSpace → ℝ} {f : CoordinateSpace → ℝ}
    (hCn : ∀ n, ContinuousOn (fₙ n) U) (hC : ContinuousOn f U)
    (hBound : ∀ L : Set CoordinateSpace, IsCompact L → L ⊆ U → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n x, x ∈ L → ‖fₙ n x‖ ≤ B)
    (hSmooth : ∀ ψ : CoordinateSpace → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      Tendsto (fun n => ∫ x, ψ x * fₙ n x) atTop (𝓝 (∫ x, ψ x * f x))) : LocalWeakStarOn U fₙ f := by
  intro K hK hKU w hw
  obtain ⟨L, hL, hKL, hLU, χ, hχ, hχc, hχs, hχB, hχ1⟩ := exists_smooth_cutoff_on_compact_chart hK hU hKU
  have hKsub : K ⊆ L := hKL.trans interior_subset
  let μ : Measure CoordinateSpace := volume.restrict L
  let w₀ := K.indicator w
  have hw₀ : Integrable w₀ (volume : Measure CoordinateSpace) := hw.integrable_indicator hK.measurableSet
  have hw₀μ : Integrable w₀ μ := hw₀.mono_measure Measure.restrict_le_self
  have hχw (x : CoordinateSpace) : χ x * w₀ x = w₀ x := by
    by_cases hx : x ∈ K
    · simp [hχ1 x hx]
    · simp [w₀, hx]
  have hEq (q : CoordinateSpace → ℝ) : (∫ x, w₀ x * q x ∂μ) = ∫ x in K, w x * q x := by
    calc
      (∫ x, w₀ x * q x ∂μ) = ∫ x, K.indicator (fun y => w y * q y) x ∂μ := by
        apply integral_congr_ae
        refine Eventually.of_forall fun x => ?_
        by_cases hx : x ∈ K <;> simp [w₀, hx]
      _ = _ := by
        rw [integral_indicator hK.measurableSet, show μ = volume.restrict L by rfl,
          Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hKsub]
  have hEqSeq : (fun n => ∫ x, w₀ x * fₙ n x ∂μ) = (fun n => ∫ x in K, w x * fₙ n x) :=
    funext fun n => hEq (fₙ n)
  rw [← hEqSeq, ← hEq f]
  obtain ⟨B, hB, hBn⟩ := hBound L hL hLU
  obtain ⟨D, hD⟩ := hL.bddAbove_image (hC.mono hLU).norm
  let C := max B D
  have hC₀ : 0 ≤ C := hB.trans (le_max_left _ _)
  have hLm : ∀ᵐ x ∂μ, x ∈ L := ae_restrict_mem hL.measurableSet
  have hBnμ (n : ℕ) : ∀ᵐ x ∂μ, ‖fₙ n x‖ ≤ C := hLm.mono fun x hx => (hBn n x hx).trans (le_max_left _ _)
  have hBμ : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := hLm.mono fun x hx =>
    (hD (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  have hmₙ (n : ℕ) : AEStronglyMeasurable (fₙ n) μ := ((hCn n).mono hLU).aestronglyMeasurable hL.measurableSet
  have hm : AEStronglyMeasurable f μ := (hC.mono hLU).aestronglyMeasurable hL.measurableSet
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := (ε / 8) / (C + 1)
  have hden : 0 < C + 1 := by positivity
  have hδ : 0 < δ := by positivity
  obtain ⟨ψ, hψ, hψc, hψs, hψi, happ⟩ := exists_smooth_L1_approx_with_cutoff hL hχ hχc hχs hχB hχw hw₀ hδ
  have hψμ : Integrable ψ μ := hψi.mono_measure Measure.restrict_le_self
  have hεerr : C * (∫ x, ‖w₀ x - ψ x‖ ∂μ) ≤ ε / 8 := by
    calc
      _ ≤ C * δ := mul_le_mul_of_nonneg_left happ hC₀
      _ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
      _ = ε / 8 := by rw [mul_comm]; exact div_mul_cancel₀ _ hden.ne'
  have hψeq (q : CoordinateSpace → ℝ) : (∫ x, ψ x * q x ∂μ) = ∫ x, ψ x * q x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun hy => hx (hψs hy))]
  have hψseq : (fun n => ∫ x, ψ x * fₙ n x ∂μ) = (fun n => ∫ x, ψ x * fₙ n x) := funext fun n => hψeq (fₙ n)
  have hψt : Tendsto (fun n => ∫ x, ψ x * fₙ n x ∂μ) atTop (𝓝 (∫ x, ψ x * f x ∂μ)) := by
    rw [hψseq, hψeq f]
    exact hSmooth ψ hψ hψc (hψs.trans hLU)
  filter_upwards [Metric.tendsto_nhds.mp hψt (ε / 2) (half_pos hε)] with n hn
  have h₁ := (bounded_test_pairing_error hw₀μ hψμ (hmₙ n) (hBnμ n)).trans hεerr
  have h₂ := (bounded_test_pairing_error hw₀μ hψμ hm hBμ).trans hεerr
  calc
    _ ≤ dist (∫ x, w₀ x * fₙ n x ∂μ) (∫ x, ψ x * fₙ n x ∂μ) +
        (dist (∫ x, ψ x * fₙ n x ∂μ) (∫ x, ψ x * f x ∂μ) +
          dist (∫ x, ψ x * f x ∂μ) (∫ x, w₀ x * f x ∂μ)) :=
      (dist_triangle _ _ _).trans (add_le_add_left (dist_triangle _ _ _) _)
    _ < ε := by rw [dist_comm (∫ x, ψ x * f x ∂μ)]; linarith

end Burnett.Geometry.FlatRigidity
