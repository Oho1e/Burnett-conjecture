import Burnett.Geometry.FiberMetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The exact coordinate connection difference

Christoffel coefficients and covariant derivatives are computed from metric
components and their first derivatives. The algebraic first-jet identities
are followed by an application to actual Frechet coordinate derivatives.
No curvature, distributional convergence, or manifold naturality is asserted.
-/

noncomputable section

namespace Burnett.Geometry.ConnectionDifference

open scoped BigOperators
open scoped Topology
open Burnett.RicciSymbol

abbrev FirstJet := Index → Tensor2
abbrev Connection := Index → Index → Index → ℝ

/-- The Christoffel coefficients with their upper index lowered. The jet's
first index is the coordinate derivative index. -/
def koszul (dg : FirstJet) (b c d : Index) : ℝ :=
  (dg b c d + dg c b d - dg d b c) / 2

/-- Actual finite-sum Christoffel construction from an inverse metric and a
first derivative array. -/
def christoffel (gInv : Tensor2) (dg : FirstJet) : Connection := fun a b c =>
  ∑ d, gInv a d * koszul dg b c d

/-- The covariant derivative of a covariant two-tensor, in coordinates. -/
def covariantJet (Γ : Connection) (h : Tensor2) (dh : FirstJet) : FirstJet := fun b c d =>
  dh b c d - (∑ e, Γ e b c * h e d) - ∑ e, Γ e b d * h c e

theorem koszul_sub (dg dk : FirstJet) (b c d : Index) :
    koszul (dg - dk) b c d = koszul dg b c d - koszul dk b c d := by
  simp only [koszul, Pi.sub_apply]
  ring

theorem christoffel_torsion_free (gInv : Tensor2) (dg : FirstJet)
    (hs : ∀ d, IsSymmetricTensor (dg d)) (a b c : Index) :
    christoffel gInv dg a b c = christoffel gInv dg a c b := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [koszul, koszul, hs d b c]
  ring

theorem inverse_contract (g gInv : Tensor2)
    (hi : ∀ a e, (∑ d, gInv a d * g d e) = if a = e then 1 else 0)
    (v : Covector) (a : Index) :
    (∑ d, gInv a d * (∑ e, g d e * v e)) = v a := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hi]
  simp [ite_mul]

theorem lower_christoffel (g gInv : Tensor2) (dg : FirstJet)
    (hi : ∀ d e, (∑ a, g d a * gInv a e) = if d = e then 1 else 0)
    (b c d : Index) :
    (∑ a, g d a * christoffel gInv dg a b c) = koszul dg b c d :=
  inverse_contract gInv g hi (fun e => koszul dg b c e) d

/-- The constructed connection is metric compatible; this is a consequence
of the inverse identity and jet symmetry, not an input connection field. -/
theorem christoffel_metric_compatible (g gInv : Tensor2) (dg : FirstJet)
    (hg : IsSymmetricTensor g) (hs : ∀ d, IsSymmetricTensor (dg d))
    (hi : ∀ d e, (∑ a, g d a * gInv a e) = if d = e then 1 else 0)
    (b c d : Index) : covariantJet (christoffel gInv dg) g dg b c d = 0 := by
  have h1 : (∑ e, christoffel gInv dg e b c * g e d) = koszul dg b c d := by
    have hh := lower_christoffel g gInv dg hi b c d
    simpa only [hg _ d, mul_comm] using hh
  have h2 : (∑ e, christoffel gInv dg e b d * g c e) = koszul dg b d c := by
    simpa only [mul_comm] using lower_christoffel g gInv dg hi b d c
  unfold covariantJet
  rw [h1, h2]
  simp only [koszul, hs b d c]
  ring

/-- The two unwanted connection terms cancel by symmetry and zero torsion.
The result is the tensorial form of the Koszul combination. -/
theorem koszul_covariantJet (Γ : Connection) (h : Tensor2) (dh : FirstJet)
    (hΓ : ∀ e b c, Γ e b c = Γ e c b) (hh : IsSymmetricTensor h) (b c d : Index) :
    koszul (covariantJet Γ h dh) b c d =
      koszul dh b c d - ∑ e, Γ e b c * h e d := by
  have h1 : (∑ e, Γ e c b * h e d) = ∑ e, Γ e b c * h e d := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hΓ e c b]
  have h2 : (∑ e, Γ e d b * h e c) = ∑ e, Γ e b d * h c e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hΓ e d b, hh e c]
  have h3 : (∑ e, Γ e d c * h b e) = ∑ e, Γ e c d * h b e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hΓ e d c]
  simp only [koszul, covariantJet]
  rw [h1, h2, h3]
  ring

/-- Exact first-jet connection-difference algebra. Both connections are
computed, and only ordinary inverse-matrix identities are assumptions.
The later metric-fiber theorem discharges those identities from actual
nondegenerate bilinear forms. -/
theorem christoffel_difference (g₀ g₁ inv₀ inv₁ : Tensor2) (dg₀ dg₁ : FirstJet)
    (hg₀ : IsSymmetricTensor g₀) (hg₁ : IsSymmetricTensor g₁)
    (hdg₀ : ∀ d, IsSymmetricTensor (dg₀ d))
    (hi₀ : ∀ d e, (∑ a, g₀ d a * inv₀ a e) = if d = e then 1 else 0)
    (hi₁ : ∀ a e, (∑ d, inv₁ a d * g₁ d e) = if a = e then 1 else 0)
    (a b c : Index) :
    christoffel inv₁ dg₁ a b c - christoffel inv₀ dg₀ a b c =
      christoffel inv₁
        (covariantJet (christoffel inv₀ dg₀) (g₁ - g₀) (dg₁ - dg₀)) a b c := by
  have hh : IsSymmetricTensor (g₁ - g₀) := fun i j => by
    simp only [Pi.sub_apply, hg₁ i j, hg₀ i j]
  have hΓ : ∀ e i j, christoffel inv₀ dg₀ e i j = christoffel inv₀ dg₀ e j i :=
    christoffel_torsion_free inv₀ dg₀ hdg₀
  have hc (d : Index) :
      koszul (covariantJet (christoffel inv₀ dg₀) (g₁ - g₀) (dg₁ - dg₀)) b c d =
        koszul dg₁ b c d - ∑ e, g₁ d e * christoffel inv₀ dg₀ e b c := by
    rw [koszul_covariantJet _ _ _ hΓ hh, koszul_sub,
      ← lower_christoffel g₀ inv₀ dg₀ hi₀ b c d]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have hs₀ : (∑ e, christoffel inv₀ dg₀ e b c * g₀ e d) =
        ∑ e, g₀ d e * christoffel inv₀ dg₀ e b c := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hg₀ e d, mul_comm]
    have hs₁ : (∑ e, christoffel inv₀ dg₀ e b c * g₁ e d) =
        ∑ e, g₁ d e * christoffel inv₀ dg₀ e b c := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hg₁ e d, mul_comm]
    rw [hs₀, hs₁]
    ring
  simp only [christoffel, hc, mul_sub, Finset.sum_sub_distrib]
  have hi := inverse_contract g₁ inv₁ hi₁ (fun e => christoffel inv₀ dg₀ e b c) a
  simpa only [christoffel] using congrArg
    (fun t => (∑ d, inv₁ a d * koszul dg₁ b c d) - t) hi.symm

/-! The remaining definitions use actual coordinate Frechet derivatives.
Total functions represent a local coordinate germ; assumptions below only
concern the point or its neighborhood, not the whole coordinate space. -/

abbrev CoordinateSpace := EuclideanSpace ℝ Index

def coordinateBasis : Module.Basis Index ℝ CoordinateSpace :=
  (EuclideanSpace.basisFun Index ℝ).toBasis

def coordinateJet (g : CoordinateSpace → Tensor2) (x : CoordinateSpace) : FirstJet :=
  fun d a b => fderiv ℝ (fun y => g y a b) x (EuclideanSpace.single d 1)

def DifferentiableComponentsAt (g : CoordinateSpace → Tensor2) (x : CoordinateSpace) : Prop :=
  ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x

theorem coordinateJet_symmetric (g : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hs : ∀ᶠ y in 𝓝 x, IsSymmetricTensor (g y)) :
    ∀ d, IsSymmetricTensor (coordinateJet g x d) := by
  intro d a b
  have heq : (fun y => g y a b) =ᶠ[𝓝 x] (fun y => g y b a) :=
    hs.mono (fun y hy => hy a b)
  exact congrArg (fun f : CoordinateSpace →L[ℝ] ℝ => f (EuclideanSpace.single d 1))
    heq.fderiv_eq

/-- Values outside a neighborhood cannot affect the coordinate first jet.
This makes the total-function representation a local coordinate germ. -/
theorem coordinateJet_congr (g k : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (heq : g =ᶠ[𝓝 x] k) : coordinateJet g x = coordinateJet k x := by
  funext d a b
  have hc : (fun y => g y a b) =ᶠ[𝓝 x] (fun y => k y a b) :=
    heq.mono fun y hy => congrFun (congrFun hy a) b
  exact congrArg (fun f : CoordinateSpace →L[ℝ] ℝ => f (EuclideanSpace.single d 1))
    hc.fderiv_eq

theorem coordinateJet_sub (g₁ g₀ : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hd₁ : DifferentiableComponentsAt g₁ x) (hd₀ : DifferentiableComponentsAt g₀ x) :
    coordinateJet (fun y => g₁ y - g₀ y) x = coordinateJet g₁ x - coordinateJet g₀ x := by
  funext d a b
  simp only [coordinateJet, Pi.sub_apply]
  rw [fderiv_fun_sub (hd₁ a b) (hd₀ a b), ContinuousLinearMap.sub_apply]

def metricComponents (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) :
    CoordinateSpace → Tensor2 := fun x => FiberMetric.covariant (g x) coordinateBasis

/-- Only the metric value at this point is used to construct the inverse. -/
def metricInverse (g : LinearMap.BilinForm ℝ CoordinateSpace) (hg : g.Nondegenerate) : Tensor2 :=
  FiberMetric.contravariant g hg coordinateBasis

/-- This is a computed Christoffel array, using the true first derivative of
the metric components. Nondegeneracy is required only at the point x. -/
def metricConnection (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hg : (g x).Nondegenerate) : Connection :=
  christoffel (metricInverse (g x) hg) (coordinateJet (metricComponents g) x)

/-- The perturbation and its background covariant derivative are actual
coordinate components and Frechet derivatives of the difference field. -/
def perturbationCovariantJet
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hg₀ : (g₀ x).Nondegenerate) : FirstJet :=
  covariantJet (metricConnection g₀ x hg₀)
    (metricComponents g₁ x - metricComponents g₀ x)
    (coordinateJet (fun y => metricComponents g₁ y - metricComponents g₀ y) x)

/-- The exact connection difference for true metric fields in coordinates.
The hypotheses are local: symmetry on a neighborhood, differentiability and
nondegeneracy at x. No global extension, global nondegeneracy, or smoothness
of an inverse field is supplied or required. -/
theorem metricConnection_difference
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate)
    (hs₀ : ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm) (hs₁ : ∀ᶠ y in 𝓝 x, (g₁ y).IsSymm)
    (hd₀ : DifferentiableComponentsAt (metricComponents g₀) x)
    (hd₁ : DifferentiableComponentsAt (metricComponents g₁) x) (a b c : Index) :
    metricConnection g₁ x hn₁ a b c - metricConnection g₀ x hn₀ a b c =
      christoffel (metricInverse (g₁ x) hn₁) (perturbationCovariantJet g₀ g₁ x hn₀) a b c := by
  have hsym₀ := hs₀.self_of_nhds
  have hsym₁ := hs₁.self_of_nhds
  have hj₀ : ∀ d, IsSymmetricTensor (coordinateJet (metricComponents g₀) x d) :=
    coordinateJet_symmetric _ x (hs₀.mono fun y hy => FiberMetric.covariant_symmetric _ hy _)
  unfold metricConnection perturbationCovariantJet
  rw [coordinateJet_sub _ _ x hd₁ hd₀]
  exact christoffel_difference _ _ _ _ _ _
    (FiberMetric.covariant_symmetric _ hsym₀ _) (FiberMetric.covariant_symmetric _ hsym₁ _)
    hj₀ (FiberMetric.covariant_mul_contravariant _ hn₀ hsym₀ coordinateBasis)
    (FiberMetric.contravariant_mul_covariant _ hn₁ hsym₁ coordinateBasis) a b c

/-- Open-chart version: all regularity and symmetry assumptions are on U,
and the two nondegeneracy assumptions only concern its chosen point x.
The arbitrary total-function values away from U have no geometric meaning. -/
theorem metricConnection_difference_on
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hx : x ∈ U)
    (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate)
    (hs₀ : ∀ y ∈ U, (g₀ y).IsSymm) (hs₁ : ∀ y ∈ U, (g₁ y).IsSymm)
    (hd₀ : ∀ a b, DifferentiableOn ℝ (fun y => metricComponents g₀ y a b) U)
    (hd₁ : ∀ a b, DifferentiableOn ℝ (fun y => metricComponents g₁ y a b) U)
    (a b c : Index) :
    metricConnection g₁ x hn₁ a b c - metricConnection g₀ x hn₀ a b c =
      christoffel (metricInverse (g₁ x) hn₁) (perturbationCovariantJet g₀ g₁ x hn₀) a b c := by
  apply metricConnection_difference g₀ g₁ x hn₀ hn₁
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hs₀ y hy)
  · exact Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hs₁ y hy)
  · intro i j
    exact (hd₀ i j x hx).differentiableAt (hU.mem_nhds hx)
  · intro i j
    exact (hd₁ i j x hx).differentiableAt (hU.mem_nhds hx)

end Burnett.Geometry.ConnectionDifference
