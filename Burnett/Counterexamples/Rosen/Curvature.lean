import Burnett.Counterexamples.Rosen.Scale
import Burnett.Geometry.BackgroundConnection
import Burnett.Geometry.CurvatureDifference
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Rosen multiscale example

The actual connection and Ricci components in both coordinate systems.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale

open Matrix Set Filter
open scoped BigOperators Topology ContDiff
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference

def originalScreenMatrix (s t : ℝ) : CoordinateMetric :=
  !![0, -1, 0, 0;
     -1, 0, 0, 0;
     0, 0, s, 0;
     0, 0, 0, t]

def originalScreenBilinear (s t : ℝ → ℝ) (x : CoordinateSpace) :
    LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis (originalScreenMatrix (s (x 0)) (t (x 0)))

theorem originalScreen_components (s t : ℝ → ℝ) :
    metricComponents (originalScreenBilinear s t) =
      fun x => originalScreenMatrix (s (x 0)) (t (x 0)) := by
  funext x
  calc
    metricComponents (originalScreenBilinear s t) x =
        BilinForm.toMatrix coordinateBasis (originalScreenBilinear s t x) := by
      ext a b
      simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, BilinForm.toMatrix_apply]
    _ = _ := BilinForm.toMatrix_toBilin coordinateBasis _

theorem originalScreen_specialize (B ψ : ℝ → ℝ) (x : CoordinateSpace) :
    metricComponents (originalScreenBilinear
      (fun u => screenX (B u) (ψ u)) (fun u => screenZ (B u) (ψ u))) x =
      originalRosenField B ψ x := by
  rw [originalScreen_components]
  rfl

private theorem originalScreen_inverse (s t : ℝ) (hs : s ≠ 0) (ht : t ≠ 0) :
    matrixInverse (originalScreenMatrix s t) = originalScreenMatrix s⁻¹ t⁻¹ := by
  have h := pulledMetricAt_inv 1 0 0 s t one_ne_zero hs ht
  have hl : pulledMetricAt 1 0 0 s t = originalScreenMatrix s t := by
    simp [pulledMetricAt, originalScreenMatrix]
  have hr : inversePulledMetricAt 1 0 0 s t = originalScreenMatrix s⁻¹ t⁻¹ := by
    simp [inversePulledMetricAt, originalScreenMatrix]
  rw [hl, hr] at h
  exact h

private theorem fderiv_univariate_at_basis (f : ℝ → ℝ) (x : CoordinateSpace)
    (hf : DifferentiableAt ℝ f (x 0)) (d : Index) :
    fderiv ℝ (fun y : CoordinateSpace => f (y 0)) x (EuclideanSpace.single d 1) =
      if d = 0 then deriv f (x 0) else 0 := by
  let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hd := hf.hasDerivAt.hasFDerivAt.comp x π.hasFDerivAt
  change fderiv ℝ (f ∘ π) x _ = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  change (EuclideanSpace.single d (1 : ℝ)) 0 * deriv f (x 0) = _
  by_cases h : d = 0
  · subst d
    simp [EuclideanSpace.single_apply]
  · simp [EuclideanSpace.single_apply, h, Ne.symm h]

private def screenMetricJet (sd td : ℝ) : FirstJet := fun d a b =>
  if d = 0 then (!![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, sd, 0; 0, 0, 0, td] : CoordinateMetric) a b else 0

private theorem originalScreen_jet (s t : ℝ → ℝ) (x : CoordinateSpace)
    (hs : DifferentiableAt ℝ s (x 0)) (ht : DifferentiableAt ℝ t (x 0)) :
    coordinateJet (metricComponents (originalScreenBilinear s t)) x =
      screenMetricJet (deriv s (x 0)) (deriv t (x 0)) := by
  rw [originalScreen_components]
  funext d a b
  fin_cases a <;> fin_cases b <;>
    simp [coordinateJet, screenMetricJet, originalScreenMatrix,
      fderiv_univariate_at_basis s x hs d, fderiv_univariate_at_basis t x ht d]

def explicitScreenConnection (sx sz lx lz : ℝ) : Connection := fun a b c =>
  if a = 1 ∧ b = 2 ∧ c = 2 then sx
  else if a = 1 ∧ b = 3 ∧ c = 3 then sz
  else if a = 2 ∧ ((b = 0 ∧ c = 2) ∨ (b = 2 ∧ c = 0)) then lx
  else if a = 3 ∧ ((b = 0 ∧ c = 3) ∨ (b = 3 ∧ c = 0)) then lz
  else 0

def originalScreenConnection (s t : ℝ → ℝ) (x : CoordinateSpace) : Connection :=
  explicitScreenConnection (deriv s (x 0) / 2) (deriv t (x 0) / 2)
    ((s (x 0))⁻¹ * (deriv s (x 0) / 2)) ((t (x 0))⁻¹ * (deriv t (x 0) / 2))

theorem computedConnection_originalScreen (s t : ℝ → ℝ) (x : CoordinateSpace)
    (hsd : DifferentiableAt ℝ s (x 0)) (htd : DifferentiableAt ℝ t (x 0))
    (hs : s (x 0) ≠ 0) (ht : t (x 0) ≠ 0) :
    computedConnection (originalScreenBilinear s t) x = originalScreenConnection s t x := by
  unfold computedConnection originalScreenConnection
  rw [originalScreen_jet s t x hsd htd, originalScreen_components, originalScreen_inverse _ _ hs ht]
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [christoffel, koszul, originalScreenMatrix, screenMetricJet,
      explicitScreenConnection, Fin.sum_univ_succ]
  all_goals ring

end Burnett.RosenMultiscale

namespace Burnett.RosenMultiscale

open Matrix Set Filter
open scoped BigOperators Topology ContDiff
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference

private theorem local_CD2_deriv {f : ℝ → ℝ} {u : ℝ} (hf : ContDiffAt ℝ 2 f u) :
    DifferentiableAt ℝ (deriv f) u := by
  have hf' : ContDiffAt ℝ ((1 : WithTop ℕ∞) + 1) f u := by
    simpa only [show (1 : WithTop ℕ∞) + 1 = 2 by norm_num] using hf
  have h : ContDiffAt ℝ 1 (deriv f) u := by
    simpa only [deriv] using hf'.fderiv_right_succ.clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => (1 : ℝ)) u)
  exact h.differentiableAt_one

private theorem screenConnectionJet_eq (s t : ℝ → ℝ) (x : CoordinateSpace)
    (hs : ContDiffAt ℝ 2 s (x 0)) (ht : ContDiffAt ℝ 2 t (x 0))
    (hsnz : s (x 0) ≠ 0) (htnz : t (x 0) ≠ 0) :
    coordinateConnectionJet (originalScreenConnection s t) x = fun d a b c =>
      if d = 0 then explicitScreenConnection
        (deriv (fun u => deriv s u / 2) (x 0)) (deriv (fun u => deriv t u / 2) (x 0))
        (deriv (fun u => (s u)⁻¹ * (deriv s u / 2)) (x 0))
        (deriv (fun u => (t u)⁻¹ * (deriv t u / 2)) (x 0)) a b c else 0 := by
  have hsd := (local_CD2_deriv hs).div_const 2
  have htd := (local_CD2_deriv ht).div_const 2
  have hlogS : DifferentiableAt ℝ (fun u => (s u)⁻¹ * (deriv s u / 2)) (x 0) :=
    ((hs.differentiableAt (by norm_num)).inv hsnz).mul hsd
  have hlogT : DifferentiableAt ℝ (fun u => (t u)⁻¹ * (deriv t u / 2)) (x 0) :=
    ((ht.differentiableAt (by norm_num)).inv htnz).mul htd
  funext d a b c
  by_cases h1 : a = 1 ∧ b = 2 ∧ c = 2
  · simp [coordinateConnectionJet, originalScreenConnection, explicitScreenConnection, h1,
      fderiv_univariate_at_basis _ x hsd d]
  by_cases h2 : a = 1 ∧ b = 3 ∧ c = 3
  · simp [coordinateConnectionJet, originalScreenConnection, explicitScreenConnection, h2,
      fderiv_univariate_at_basis _ x htd d]
  by_cases h3 : a = 2 ∧ ((b = 0 ∧ c = 2) ∨ (b = 2 ∧ c = 0))
  · simp [coordinateConnectionJet, originalScreenConnection, explicitScreenConnection, h3,
      fderiv_univariate_at_basis _ x hlogS d]
  by_cases h4 : a = 3 ∧ ((b = 0 ∧ c = 3) ∨ (b = 3 ∧ c = 0))
  · simp [coordinateConnectionJet, originalScreenConnection, explicitScreenConnection, h4,
      fderiv_univariate_at_basis _ x hlogT d]
  simp [coordinateConnectionJet, originalScreenConnection, explicitScreenConnection, h1, h2, h3, h4]

private theorem ricci_explicitScreen (sx sz lx lz dx dz dlx dlz : ℝ) (b c : Index) :
    ricci (explicitScreenConnection sx sz lx lz)
      (fun d a j k => if d = 0 then explicitScreenConnection dx dz dlx dlz a j k else 0) b c =
      if b = 0 ∧ c = 0 then -(dlx + dlz + lx^2 + lz^2) else 0 := by
  fin_cases b <;> fin_cases c <;> simp [ricci, explicitScreenConnection, Fin.sum_univ_succ]
  ring

/-- The actual computed Ricci array of the original Rosen metric has just its uu entry.
    All terms in that entry are ordinary derivatives of the actual screen coefficients. -/
theorem coordinateRicci_originalScreen (s t : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hs : ContDiffOn ℝ 2 s U) (ht : ContDiffOn ℝ 2 t U)
    (hsnz : ∀ u ∈ U, s u ≠ 0) (htnz : ∀ u ∈ U, t u ≠ 0)
    (x : CoordinateSpace) (hx : x 0 ∈ U) (b c : Index) :
    coordinateRicci (computedConnection (originalScreenBilinear s t)) x b c =
    if b = 0 ∧ c = 0 then
      -(deriv (fun u => (s u)⁻¹ * (deriv s u / 2)) (x 0) +
        deriv (fun u => (t u)⁻¹ * (deriv t u / 2)) (x 0) +
        ((s (x 0))⁻¹ * (deriv s (x 0) / 2))^2 + ((t (x 0))⁻¹ * (deriv t (x 0) / 2))^2)
      else 0 := by
  let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  let F := computedConnection (originalScreenBilinear s t)
  let G := originalScreenConnection s t
  have heqPt (p : CoordinateSpace) (hp : p 0 ∈ U) : F p = G p :=
    computedConnection_originalScreen s t p
      ((hs.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
      ((ht.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)) (hsnz _ hp) (htnz _ hp)
  have heq : F =ᶠ[𝓝 x] G := by
    have hNear : ∀ᶠ p in 𝓝 x, p 0 ∈ U := π.continuous.continuousAt (hU.mem_nhds hx)
    filter_upwards [hNear] with p hp
    exact heqPt p hp
  have hjet : coordinateConnectionJet F x = coordinateConnectionJet G x := by
    funext d a i j
    have heqComp : (fun p => F p a i j) =ᶠ[𝓝 x] (fun p => G p a i j) :=
      heq.mono fun _ hp => congrFun (congrFun (congrFun hp a) i) j
    unfold coordinateConnectionJet
    rw [heqComp.fderiv_eq]
  change coordinateRicci F x b c = _
  unfold coordinateRicci
  rw [heqPt x hx, hjet, screenConnectionJet_eq s t x
    (hs.contDiffAt (hU.mem_nhds hx)) (ht.contDiffAt (hU.mem_nhds hx)) (hsnz _ hx) (htnz _ hx)]
  exact ricci_explicitScreen _ _ _ _ _ _ _ _ b c

end Burnett.RosenMultiscale

namespace Burnett.RosenMultiscale

open Matrix Set Filter
open scoped BigOperators Topology ContDiff
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference

private def scaledScreen (c : ℝ) (B ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (B u)^2 * Real.exp (2 * c * ψ u)

private theorem scaledScreen_logDerivative (c : ℝ) (B ψ : ℝ → ℝ) (u : ℝ)
    (hB : DifferentiableAt ℝ B u) (hψ : DifferentiableAt ℝ ψ u) (hb : B u ≠ 0) :
    (scaledScreen c B ψ u)⁻¹ * (deriv (scaledScreen c B ψ) u / 2) =
      deriv B u / B u + c * deriv ψ u := by
  have hExp := (hψ.hasDerivAt.const_mul (2 * c)).exp
  have h := ((hB.hasDerivAt.pow 2).mul hExp).deriv
  change deriv (fun v => (B v)^2 * Real.exp (2 * c * ψ v)) u = _ at h
  simp only [Pi.pow_apply] at h
  unfold scaledScreen
  rw [h]
  field_simp [hb, Real.exp_ne_zero]
  ring

private theorem scaledScreen_logDerivative_germ (c : ℝ) (B ψ : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ 2 B U) (hψ : ContDiffOn ℝ 2 ψ U)
    (hb : ∀ v ∈ U, B v ≠ 0) (u : ℝ) (hu : u ∈ U) :
    (fun v => (scaledScreen c B ψ v)⁻¹ * (deriv (scaledScreen c B ψ) v / 2)) =ᶠ[𝓝 u]
      (fun v => deriv B v / B v + c * deriv ψ v) := by
  filter_upwards [hU.mem_nhds hu] with v hv
  exact scaledScreen_logDerivative c B ψ v
    ((hB.contDiffAt (hU.mem_nhds hv)).differentiableAt (by norm_num))
    ((hψ.contDiffAt (hU.mem_nhds hv)).differentiableAt (by norm_num)) (hb v hv)

/-- The metric is the original, unpulled Rosen metric with the literal opposite exponent screens. -/
def originalRosenBilinear (B ψ : ℝ → ℝ) : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace :=
  originalScreenBilinear (fun u => screenX (B u) (ψ u)) (fun u => screenZ (B u) (ψ u))

theorem originalRosenBilinear_components (B ψ : ℝ → ℝ) (x : CoordinateSpace) :
    metricComponents (originalRosenBilinear B ψ) x = originalRosenField B ψ x := by
  exact originalScreen_specialize B ψ x

/-- The actual Ricci tensor of the original Rosen metric, in coordinates and with
    both exponent signs retained. -/
theorem coordinateRicci_originalRosen (B ψ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hB : ContDiffOn ℝ 2 B U) (hψ : ContDiffOn ℝ 2 ψ U)
    (hnz : ∀ u ∈ U, B u ≠ 0) (x : CoordinateSpace) (hx : x 0 ∈ U) (b c : Index) :
    coordinateRicci (computedConnection (originalRosenBilinear B ψ)) x b c =
      if b = 0 ∧ c = 0 then -2 * (deriv (deriv B) (x 0) / B (x 0) + (deriv ψ (x 0))^2)
      else 0 := by
  let u := x 0
  let s := scaledScreen 1 B ψ
  let t := scaledScreen (-1) B ψ
  have hsScreen : s = fun v => screenX (B v) (ψ v) := by ext v; simp [s, scaledScreen, screenX]
  have htScreen : t = fun v => screenZ (B v) (ψ v) := by ext v; simp [t, scaledScreen, screenZ]
  have hboth (k : ℝ) : ContDiffOn ℝ 2 (scaledScreen k B ψ) U :=
    (hB.pow 2).mul ((contDiffOn_const.mul hψ).exp)
  have hbothNZ (k v : ℝ) (hv : v ∈ U) : scaledScreen k B ψ v ≠ 0 := by
    unfold scaledScreen
    exact mul_ne_zero (pow_ne_zero _ (hnz v hv)) (Real.exp_ne_zero _)
  unfold originalRosenBilinear
  rw [← hsScreen, ← htScreen, coordinateRicci_originalScreen s t U hU (hboth 1) (hboth (-1))
    (hbothNZ 1) (hbothNZ (-1)) x hx b c]
  split_ifs with h <;> try rfl
  let L := fun v => deriv B v / B v
  let D := fun v => deriv ψ v
  have hgs := scaledScreen_logDerivative_germ 1 B ψ U hU hB hψ hnz u hx
  have hgt := scaledScreen_logDerivative_germ (-1) B ψ U hU hB hψ hnz u hx
  have hcs : (fun v => (s v)⁻¹ * (deriv s v / 2)) =ᶠ[𝓝 u] (fun v => L v + D v) := by
    simpa [s, L, D] using hgs
  have hct : (fun v => (t v)⁻¹ * (deriv t v / 2)) =ᶠ[𝓝 u] (fun v => L v - D v) := by
    simpa [t, L, D, sub_eq_add_neg] using hgt
  have atS := hcs.eq_of_nhds
  have atT := hct.eq_of_nhds
  have huB := hB.contDiffAt (hU.mem_nhds hx)
  have huPsi := hψ.contDiffAt (hU.mem_nhds hx)
  have hB1 := huB.differentiableAt (by norm_num)
  have hB2 := local_CD2_deriv huB
  have hD := local_CD2_deriv huPsi
  have hu : B u ≠ 0 := hnz u hx
  have hL := hB2.hasDerivAt.div hB1.hasDerivAt hu
  have hAdd := (hL.add hD.hasDerivAt).deriv
  have hSub := (hL.sub hD.hasDerivAt).deriv
  change deriv (fun v => deriv B v / B v + deriv ψ v) u = _ at hAdd
  change deriv (fun v => deriv B v / B v - deriv ψ v) u = _ at hSub
  change -(deriv (fun v => (s v)⁻¹ * (deriv s v / 2)) u +
    deriv (fun v => (t v)⁻¹ * (deriv t v / 2)) u +
    ((s u)⁻¹ * (deriv s u / 2))^2 + ((t u)⁻¹ * (deriv t u / 2))^2) = _
  rw [hcs.deriv_eq, hct.deriv_eq, atS, atT]
  change -(deriv (fun v => L v + D v) u + deriv (fun v => L v - D v) u +
    (L u + D u)^2 + (L u - D u)^2) = _
  unfold L D
  rw [hAdd, hSub]
  dsimp only [u] at hu ⊢
  field_simp [hu]
  ring

theorem coordinateRicci_originalRosen_vacuum (B ψ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hB : ContDiffOn ℝ 2 B U) (hψ : ContDiffOn ℝ 2 ψ U) (hnz : ∀ u ∈ U, B u ≠ 0)
    (hODE : ∀ u ∈ U, deriv (deriv B) u = -((deriv ψ u)^2 * B u))
    (x : CoordinateSpace) (hx : x 0 ∈ U) (b c : Index) :
    coordinateRicci (computedConnection (originalRosenBilinear B ψ)) x b c = 0 := by
  rw [coordinateRicci_originalRosen B ψ U hU hB hψ hnz x hx b c]
  split_ifs with h
  · rw [hODE (x 0) hx]
    field_simp [hnz _ hx]
    ring
  · rfl

/-- The exact limit has Ricci tensor 2 du^2 in the same actual coordinate model. -/
theorem coordinateRicci_originalRosen_cos (U : Set ℝ) (hU : IsOpen U)
    (hnz : ∀ u ∈ U, Real.cos u ≠ 0) (x : CoordinateSpace) (hx : x 0 ∈ U) (b c : Index) :
    coordinateRicci (computedConnection (originalRosenBilinear Real.cos (fun _ => 0))) x b c =
      if b = 0 ∧ c = 0 then 2 else 0 := by
  rw [coordinateRicci_originalRosen Real.cos (fun _ => 0) U hU
    Real.contDiff_cos.contDiffOn contDiffOn_const hnz x hx b c]
  split_ifs with h
  · simp only [Real.deriv_cos', deriv.fun_neg, Real.deriv_sin, deriv_const, zero_pow (by decide : 2 ≠ 0),
      add_zero, neg_div, div_self (hnz _ hx), mul_neg, mul_one, neg_neg]
  · rfl

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Matrix Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators

def pulledScreenMetricJet (B' B'' V s' t' : ℝ) : FirstJet := fun d =>
  if d = 0 then
    !![-2 * B'' * V, -B', 0, 0;
       -B',          0, 0, 0;
       0,            0, s', 0;
       0,            0, 0, t']
  else if d = 1 then
    !![-2 * B', 0, 0, 0;
       0,       0, 0, 0;
       0,       0, 0, 0;
       0,       0, 0, 0]
  else 0

def explicitPulledScreenConnection (f q sx sz lx lz : ℝ) : Connection := fun a b c =>
  if a = 1 ∧ b = 0 ∧ c = 0 then f
  else if a = 1 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then q
  else explicitScreenConnection sx sz lx lz a b c

theorem christoffel_pulledScreenMetricJet (B B' B'' V s t s' t' : ℝ) :
    christoffel (inversePulledMetricAt B B' V s t) (pulledScreenMetricJet B' B'' V s' t') =
      explicitPulledScreenConnection (B⁻¹ * (B'' * V)) (B⁻¹ * B')
        (B⁻¹ * (s' / 2)) (B⁻¹ * (t' / 2)) (s⁻¹ * (s' / 2)) (t⁻¹ * (t' / 2)) := by
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [christoffel, koszul, pulledScreenMetricJet, inversePulledMetricAt,
      explicitPulledScreenConnection, explicitScreenConnection, Fin.sum_univ_succ]
  all_goals first | exact Or.inr trivial | (ring <;> simp)

theorem ricci_explicitPulledScreen (f q sx sz lx lz fu fv qu sxu szu lxu lzu : ℝ) (b c : Index) :
    ricci (explicitPulledScreenConnection f q sx sz lx lz)
      (fun d a j k =>
        if d = 0 then explicitPulledScreenConnection fu qu sxu szu lxu lzu a j k
        else if d = 1 then explicitPulledScreenConnection fv 0 0 0 0 0 a j k
        else 0) b c =
      if b = 0 ∧ c = 0 then fv - qu - q^2 - (lxu + lzu + lx^2 + lz^2) else 0 := by
  fin_cases b <;> fin_cases c <;>
    simp [ricci, explicitPulledScreenConnection, explicitScreenConnection, Fin.sum_univ_succ]
  all_goals ring

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField Burnett.Geometry.CurvatureDifference

private theorem fderiv_univariate_mul_secondary (f : ℝ → ℝ) (x : CoordinateSpace)
    (hf : DifferentiableAt ℝ f (x 0)) (d : Index) :
    fderiv ℝ (fun y : CoordinateSpace => f (y 0) * y 1) x (EuclideanSpace.single d 1) =
      if d = 0 then deriv f (x 0) * x 1 else if d = 1 then f (x 0) else 0 := by
  let u : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  let v : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hu := hf.hasDerivAt.hasFDerivAt.comp x u.hasFDerivAt
  have hv := v.hasFDerivAt (x := x)
  change fderiv ℝ (fun y => (f ∘ u) y * v y) x _ = _
  rw [(hu.fun_mul hv).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  change f (x 0) * (EuclideanSpace.single d (1 : ℝ)) 1 +
    x 1 * ((EuclideanSpace.single d (1 : ℝ)) 0 * deriv f (x 0)) = _
  fin_cases d <;> simp [EuclideanSpace.single_apply, mul_comm]

theorem coordinateConnectionJet_explicitPulledScreen (f q sx sz lx lz : ℝ → ℝ)
    (x : CoordinateSpace) (hf : DifferentiableAt ℝ f (x 0)) (hq : DifferentiableAt ℝ q (x 0))
    (hsx : DifferentiableAt ℝ sx (x 0)) (hsz : DifferentiableAt ℝ sz (x 0))
    (hlx : DifferentiableAt ℝ lx (x 0)) (hlz : DifferentiableAt ℝ lz (x 0)) :
    coordinateConnectionJet (fun p => explicitPulledScreenConnection (f (p 0) * p 1) (q (p 0))
      (sx (p 0)) (sz (p 0)) (lx (p 0)) (lz (p 0))) x = fun d a b c =>
      if d = 0 then explicitPulledScreenConnection (deriv f (x 0) * x 1) (deriv q (x 0))
        (deriv sx (x 0)) (deriv sz (x 0)) (deriv lx (x 0)) (deriv lz (x 0)) a b c
      else if d = 1 then explicitPulledScreenConnection (f (x 0)) 0 0 0 0 0 a b c else 0 := by
  funext d a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [coordinateConnectionJet, explicitPulledScreenConnection, explicitScreenConnection,
      fderiv_univariate_mul_secondary f x hf d, fderiv_univariate_at_basis q x hq d,
      fderiv_univariate_at_basis sx x hsx d, fderiv_univariate_at_basis sz x hsz d,
      fderiv_univariate_at_basis lx x hlx d, fderiv_univariate_at_basis lz x hlz d]

theorem deriv_rosen_inverse_mul_first (B : ℝ → ℝ) (u : ℝ) (hb : B u ≠ 0)
    (hB : DifferentiableAt ℝ B u) (hB' : DifferentiableAt ℝ (deriv B) u) :
    deriv (fun w => (B w)⁻¹ * deriv B w) u + ((B u)⁻¹ * deriv B u)^2 =
      (B u)⁻¹ * deriv (deriv B) u := by
  have hp := (hB.hasDerivAt.inv hb).mul hB'.hasDerivAt
  change deriv (B⁻¹ * deriv B) u + ((B u)⁻¹ * deriv B u)^2 = _
  rw [hp.deriv]
  change -deriv B u / (B u)^2 * deriv B u + (B u)⁻¹ * deriv (deriv B) u +
    ((B u)⁻¹ * deriv B u)^2 = _
  field_simp [hb]
  ring

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Matrix Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference

def pulledScreenBilinear (B s t : ℝ → ℝ) (x : CoordinateSpace) :
    LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis
    (pulledMetricAt (B (x 0)) (deriv B (x 0)) (x 1) (s (x 0)) (t (x 0)))

theorem pulledScreen_components (B s t : ℝ → ℝ) :
    metricComponents (pulledScreenBilinear B s t) =
      fun x => pulledMetricAt (B (x 0)) (deriv B (x 0)) (x 1) (s (x 0)) (t (x 0)) := by
  funext x
  calc
    metricComponents (pulledScreenBilinear B s t) x =
        BilinForm.toMatrix coordinateBasis (pulledScreenBilinear B s t x) := by
      ext a b
      simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, BilinForm.toMatrix_apply]
    _ = _ := BilinForm.toMatrix_toBilin coordinateBasis _

theorem pulledScreen_specialize (B ψ : ℝ → ℝ) (x : CoordinateSpace) :
    metricComponents (pulledScreenBilinear B
      (fun u => screenX (B u) (ψ u)) (fun u => screenZ (B u) (ψ u))) x =
      pulledRosenField B ψ x := by
  rw [pulledScreen_components]
  rfl

private theorem fderiv_pulled_entry_zero_zero (B : ℝ → ℝ) (x : CoordinateSpace)
    (hBdd : DifferentiableAt ℝ (deriv B) (x 0)) (d : Index) :
    fderiv ℝ (fun y : CoordinateSpace => -2 * deriv B (y 0) * y 1) x (EuclideanSpace.single d 1) =
      if d = 0 then -2 * deriv (deriv B) (x 0) * x 1
      else if d = 1 then -2 * deriv B (x 0) else 0 := by
  let u : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  let V : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hu := (hBdd.hasDerivAt.hasFDerivAt.comp x u.hasFDerivAt).const_mul (-2 : ℝ)
  have h := hu.fun_mul V.hasFDerivAt
  change fderiv ℝ (fun y : CoordinateSpace => -2 * (deriv B ∘ u) y * V y) x _ = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, Function.comp_apply]
  change -2 * deriv B (x 0) * (EuclideanSpace.single d (1 : ℝ)) 1 +
      x 1 * (-2 * ((EuclideanSpace.single d (1 : ℝ)) 0 * deriv (deriv B) (x 0))) = _
  fin_cases d <;> simp [EuclideanSpace.single_apply]
  ring

theorem pulledScreen_jet (B s t : ℝ → ℝ) (x : CoordinateSpace)
    (hBd : DifferentiableAt ℝ B (x 0)) (hBdd : DifferentiableAt ℝ (deriv B) (x 0))
    (hsd : DifferentiableAt ℝ s (x 0)) (htd : DifferentiableAt ℝ t (x 0)) :
    coordinateJet (metricComponents (pulledScreenBilinear B s t)) x =
      pulledScreenMetricJet (deriv B (x 0)) (deriv (deriv B) (x 0)) (x 1)
        (deriv s (x 0)) (deriv t (x 0)) := by
  rw [pulledScreen_components]
  funext d a b
  have hneg :
      fderiv ℝ (fun y : CoordinateSpace => -B (y 0)) x (EuclideanSpace.single d 1) =
        if d = 0 then -deriv B (x 0) else 0 := by
    simpa using fderiv_univariate_at_basis (fun u => -B u) x hBd.neg d
  have hs := fderiv_univariate_at_basis s x hsd d
  have ht := fderiv_univariate_at_basis t x htd d
  have huu := fderiv_pulled_entry_zero_zero B x hBdd d
  fin_cases a <;> fin_cases b <;>
    by_cases h0 : d = 0 <;> by_cases h1 : d = 1 <;>
    simp [coordinateJet, pulledScreenMetricJet, pulledMetricAt, h0, h1] <;>
    first | simpa [h0, h1] using huu | simpa [h0, h1] using hneg
          | simpa [h0, h1] using hs | simpa [h0, h1] using ht

def pulledScreenConnection (B s t : ℝ → ℝ) (x : CoordinateSpace) : Connection :=
  explicitPulledScreenConnection
    ((B (x 0))⁻¹ * (deriv (deriv B) (x 0) * x 1)) ((B (x 0))⁻¹ * deriv B (x 0))
    ((B (x 0))⁻¹ * (deriv s (x 0) / 2)) ((B (x 0))⁻¹ * (deriv t (x 0) / 2))
    ((s (x 0))⁻¹ * (deriv s (x 0) / 2)) ((t (x 0))⁻¹ * (deriv t (x 0) / 2))

theorem computedConnection_pulledScreen (B s t : ℝ → ℝ) (x : CoordinateSpace)
    (hBd : DifferentiableAt ℝ B (x 0)) (hBdd : DifferentiableAt ℝ (deriv B) (x 0))
    (hsd : DifferentiableAt ℝ s (x 0)) (htd : DifferentiableAt ℝ t (x 0))
    (hb : B (x 0) ≠ 0) (hs : s (x 0) ≠ 0) (ht : t (x 0) ≠ 0) :
    computedConnection (pulledScreenBilinear B s t) x = pulledScreenConnection B s t x := by
  unfold computedConnection pulledScreenConnection matrixInverse
  rw [pulledScreen_jet B s t x hBd hBdd hsd htd, pulledScreen_components,
    pulledMetricAt_inv _ _ _ _ _ hb hs ht, christoffel_pulledScreenMetricJet]

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open scoped Topology ContDiff

theorem coordinateRicci_pulledScreen_eq_originalScreen (B s t : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ 3 B U)
    (hs : ContDiffOn ℝ 2 s U) (ht : ContDiffOn ℝ 2 t U)
    (hb : ∀ u ∈ U, B u ≠ 0) (hsn : ∀ u ∈ U, s u ≠ 0) (htn : ∀ u ∈ U, t u ≠ 0)
    (x : CoordinateSpace) (hx : x 0 ∈ U) (i j : Index) :
    coordinateRicci (computedConnection (pulledScreenBilinear B s t)) x i j =
      coordinateRicci (computedConnection (originalScreenBilinear s t)) x i j := by
  let f := fun u => (B u)⁻¹ * deriv (deriv B) u
  let q := fun u => (B u)⁻¹ * deriv B u
  let sx := fun u => (B u)⁻¹ * (deriv s u / 2)
  let sz := fun u => (B u)⁻¹ * (deriv t u / 2)
  let lx := fun u => (s u)⁻¹ * (deriv s u / 2)
  let lz := fun u => (t u)⁻¹ * (deriv t u / 2)
  let F := computedConnection (pulledScreenBilinear B s t)
  let G := fun p : CoordinateSpace => explicitPulledScreenConnection (f (p 0) * p 1) (q (p 0))
    (sx (p 0)) (sz (p 0)) (lx (p 0)) (lz (p 0))
  have hB' : ContDiffOn ℝ 2 (deriv B) U := hB.deriv_of_isOpen hU (by norm_num)
  have hB'' : ContDiffOn ℝ 1 (deriv (deriv B)) U := hB'.deriv_of_isOpen hU (by norm_num)
  have hs' : ContDiffOn ℝ 1 (deriv s) U := hs.deriv_of_isOpen hU (by norm_num)
  have ht' : ContDiffOn ℝ 1 (deriv t) U := ht.deriv_of_isOpen hU (by norm_num)
  have heqPt (p : CoordinateSpace) (hp : p 0 ∈ U) : F p = G p := by
    have hpU := hU.mem_nhds hp
    unfold F
    rw [computedConnection_pulledScreen B s t p
      ((hB.contDiffAt hpU).differentiableAt (by norm_num))
      ((hB'.contDiffAt hpU).differentiableAt (by norm_num))
      ((hs.contDiffAt hpU).differentiableAt (by norm_num))
      ((ht.contDiffAt hpU).differentiableAt (by norm_num)) (hb _ hp) (hsn _ hp) (htn _ hp)]
    simp only [G, f, q, sx, sz, lx, lz, pulledScreenConnection, mul_assoc]
  have heq : F =ᶠ[𝓝 x] G := by
    let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
    have hnear : ∀ᶠ p in 𝓝 x, p 0 ∈ U := π.continuous.continuousAt (hU.mem_nhds hx)
    exact hnear.mono heqPt
  have hjet : coordinateConnectionJet F x = coordinateConnectionJet G x := by
    funext d a b c
    have hcomp : (fun p => F p a b c) =ᶠ[𝓝 x] (fun p => G p a b c) :=
      heq.mono fun _ h => congrFun (congrFun (congrFun h a) b) c
    unfold coordinateConnectionJet
    rw [hcomp.fderiv_eq]
  have hdB := (hB.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdB' := (hB'.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdB'' := (hB''.contDiffAt (hU.mem_nhds hx)).differentiableAt_one
  have hds := (hs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdt := (ht.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hds' := (hs'.contDiffAt (hU.mem_nhds hx)).differentiableAt_one
  have hdt' := (ht'.contDiffAt (hU.mem_nhds hx)).differentiableAt_one
  have hgjet := coordinateConnectionJet_explicitPulledScreen f q sx sz lx lz x
    ((hdB.inv (hb _ hx)).mul hdB'') ((hdB.inv (hb _ hx)).mul hdB')
    ((hdB.inv (hb _ hx)).mul (hds'.div_const 2)) ((hdB.inv (hb _ hx)).mul (hdt'.div_const 2))
    ((hds.inv (hsn _ hx)).mul (hds'.div_const 2)) ((hdt.inv (htn _ hx)).mul (hdt'.div_const 2))
  change coordinateRicci F x i j = _
  unfold coordinateRicci at ⊢
  rw [heqPt x hx, hjet]
  change ricci (explicitPulledScreenConnection (f (x 0) * x 1) (q (x 0))
    (sx (x 0)) (sz (x 0)) (lx (x 0)) (lz (x 0))) (coordinateConnectionJet G x) i j = _
  change ricci _ (coordinateConnectionJet G x) i j =
    coordinateRicci (computedConnection (originalScreenBilinear s t)) x i j
  rw [show coordinateConnectionJet G x = _ from hgjet, ricci_explicitPulledScreen,
      coordinateRicci_originalScreen s t U hU hs ht hsn htn x hx i j]
  have hzero : f (x 0) - deriv q (x 0) - (q (x 0))^2 = 0 := by
    have h := deriv_rosen_inverse_mul_first B (x 0) (hb _ hx) hdB hdB'
    change deriv q (x 0) + (q (x 0))^2 = f (x 0) at h
    linarith only [h]
  rw [hzero, zero_sub]

theorem coordinateRicci_pulledRosen_eq_originalRosen (B ψ : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ 3 B U) (hψ : ContDiffOn ℝ 2 ψ U)
    (hb : ∀ u ∈ U, B u ≠ 0) (x : CoordinateSpace) (hx : x 0 ∈ U) (i j : Index) :
    coordinateRicci (computedConnection (pulledScreenBilinear B
      (fun u => screenX (B u) (ψ u)) (fun u => screenZ (B u) (ψ u)))) x i j =
      coordinateRicci (computedConnection (originalRosenBilinear B ψ)) x i j := by
  have hB2 : ContDiffOn ℝ 2 B U := hB.of_le (by norm_num)
  have hs : ContDiffOn ℝ 2 (fun u => screenX (B u) (ψ u)) U :=
    (hB2.pow 2).mul ((contDiffOn_const.mul hψ).exp)
  have ht : ContDiffOn ℝ 2 (fun u => screenZ (B u) (ψ u)) U :=
    (hB2.pow 2).mul ((contDiffOn_const.mul hψ).exp)
  exact coordinateRicci_pulledScreen_eq_originalScreen B _ _ U hU hB hs ht
    hb (fun u hu => mul_ne_zero (pow_ne_zero _ (hb u hu)) (Real.exp_ne_zero _))
    (fun u hu => mul_ne_zero (pow_ne_zero _ (hb u hu)) (Real.exp_ne_zero _)) x hx i j

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open scoped ContDiff

theorem coordinateRicci_pulledRosen_cos (x : CoordinateSpace)
    (hx : x 0 ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) (i j : Index) :
    coordinateRicci (computedConnection (pulledScreenBilinear Real.cos
      (fun u => screenX (Real.cos u) 0) (fun u => screenZ (Real.cos u) 0))) x i j =
      if i = 0 ∧ j = 0 then 2 else 0 := by
  have hcos (u : ℝ) (hu : u ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) : Real.cos u ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo ?_).ne'
    exact ⟨by linarith [hu.1, Real.two_le_pi], by linarith [hu.2, Real.two_le_pi]⟩
  have hpull := coordinateRicci_pulledRosen_eq_originalRosen Real.cos (fun _ => 0) _ isOpen_Ioo
    Real.contDiff_cos.contDiffOn contDiffOn_const hcos x hx i j
  exact hpull.trans (coordinateRicci_originalRosen_cos _ isOpen_Ioo hcos x hx i j)

theorem exists_rosen_multiscale_vacuum_geometry :
    ∃ B : ℕ → ℝ → ℝ,
      (∀ n, B n 0 = 1) ∧ (∀ n, deriv (B n) 0 = 0) ∧
      (∀ n, ContDiffOn ℝ ∞ (B n) (Ioo (-(1 / 3) : ℝ) (1 / 3))) ∧
      (∀ n t, t ∈ Ioo (-(1 / 3) : ℝ) (1 / 3) →
        deriv (deriv (B n)) t =
          -((deriv (phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))) t)^2 * B n t)) ∧
      (∀ n u, u ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        0 < Real.cos (2 * u) ∧ Real.cos (2 * u) ≤ B n u ∧ B n u ≤ 1 ∧
        |deriv (B n) u| ≤ 1 ∧ |deriv (deriv (B n)) u| ≤ 4) ∧
      TendstoUniformlyOn B Real.cos atTop (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      TendstoUniformlyOn (fun n => deriv (B n)) (deriv Real.cos) atTop (Icc (-(1 / 4) : ℝ) (1 / 4)) ∧
      let ψ := fun n : ℕ => phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
      (∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        let J := coordinateJacobian (rosenCoordinates (B n)) point
        (J.transpose * originalRosenField (B n) (ψ n) (rosenCoordinates (B n) point) * J =
          pulledRosenField (B n) (ψ n) point) ∧ ∀ i, contractedSource (B n) (ψ n) point i = 0) ∧
      TendstoUniformlyOn
        (fun n (point : Fin 4 → ℝ) (i j : Fin 4) => originalRosenField (B n) (ψ n) point i j)
        (fun (point : Fin 4 → ℝ) (i j : Fin 4) => originalRosenField Real.cos (fun _ => 0) point i j)
        atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4)} ∧
      (∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) →
        ∀ i j k : Fin 4, ∃ d : ℝ,
          HasDerivAt (fun t => originalRosenField (B n) (ψ n) (Function.update point k t) i j)
            d (point k) ∧ |d| ≤ 6 * Real.exp 4) ∧
      (∀ R ≥ 0,
        TendstoUniformlyOn
          (fun n (point : Fin 4 → ℝ) (i j : Fin 4) => pulledRosenField (B n) (ψ n) point i j)
          (fun (point : Fin 4 → ℝ) (i j : Fin 4) => pulledRosenField Real.cos (fun _ => 0) point i j)
          atTop {point | point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) ∧ |point 1| ≤ R} ∧
        ∀ (n : ℕ) (point : Fin 4 → ℝ), point 0 ∈ Icc (-(1 / 4) : ℝ) (1 / 4) → |point 1| ≤ R →
          ∀ i j k : Fin 4, ∃ d : ℝ,
            HasDerivAt (fun t => pulledRosenField (B n) (ψ n) (Function.update point k t) i j)
              d (point k) ∧ |d| ≤ 8 * R + 2 + 6 * Real.exp 4) ∧
      (∀ (n : ℕ) (x : CoordinateSpace), x 0 ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) →
        ∀ i j : Index,
          coordinateRicci (computedConnection (originalRosenBilinear (B n) (ψ n))) x i j = 0 ∧
          coordinateRicci (computedConnection (pulledScreenBilinear (B n)
            (fun u => screenX (B n u) (ψ n u)) (fun u => screenZ (B n u) (ψ n u)))) x i j = 0) ∧
      ∀ (pulled : Bool) (left right : ℝ), left < 0 → 0 < right →
        Icc left right ⊆ Icc (-(1 / 4) : ℝ) (1 / 4) →
        let F := rosenMetricInCoordinates pulled
        let μ := volume.restrict (rosenScaleBox left right)
        ¬ ∃ δ : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
          0 < δ n ∧
          eLpNormEssSup (fun point =>
            max |F (B n) (ψ n) point 2 2 - F Real.cos (fun _ => 0) point 2 2|
                |F (B n) (ψ n) point 3 3 - F Real.cos (fun _ => 0) point 3 3|) μ ≤ ENNReal.ofReal (δ n) ∧
          eLpNormEssSup (fun point => deriv (deriv (fun t =>
            F (B n) (ψ n) (Function.update point 0 t) 2 2)) (point 0)) μ ≤ ENNReal.ofReal (C / δ n) := by
  obtain ⟨B, h0, h0', hs, ho, hb, hlim, hlim', hcoord, hc0, hc1, hpull⟩ :=
    exists_smooth_rosen_sequence_c1_zero_source_and_both_metrics
  refine ⟨B, h0, h0', hs, ho, hb, hlim, hlim', hcoord, hc0, hc1, hpull, ?_, ?_⟩
  · intro n x hx i j
    let ψ := phase ((n : ℝ) + 1) (Real.exp ((n : ℝ) + 1))
    have hψ : ContDiff ℝ 2 ψ := by
      unfold ψ phase scaledSine
      fun_prop
    have hquarter : Ioo (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 3) : ℝ) (1 / 3) := by
      intro u hu
      exact ⟨lt_trans (by norm_num) hu.1, lt_trans hu.2 (by norm_num)⟩
    have hBpos (u : ℝ) (hu : u ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) : B n u ≠ 0 := by
      obtain ⟨hcos, hB, _⟩ := hb n u ⟨hu.1.le, hu.2.le⟩
      exact (hcos.trans_le hB).ne'
    have hvac := coordinateRicci_originalRosen_vacuum (B n) ψ _ isOpen_Ioo
      (((contDiffOn_infty.mp (hs n)) 2).mono hquarter) hψ.contDiffOn hBpos
      (fun u hu => ho n u (hquarter hu)) x hx i j
    have heq := coordinateRicci_pulledRosen_eq_originalRosen (B n) ψ _ isOpen_Ioo
      (((contDiffOn_infty.mp (hs n)) 3).mono hquarter) hψ.contDiffOn hBpos x hx i j
    exact ⟨hvac, heq.trans hvac⟩
  · intro pulled left right hl hr hsub
    exact rosen_no_common_essential_metric_scale B (fun n => (contDiffOn_infty.mp (hs n)) 2)
      (fun n u hu => (hb n u hu).2) pulled left right hl hr hsub

end Burnett.RosenMultiscale
