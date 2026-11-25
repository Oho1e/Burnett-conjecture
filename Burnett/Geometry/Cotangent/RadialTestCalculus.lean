import Burnett.Geometry.Cotangent.HamiltonianCoordinates
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Coordinate expression of the actual degree-one extension. -/
def coordinateDegreeOne (r : Metric (M := M)) (c : M) (f : Phase → ℝ) (q : Phase) : ℝ :=
  coordinateNorm r c q * f (coordinateNormalize r c q)

theorem coordinateDegreeOne_cotangentChart (r : Metric (M := M)) (c : M)
    (f : CotangentBundle M → ℝ) {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    coordinateDegreeOne r c (f ∘ cotangentChartInverse c) (cotangentChart c p) =
      degreeOneRadialExtension r f p := by
  have hnp : cotangentNormalize r p ∈ cotangentSource c := hp
  rw [coordinateDegreeOne, coordinateNorm_cotangentChart r c hp,
    coordinateNormalize_cotangentChart r c hp, Function.comp_apply,
    cotangentChart_left_inv c hnp]
  rfl

theorem fderiv_coordinateDegreeOne_apply_hamiltonVector
    (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M) (f : Phase → ℝ)
    {q : Phase} (hq : q ∈ puncturedPhaseTarget c)
    (hf : DifferentiableAt ℝ f (coordinateNormalize r c q)) {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (coordinateDegreeOne r c f) (phaseScale t q)
      (hamiltonVector G (phaseScale t q)) =
      t^2 * (f (coordinateNormalize r c q) * radialCoefficient G r c q +
        coordinateNorm r c q * fderiv ℝ f (coordinateNormalize r c q) (angularVector G r c q)) := by
  have hqt := phaseScale_mem_puncturedPhaseTarget c hq ht.ne'
  have hN := (contDiffAt_coordinateNorm r c hqt).differentiableAt (by simp)
  have hA := (contDiffAt_coordinateNormalize r c hqt).differentiableAt (by simp)
  have hfAt : DifferentiableAt ℝ f (coordinateNormalize r c (phaseScale t q)) := by
    rwa [coordinateNormalize_scale r c q ht]
  have hFA := hfAt.hasFDerivAt.comp (phaseScale t q) hA.hasFDerivAt
  have hD := (hN.hasFDerivAt.mul hFA).fderiv
  change fderiv ℝ (coordinateDegreeOne r c f) (phaseScale t q) = _ at hD
  rw [hD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Function.comp_apply]
  change coordinateNorm r c (phaseScale t q) *
      fderiv ℝ f (coordinateNormalize r c (phaseScale t q)) (angularVector G r c (phaseScale t q)) +
    f (coordinateNormalize r c (phaseScale t q)) * radialCoefficient G r c (phaseScale t q) = _
  rw [coordinateNorm_scale r c q ht, coordinateNormalize_scale r c q ht,
    radialCoefficient_scale G r c hq ht, angularVector_scale G r c hq ht]
  simp only [map_smul, smul_eq_mul]
  ring

theorem fderiv_coordinateDegreeOne_apply_hamiltonVector_at_unit
    (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M) (f : Phase → ℝ)
    {q : Phase} (hq : q ∈ puncturedPhaseTarget c) (hu : coordinateNorm r c q = 1)
    (hf : DifferentiableAt ℝ f q) {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (coordinateDegreeOne r c f) (phaseScale t q)
      (hamiltonVector G (phaseScale t q)) =
      t^2 * (fderiv ℝ f q (angularVector G r c q) + radialCoefficient G r c q * f q) := by
  have hA := coordinateNormalize_of_norm_one r c hu
  have hfAt : DifferentiableAt ℝ f (coordinateNormalize r c q) := by rwa [hA]
  rw [fderiv_coordinateDegreeOne_apply_hamiltonVector G r c f hq hfAt ht, hA, hu, one_mul]
  ring

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def phaseRay (v : ℝ × Phase) : Phase := phaseScale v.1 v.2

theorem contDiff_phaseRay : ContDiff ℝ ∞ phaseRay := by
  exact (contDiff_fst.comp contDiff_snd).prodMk (contDiff_fst.smul (contDiff_snd.comp contDiff_snd))

theorem phaseRay_radialChart (r : Metric (M := M)) (c : M) {q : Phase}
    (hq : q ∈ puncturedPhaseTarget c) :
    phaseRay (coordinateNorm r c q, coordinateNormalize r c q) = q := by
  have h := (coordinateNorm_pos r c hq).ne'
  simp [phaseRay, coordinateNormalize, phaseScale_apply, smul_smul, mul_inv_cancel₀ h]

def coordinateSection (s : Phase → ℝ) (q : Phase) : Phase := phaseRay (s q, q)

private theorem hasFDerivAt_coordinateSection {s : Phase → ℝ} {q : Phase}
    (hs : DifferentiableAt ℝ s q) :
    HasFDerivAt (coordinateSection s)
      ((fderiv ℝ phaseRay (s q, q)).comp
        ((fderiv ℝ s q).prod (ContinuousLinearMap.id ℝ Phase))) q := by
  have hpair : HasFDerivAt (fun z : Phase => (s z, z))
      ((fderiv ℝ s q).prod (ContinuousLinearMap.id ℝ Phase)) q :=
    hs.hasFDerivAt.prodMk (hasFDerivAt_id (𝕜 := ℝ) q)
  have hRay : HasFDerivAt phaseRay (fderiv ℝ phaseRay (s q, q)) ((fun z : Phase => (s z, z)) q) :=
    (contDiff_phaseRay.differentiable (by simp) _).hasFDerivAt
  exact HasFDerivAt.comp (f := fun z : Phase => (s z, z)) q hRay hpair

/-- The graph differential of an invariant-scale section recovers the actual Hamilton direction. -/
theorem fderiv_coordinateSection_apply_angularVector
    (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M) (s : Phase → ℝ)
    {q : Phase} (hq : q ∈ puncturedPhaseTarget c) (hu : coordinateNorm r c q = 1)
    (hs : DifferentiableAt ℝ s q) (hsPos : 0 < s q)
    (hsInvariant : fderiv ℝ s q (angularVector G r c q) = radialCoefficient G r c q * s q) :
    s q • fderiv ℝ (coordinateSection s) q (angularVector G r c q) =
      hamiltonVector G (coordinateSection s q) := by
  let t := s q
  have ht : 0 < t := hsPos
  let X := angularVector G r c q
  let k := radialCoefficient G r c q
  let qt := phaseScale t q
  let Φ : Phase → ℝ × Phase := fun z => (coordinateNorm r c z, coordinateNormalize r c z)
  have hqt := phaseScale_mem_puncturedPhaseTarget c hq hsPos.ne'
  have hΦsmooth : ContDiffAt ℝ ∞ Φ qt :=
    (contDiffAt_coordinateNorm r c hqt).prodMk (contDiffAt_coordinateNormalize r c hqt)
  have hΦ : DifferentiableAt ℝ Φ qt := hΦsmooth.differentiableAt (by simp)
  have hΦvalue : Φ qt = (t, q) := by
    change (coordinateNorm r c (phaseScale t q), coordinateNormalize r c (phaseScale t q)) = _
    simp only [coordinateNorm_scale r c q ht, coordinateNormalize_scale r c q ht,
      hu, mul_one, coordinateNormalize_of_norm_one r c hu]
  have hRay := (contDiff_phaseRay.differentiable (by simp) (Φ qt)).hasFDerivAt
  have hc := (hRay.comp qt hΦ.hasFDerivAt).fderiv
  have hev : ∀ᶠ z in 𝓝 qt, z ∈ puncturedPhaseTarget c :=
    (isOpen_puncturedPhaseTarget c).mem_nhds hqt
  have hident : phaseRay ∘ Φ =ᶠ[𝓝 qt] id :=
    hev.mono fun _ hz => phaseRay_radialChart r c hz
  rw [hident.fderiv_eq, fderiv_id, hΦvalue] at hc
  have hvec := congrArg (fun D : Phase →L[ℝ] Phase => D (hamiltonVector G qt)) hc
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at hvec
  have hsplit : fderiv ℝ Φ qt (hamiltonVector G qt) = (t^2 * k, t • X) :=
    fderiv_radialChart_apply_hamiltonVector G r c hq hsPos
  rw [hsplit] at hvec
  have hS := (hasFDerivAt_coordinateSection hs).fderiv
  change t • fderiv ℝ (coordinateSection s) q X = hamiltonVector G qt
  rw [hS]
  change t • fderiv ℝ phaseRay (t, q) (fderiv ℝ s q X, X) = _
  rw [← map_smul, hvec]
  have hsI : fderiv ℝ s q X = k * t := hsInvariant
  rw [hsI]
  have hEq : t • (k * t, X) = (t^2 * k, t • X) := by
    apply Prod.ext
    · change t * (k * t) = t^2 * k
      ring
    · rfl
  rw [hEq]

/-- Actual derivative transport across the invariant-scale section, in its product chart. -/
theorem fderiv_apply_hamiltonVector_on_coordinateSection
    (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M)
    (s b : Phase → ℝ) {q : Phase} (hq : q ∈ puncturedPhaseTarget c)
    (hu : coordinateNorm r c q = 1) (hs : DifferentiableAt ℝ s q) (hsPos : 0 < s q)
    (hsInvariant : fderiv ℝ s q (angularVector G r c q) = radialCoefficient G r c q * s q)
    (hb : DifferentiableAt ℝ b (coordinateSection s q)) :
    fderiv ℝ b (coordinateSection s q) (hamiltonVector G (coordinateSection s q)) =
      s q * fderiv ℝ (b ∘ coordinateSection s) q (angularVector G r c q) := by
  let hS := fderiv_coordinateSection_apply_angularVector G r c s hq hu hs hsPos hsInvariant
  have hsd := (hasFDerivAt_coordinateSection hs).differentiableAt
  have hdiff := (hb.hasFDerivAt.comp q hsd.hasFDerivAt).fderiv
  rw [← hS, hdiff]
  simp only [ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]

/-- The two actual Hamilton derivatives give the exact squared section factor. -/
theorem coordinateDegreeOne_transport_weight
    (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M)
    (s b : Phase → ℝ) {q : Phase} (hq : q ∈ puncturedPhaseTarget c)
    (hu : coordinateNorm r c q = 1) (hs : DifferentiableAt ℝ s q) (hsPos : 0 < s q)
    (hsInvariant : fderiv ℝ s q (angularVector G r c q) = radialCoefficient G r c q * s q)
    (hb : DifferentiableAt ℝ b (coordinateSection s q)) :
    let f : Phase → ℝ := fun z => b (coordinateSection s z) / s z
    fderiv ℝ b (coordinateSection s q) (hamiltonVector G (coordinateSection s q)) =
      (s q)^2 * fderiv ℝ (coordinateDegreeOne r c f) q (hamiltonVector G q) := by
  dsimp only
  let B := b ∘ coordinateSection s
  let f := fun z => B z / s z
  let X := angularVector G r c q
  let k := radialCoefficient G r c q
  have hsd := (hasFDerivAt_coordinateSection hs).differentiableAt
  have hB : DifferentiableAt ℝ B q := hb.comp q hsd
  have hf : DifferentiableAt ℝ f q := by
    simpa only [f, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using hB.mul (hs.inv hsPos.ne')
  have hnear : ∀ᶠ z in 𝓝 q, s z ≠ 0 := hs.continuousAt.eventually_ne hsPos.ne'
  have he : (s * f) =ᶠ[𝓝 q] B := hnear.mono fun z hz => by
    change s z * (B z / s z) = B z
    field_simp
  have hd := (hs.hasFDerivAt.mul hf.hasFDerivAt).fderiv
  rw [he.fderiv_eq] at hd
  have hX := congrArg (fun D : Phase →L[ℝ] ℝ => D X) hd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hX
  change fderiv ℝ s q X = k * s q at hsInvariant
  rw [hsInvariant] at hX
  have ha := fderiv_coordinateDegreeOne_apply_hamiltonVector_at_unit G r c f hq hu hf (t := 1) one_pos
  have h1 : phaseScale 1 q = q := by simp [phaseScale_apply]
  rw [h1, one_pow, one_mul] at ha
  change fderiv ℝ b (coordinateSection s q) (hamiltonVector G (coordinateSection s q)) =
    (s q)^2 * fderiv ℝ (coordinateDegreeOne r c f) q (hamiltonVector G q)
  rw [fderiv_apply_hamiltonVector_on_coordinateSection G r c s b hq hu hs hsPos hsInvariant hb, ha]
  change s q * fderiv ℝ B q X = (s q)^2 * (fderiv ℝ f q X + k * f q)
  rw [hX]
  ring

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem coordinateDegreeOne_eq_homogeneous (r : Metric (M := M)) (c : M) (E : Phase → ℝ)
    (hE : ∀ q ∈ puncturedPhaseTarget c, ∀ t > (0 : ℝ), E (phaseScale t q) = t * E q)
    {q : Phase} (hq : q ∈ puncturedPhaseTarget c) :
    coordinateDegreeOne r c E q = E q := by
  have hN := coordinateNorm_pos r c hq
  rw [coordinateDegreeOne, coordinateNormalize, hE q hq _ (inv_pos.mpr hN)]
  rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]

/-- A true degree-one first integral gives the differentiated invariant-scale equation. -/
theorem inverse_energy_derivative_eq_radialCoefficient_mul
    (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M) (E : Phase → ℝ)
    (hEh : ∀ q ∈ puncturedPhaseTarget c, ∀ t > (0 : ℝ), E (phaseScale t q) = t * E q)
    {q : Phase} (hq : q ∈ puncturedPhaseTarget c) (hu : coordinateNorm r c q = 1)
    (hE : DifferentiableAt ℝ E q) (hpos : 0 < E q)
    (hfirst : fderiv ℝ E q (hamiltonVector G q) = 0) :
    fderiv ℝ (fun z => (E z)⁻¹) q (angularVector G r c q) =
      radialCoefficient G r c q * (E q)⁻¹ := by
  let X := angularVector G r c q
  let k := radialCoefficient G r c q
  let s := fun z => (E z)⁻¹
  have hnear : ∀ᶠ z in 𝓝 q, z ∈ puncturedPhaseTarget c := (isOpen_puncturedPhaseTarget c).mem_nhds hq
  have heq : coordinateDegreeOne r c E =ᶠ[𝓝 q] E :=
    hnear.mono fun z hz => coordinateDegreeOne_eq_homogeneous r c E hEh hz
  have hA := fderiv_coordinateDegreeOne_apply_hamiltonVector_at_unit G r c E hq hu hE (t := 1) one_pos
  have h1 : phaseScale 1 q = q := by simp [phaseScale_apply]
  rw [h1, one_pow, one_mul, heq.fderiv_eq, hfirst] at hA
  change 0 = fderiv ℝ E q X + k * E q at hA
  have hEX : fderiv ℝ E q X = -(k * E q) := by linarith
  have hs : DifferentiableAt ℝ s q := hE.inv hpos.ne'
  have hEne : ∀ᶠ z in 𝓝 q, E z ≠ 0 := hE.continuousAt.eventually_ne hpos.ne'
  have he : (E * s) =ᶠ[𝓝 q] (fun _ => (1 : ℝ)) := hEne.mono fun z hz =>
    mul_inv_cancel₀ hz
  have hconst : fderiv ℝ (fun _ : Phase => (1 : ℝ)) q = 0 :=
    (hasFDerivAt_const (1 : ℝ) q).fderiv
  have hD := (hE.hasFDerivAt.mul hs.hasFDerivAt).fderiv
  rw [he.fderiv_eq, hconst] at hD
  have hX := congrArg (fun D : Phase →L[ℝ] ℝ => D X) hD
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hEX] at hX
  change fderiv ℝ s q X = k * (E q)⁻¹
  apply mul_left_cancel₀ hpos.ne'
  have hsValue : s q * E q = 1 := inv_mul_cancel₀ hpos.ne'
  have h₁ : s q * -(k * E q) = -k := by calc
    s q * -(k * E q) = -(k * (s q * E q)) := by ring
    _ = -k := by rw [hsValue, mul_one]
  rw [h₁] at hX
  calc
    E q * fderiv ℝ s q X = k := by linarith
    _ = E q * (k * (E q)⁻¹) := by rw [mul_comm k, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Matrix Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

/-- Every ambient directional derivative tangent to the nonzero null level depends only on its null trace. -/
theorem fderiv_eq_of_same_null_trace (G : CoordinateSpace → Tensor2)
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) U)
    (hSym : ∀ x ∈ U, IsSymmetricTensor (G x))
    {q : Phase} (hq : q.1 ∈ U) (hξ : q.2 ≠ 0)
    (hDet : Matrix.det (G q.1) ≠ 0) (hnull : coordinateP G q = 0)
    {V : Phase} (hV : fderiv ℝ (coordinateP G) q V = 0)
    {f b : Phase → ℝ} (hf : DifferentiableAt ℝ f q) (hb : DifferentiableAt ℝ b q)
    (htrace : ∀ z : Phase, z.1 ∈ U → z.2 ≠ 0 → coordinateP G z = 0 → f z = b z) :
    fderiv ℝ f q V = fderiv ℝ b q V := by
  obtain ⟨w, hw⟩ := exists_dualPair_pos (G q.1) hDet hξ
  let B := fun z : Phase => dualPair (G z.1) z.2 w
  let C := fun z : Phase => dualPair (G z.1) z.2 z.2
  let A := fun z : Phase => dualPair (G z.1) w w
  let Δ := fun z : Phase => (B z)^2 - A z * C z
  let W := U ×ˢ (univ : Set Covector)
  have hW : IsOpen W := hU.prod isOpen_univ
  have hqW : q ∈ W := ⟨hq, trivial⟩
  have hmap : MapsTo Prod.fst W U := fun _ hz => hz.1
  have hBW : ContDiffOn ℝ ∞ B W := contDiffOn_dualPair G hG hmap contDiffOn_snd contDiffOn_const
  have hCW : ContDiffOn ℝ ∞ C W := contDiffOn_dualPair G hG hmap contDiffOn_snd contDiffOn_snd
  have hAW : ContDiffOn ℝ ∞ A W := contDiffOn_dualPair G hG hmap contDiffOn_const contDiffOn_const
  have hB := hBW.contDiffAt (hW.mem_nhds hqW)
  have hC := hCW.contDiffAt (hW.mem_nhds hqW)
  have hA := hAW.contDiffAt (hW.mem_nhds hqW)
  have hD : ContDiffAt ℝ ∞ Δ q := (hB.pow 2).sub (hA.mul hC)
  have hCP : C = (2 : ℝ) • coordinateP G := by
    funext z
    change dualPair (G z.1) z.2 z.2 = 2 * (symbolNorm (G z.1) z.2 / 2)
    rw [dualPair_self]
    ring
  have hzero : C q = 0 := by
    rw [hCP]
    change 2 * coordinateP G q = 0
    rw [hnull, mul_zero]
  have hCZ : fderiv ℝ C q V = 0 := by
    rw [hCP, fderiv_const_smul_of_field]
    change 2 * fderiv ℝ (coordinateP G) q V = 0
    rw [hV, mul_zero]
  have hDpos : 0 < Δ q := by
    change 0 < (B q)^2 - A q * C q
    rw [hzero, mul_zero, sub_zero]
    exact pow_pos hw 2
  let den := fun z => B z + Real.sqrt (Δ z)
  have hden : ContDiffAt ℝ ∞ den q :=
    hB.add ((Real.contDiffAt_sqrt hDpos.ne').comp q hD)
  have hdenPos : 0 < den q := add_pos_of_pos_of_nonneg hw (Real.sqrt_nonneg _)
  let a := fun z => correction (B z) (C z) (A z)
  let ret := fun z : Phase => (z.1, z.2 + a z • w)
  have hAc : DifferentiableAt ℝ a q := by
    have hI : DifferentiableAt ℝ (den⁻¹) q := (hden.inv hdenPos.ne').differentiableAt (by simp)
    simpa only [a, correction, den, Δ, div_eq_mul_inv] using
      (hC.neg.differentiableAt (by simp)).mul hI
  have hAzero : a q = 0 := by
    change correction (B q) (C q) (A q) = 0
    rw [hzero, correction_zero]
  have hAd : fderiv ℝ a q V = 0 := by
    have hI : DifferentiableAt ℝ (den⁻¹) q := (hden.inv hdenPos.ne').differentiableAt (by simp)
    have hderiv := ((hC.differentiableAt (by simp)).hasFDerivAt.neg.mul hI.hasFDerivAt).fderiv
    have heq : a = ((-C) * den⁻¹) := by
      funext z
      change -C z / den z = -C z * (den z)⁻¹
      exact div_eq_mul_inv _ _
    rw [heq, hderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.neg_apply, hzero, hCZ,
      neg_zero, zero_mul, mul_zero, add_zero]
  have hretAt := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).prodMk
    ((ContinuousLinearMap.snd ℝ CoordinateSpace Covector).hasFDerivAt.add
      (hAc.hasFDerivAt.smul_const w))
  change HasFDerivAt ret _ q at hretAt
  have hretQ : ret q = q := by
    change (q.1, q.2 + a q • w) = q
    simp [hAzero]
  have hretV : fderiv ℝ ret q V = V := by
    rw [hretAt.fderiv]
    simp [hAd]
  have hretNe : ∀ᶠ z in 𝓝 q, (ret z).2 ≠ 0 := by
    apply (continuous_snd.continuousAt.comp hretAt.continuousAt).eventually_ne
    rwa [Function.comp_apply, hretQ]
  have hnearU : ∀ᶠ z : Phase in 𝓝 q, z ∈ W := hW.mem_nhds hqW
  have hnearB : ∀ᶠ z in 𝓝 q, 0 < B z := hB.continuousAt (Ioi_mem_nhds hw)
  have hnearD : ∀ᶠ z in 𝓝 q, 0 < Δ z := hD.continuousAt (Ioi_mem_nhds hDpos)
  have hsame : (f ∘ ret) =ᶠ[𝓝 q] (b ∘ ret) := by
    filter_upwards [hnearU, hnearB, hnearD, hretNe] with z hz hbz hdz hneq
    apply htrace (ret z) hz.1 hneq
    change symbolNorm (G z.1) (z.2 + a z • w) / 2 = 0
    rw [← dualPair_self, dualPair_add_smul_self _ (hSym z.1 hz.1)]
    have hr := correction_quadratic (B z) (C z) (A z) hbz hdz
    change C z + 2 * B z * a z + A z * (a z)^2 = 0 at hr
    change (C z + 2 * B z * a z + A z * (a z)^2) / 2 = 0
    rw [hr, zero_div]
  have hfr : DifferentiableAt ℝ f (ret q) := by rwa [hretQ]
  have hbr : DifferentiableAt ℝ b (ret q) := by rwa [hretQ]
  have hDcomp := hsame.fderiv_eq (𝕜 := ℝ)
  rw [(hfr.hasFDerivAt.comp q hretAt).fderiv, (hbr.hasFDerivAt.comp q hretAt).fderiv] at hDcomp
  have hDcompV := congrArg (fun D : Phase →L[ℝ] ℝ => D V) hDcomp
  simpa only [ContinuousLinearMap.comp_apply, hretQ, hretAt.fderiv.symm, hretV] using hDcompV

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Matrix Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.ManifoldMetricTransition (coordinateBilinear)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The canonical Hamilton derivative is determined by an actual test's trace on the nonzero null cone. -/
theorem fderiv_apply_actual_hamiltonVector_eq_of_same_null_trace
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (c : M) {q : Phase} (hq : q ∈ puncturedPhaseTarget c)
    (hnull : coordinateP (chartInverse g c) q = 0) (f b : CotangentBundle M → ℝ)
    (hf : DifferentiableAt ℝ (f ∘ cotangentChartInverse c) q)
    (hb : DifferentiableAt ℝ (b ∘ cotangentChartInverse c) q)
    (htrace : ∀ p ∈ cotangentSource c, p ∈ puncturedCotangent →
      dualEnergy g hgn p = 0 → f p = b p) :
    let H := hamiltonVector (chartInverse g c) q
    fderiv ℝ (f ∘ cotangentChartInverse c) q H =
      fderiv ℝ (b ∘ cotangentChartInverse c) q H := by
  let G := chartInverse g c
  let U := (chartAt CoordinateSpace c).target
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  have hdet : Matrix.det (G q.1) ≠ 0 :=
    UnitNullAngular.chartInverse_det_ne_zero g hgn c q.1 hq.1.1
  have hP : DifferentiableAt ℝ (coordinateP G) q :=
    (((contDiffOn_coordinateP_chartInverse g hg hgn c).contDiffAt
      ((isOpen_phaseTarget c).mem_nhds hq.1))).differentiableAt (by simp)
  apply fderiv_eq_of_same_null_trace G hU (UnitNullAngular.chartInverse_smooth g hg hgn c)
    (fun x _ => UnitNullAngular.chartInverse_symm g hgs c x) hq.1.1 hq.2 hdet hnull
    (fderiv_coordinateP_apply_hamiltonVector G hP) hf hb
  intro z hz hξ hzNull
  have hzT : z ∈ phaseTarget c := ⟨hz, trivial⟩
  have hsrc := cotangentChartInverse_mapsTo c hzT
  apply htrace (cotangentChartInverse c z) hsrc
    (cotangentChartInverse_mem_punctured (show z ∈ puncturedPhaseTarget c from ⟨hzT, hξ⟩))
  have hp := coordinateP_cotangentChart g hgn hgs c hsrc
  rw [cotangentChart_right_inv c hzT] at hp
  change coordinateP (chartInverse g c) z = _ at hzNull
  rw [hzNull] at hp
  linarith

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Angular extensions that agree on the genuine unit-null bundle give the same Hamilton test. -/
theorem fderiv_apply_actual_hamiltonVector_eq_of_same_unitNull_trace
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (r : Metric (M := M)) (c : M) {q : Phase} (hq : q ∈ puncturedPhaseTarget c)
    (hnull : coordinateP (chartInverse g c) q = 0) (f b : CotangentBundle M → ℝ)
    (hf : DifferentiableAt ℝ (degreeOneRadialExtension r f ∘ cotangentChartInverse c) q)
    (hb : DifferentiableAt ℝ (degreeOneRadialExtension r b ∘ cotangentChartInverse c) q)
    (htrace : ∀ p ∈ cotangentUnitNull r g hgn, f p = b p) :
    let H := hamiltonVector (chartInverse g c) q
    fderiv ℝ (degreeOneRadialExtension r f ∘ cotangentChartInverse c) q H =
      fderiv ℝ (degreeOneRadialExtension r b ∘ cotangentChartInverse c) q H := by
  apply fderiv_apply_actual_hamiltonVector_eq_of_same_null_trace g hg hgn hgs c hq hnull
    (degreeOneRadialExtension r f) (degreeOneRadialExtension r b) hf hb
  intro p _ hp hpNull
  unfold degreeOneRadialExtension
  rw [htrace (cotangentNormalize r p) (cotangentNormalize_mem_unitNull r g hgn hp hpNull)]

end Burnett.Geometry.RadialHamilton
