import Burnett.Analysis.Microlocal.Overlap.UnweightedReceivingFirstOrder

/-! Recover the principal chart row from the actual action on a vanishing scalar times a jet. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 4700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff Topology

local notation "E" => CoordinateSpace

/-- The symbol of a coordinate row evaluated on a genuine cotangent
functional and an ordered component vector. -/
def rawFirstOrderPrincipalEvaluation {J : Type*} [Fintype J]
    (a : J → E → ℝ) (v : J → E) (i : J → JetSlot) (x : E) (ξ : E →L[ℝ] ℝ) (w : JetSlot → ℂ) : ℂ :=
  ∑ h, (a h x : ℂ) * (ξ (v h) : ℂ) * w (i h)

/-- At a zero of the scalar factor the differential row on its product
with a jet evaluates the principal symbol at the scalar's actual differential. -/
theorem receivingRawFirstOrderRow_mul_of_scalar_vanishes
    {J L : Type*} [Fintype J] [Fintype L]
    (a : J → E → ℝ) (v : J → E) (i : J → JetSlot) (b : L → E → ℝ) (j : L → JetSlot)
    (x : E) (f : E → ℝ) (ξ : E →L[ℝ] ℝ) (hf : HasFDerivAt f ξ x) (hZero : f x = 0)
    (u : JetSlot → E → ℂ) (hu : ∀ k, DifferentiableAt ℝ (u k) x) :
    receivingRawFirstOrderRow a v i b j (fun k y => (f y : ℂ) * u k y) x =
      rawFirstOrderPrincipalEvaluation a v i x ξ (fun k => u k x) := by
  have hCast : HasFDerivAt (fun y => (f y : ℂ)) (Complex.ofRealCLM.comp ξ) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hf
  have hApply (k : JetSlot) (e : E) : fderiv ℝ (fun y => (f y : ℂ) * u k y) x e = (ξ e : ℂ) * u k x := by
    change fderiv ℝ ((fun y => (f y : ℂ)) * u k) x e = _
    rw [(hCast.mul (hu k).hasFDerivAt).fderiv]
    simp [hZero, mul_comm]
  simp only [receivingRawFirstOrderRow, rawFirstOrderPrincipalEvaluation, hApply, hZero, Complex.ofReal_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, mul_assoc]

/-- One actual chart-action law implies the principal cotangent change.
The transformation is extracted by applying the law to a scalar affine
function vanishing at the point times a constant jet, so derivatives of
the fiber-coordinate matrices do not enter the symbol. -/
theorem rawFirstOrderPrincipal_change_of_actual_chart_action
    {RowsC RowsD Jc Jd Lc Ld : Type*}
    [Fintype Jc] [Fintype Jd] [Fintype Lc] [Fintype Ld]
    (ac : RowsC → Jc → E → ℝ) (vc : RowsC → Jc → E) (ic : RowsC → Jc → JetSlot)
    (bc : RowsC → Lc → E → ℝ) (jc : RowsC → Lc → JetSlot)
    (ad : RowsD → Jd → E → ℝ) (vd : RowsD → Jd → E) (id : RowsD → Jd → JetSlot)
    (bd : RowsD → Ld → E → ℝ) (jd : RowsD → Ld → JetSlot)
    (x : E) (φ : E → E) (Dφ : E →L[ℝ] E) (hφ : HasFDerivAt φ Dφ x)
    (inputChange : E → (JetSlot → ℂ) →ₗ[ℂ] (JetSlot → ℂ))
    (outputChange : (RowsD → ℂ) →ₗ[ℂ] (RowsC → ℂ))
    (hInput : ∀ w k, DifferentiableAt ℝ (fun y => inputChange y w k) x)
    (hActual : ∀ u : JetSlot → E → ℂ, (∀ k, ContDiff ℝ ∞ (u k)) →
      (fun s => receivingRawFirstOrderRow (ac s) (vc s) (ic s) (bc s) (jc s)
        (fun k y => inputChange y (fun l => u l (φ y)) k) x) =
      outputChange (fun s => receivingRawFirstOrderRow (ad s) (vd s) (id s) (bd s) (jd s) u (φ x)))
    (ξ : E →L[ℝ] ℝ) (w : JetSlot → ℂ) :
    (fun s => rawFirstOrderPrincipalEvaluation (ac s) (vc s) (ic s) x (ξ.comp Dφ) (inputChange x w)) =
      outputChange (fun s => rawFirstOrderPrincipalEvaluation (ad s) (vd s) (id s) (φ x) ξ w) := by
  let f (y : E) := ξ (y - φ x)
  let u (k : JetSlot) (y : E) := (f y : ℂ) * w k
  have hfSmooth : ContDiff ℝ ∞ f := ξ.contDiff.comp (contDiff_id.sub contDiff_const)
  have hu (k : JetSlot) : ContDiff ℝ ∞ (u k) :=
    (Complex.ofRealCLM.contDiff.comp hfSmooth).mul contDiff_const
  have hfZero : f (φ x) = 0 := by simp [f]
  have hf : HasFDerivAt f ξ (φ x) := by
    have h := ξ.hasFDerivAt.comp (φ x) ((hasFDerivAt_id (φ x)).sub_const (φ x))
    simpa only [ContinuousLinearMap.comp_id] using h
  have hInputProduct : (fun k y => inputChange y (fun l => u l (φ y)) k) =
      fun k y => (f (φ y) : ℂ) * inputChange y w k := by
    funext k y
    change inputChange y ((f (φ y) : ℂ) • w) k = _
    rw [map_smul]
    rfl
  have hC s := receivingRawFirstOrderRow_mul_of_scalar_vanishes
    (ac s) (vc s) (ic s) (bc s) (jc s) x (f ∘ φ) (ξ.comp Dφ) (hf.comp x hφ) hfZero
    (fun k y => inputChange y w k) (hInput w)
  have hD s := receivingRawFirstOrderRow_mul_of_scalar_vanishes
    (ad s) (vd s) (id s) (bd s) (jd s) (φ x) f ξ hf hfZero (fun k _ => w k) (fun _ => differentiableAt_const _)
  rw [← funext hC, ← funext hD]
  simpa only [hInputProduct, Function.comp_apply] using hActual u hu

end Burnett.Microlocal.Overlap
