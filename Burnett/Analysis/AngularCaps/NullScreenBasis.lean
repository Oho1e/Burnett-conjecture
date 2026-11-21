import Burnett.Analysis.AngularCaps.UniformScreenPositivity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set
open scoped BigOperators
open Burnett.RicciSymbol

def pairingLinearMap (m : Form) (x : Vec) : Vec →ₗ[ℝ] ℝ where
  toFun := pairing m x
  map_add' := pairing_add_right m x
  map_smul' := fun a y => pairing_smul_right m a x y

def screenLinearConditions (m : Form) (w n : Vec) : Vec →ₗ[ℝ] ℝ × ℝ :=
  (pairingLinearMap m w).prod (pairingLinearMap m n)

def nullScreenSubmodule (m : Form) (w n : Vec) : Submodule ℝ Vec :=
  LinearMap.ker (screenLinearConditions m w n)

theorem mem_nullScreenSubmodule {m : Form} {w n z : Vec} :
    z ∈ nullScreenSubmodule m w n ↔ screenOrthogonal m w n z := by
  change (pairing m w z,pairing m n z) = (0,0) ↔ screenOrthogonal m w n z
  simp only [screenOrthogonal,Prod.mk.injEq]

theorem nullScreenSubmodule_finrank {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) :
    Module.finrank ℝ (nullScreenSubmodule m w n) = 2 := by
  let F := screenLinearConditions m w n
  have hW : pairing m w w = 0 := hw.2
  have hN : pairing m n n = 0 := hn.1
  have hNW : pairing m n w = -1/2 := (pairing_symm hSym n w).trans hn.2
  have hOnto : Function.Surjective F := by
    rintro ⟨a,b⟩
    refine ⟨(-2*b) • w + (-2*a) • n,?_⟩
    apply Prod.ext
    · change pairing m w ((-2*b) • w + (-2*a) • n) = a
      simp only [pairing_add_right,pairing_smul_right,hW,hn.2,mul_zero,zero_add]
      ring
    · change pairing m n ((-2*b) • w + (-2*a) • n) = b
      simp only [pairing_add_right,pairing_smul_right,hNW,hN,mul_zero,add_zero]
      ring
  have hDim := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hOnto,finrank_top,Module.finrank_prod,Module.finrank_self,
    finrank_euclideanSpace_fin] at hDim
  change 1+1+Module.finrank ℝ (nullScreenSubmodule m w n) = 4 at hDim
  omega

private theorem exists_positive_quadratic_normalization {m : Form} {z : Vec} (h : 0 < quadratic m z) :
    ∃ a : ℝ, 0 < a ∧ quadratic m (a • z) = 1 := by
  refine ⟨(Real.sqrt (quadratic m z))⁻¹,inv_pos.mpr (Real.sqrt_pos.2 h),?_⟩
  rw [quadratic_smul,inv_pow,Real.sq_sqrt h.le,inv_mul_cancel₀ h.ne']

structure NullScreenAxes (m : Form) (w n : Vec) where
  first : Vec
  second : Vec
  first_orthogonal : screenOrthogonal m w n first
  second_orthogonal : screenOrthogonal m w n second
  first_quadratic : quadratic m first = 1
  second_quadratic : quadratic m second = 1
  mixed_zero : pairing m first second = 0

/-- Choose an orthonormal pair for the positive Lorentz form on the
two-dimensional screen, while keeping the two prescribed null axes. -/
theorem exists_nullScreenAxes {m : Form} (f : TensorFrame.LorentzFrame m)
    {w n : Vec} (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) :
    Nonempty (NullScreenAxes m w n) := by
  let S := nullScreenSubmodule m w n
  let b := Module.finBasisOfFinrankEq ℝ S (nullScreenSubmodule_finrank (lorentzFrame_symm f) hw hn)
  have hx : (b 0 : Vec) ≠ 0 := by
    intro hz
    exact b.ne_zero 0 (Subtype.ext (by simpa using hz))
  have hxO : screenOrthogonal m w n (b 0 : Vec) :=
    mem_nullScreenSubmodule.mp (b 0).2
  obtain ⟨a,_,ha⟩ := exists_positive_quadratic_normalization (screen_quadratic_pos f hw hn hxO hx)
  let e : S := a • b 0
  have he : quadratic m (e : Vec) = 1 := ha
  let c := pairing m (e : Vec) (b 1 : Vec)
  let v : S := b 1-c • e
  have hv : (v : Vec) ≠ 0 := by
    intro heq
    have hVs : v = 0 := Subtype.ext (by simpa using heq)
    have heq' : b 1 = c • e := sub_eq_zero.mp hVs
    have hRepr := congrArg (fun u : S => b.repr u 1) heq'
    simp [e] at hRepr
  have hvOrth : screenOrthogonal m w n (v : Vec) := mem_nullScreenSubmodule.mp v.2
  obtain ⟨r,_,hr⟩ := exists_positive_quadratic_normalization (screen_quadratic_pos f hw hn hvOrth hv)
  let e₂ : S := r • v
  have hV : pairing m (e : Vec) (v : Vec) = 0 := by
    change pairing m (e : Vec) ((b 1 : Vec)-c • (e : Vec)) = 0
    rw [pairing_sub_right,pairing_smul_right,show pairing m (e : Vec) (e : Vec) = 1 from he,
      mul_one,sub_self]
  refine ⟨⟨(e : Vec),(e₂ : Vec),mem_nullScreenSubmodule.mp e.2,mem_nullScreenSubmodule.mp e₂.2,he,hr,?_⟩⟩
  change pairing m (e : Vec) (r • (v : Vec)) = 0
  rw [pairing_smul_right,hV,mul_zero]

theorem norm_le_of_screen_unit_quadratic {m : Form} {w n x : Vec} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hLower : ∀ x : Vec, ‖x‖ = 1 → screenOrthogonal m w n x → ℓ ≤ quadratic m x)
    (hScreen : screenOrthogonal m w n x) (hQ : quadratic m x = 1) :
    ‖x‖ ≤ 1+1/ℓ := by
  have hx : x ≠ 0 := by intro h; simp [h,quadratic,pairing] at hQ
  have hu : screenOrthogonal m w n (unitRep x) := by
    constructor
    · rw [unitRep,pairing_smul_right,hScreen.1,mul_zero]
    · rw [unitRep,pairing_smul_right,hScreen.2,mul_zero]
  have hb := hLower (unitRep x) (norm_unitRep x hx) hu
  rw [unitRep,quadratic_smul,hQ,mul_one,inv_pow] at hb
  have hMult := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
  rw [inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))] at hMult
  have hSq : ‖x‖^2 ≤ 1/ℓ := (le_div_iff₀ hℓ).mpr (by rwa [mul_comm])
  nlinarith only [hSq,sq_nonneg (‖x‖-1/2)]

end Burnett.Analysis.ProjectiveNullCaps
