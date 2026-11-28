import Burnett.Geometry.FlatRigidity.WeakCurvature
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! One genuine compact plateau extends a family of local real smooth
coefficients to Schwartz inputs without changing their germs nearby. -/

set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Set Filter Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.FlatRigidity (exists_smooth_cutoff_on_compact_chart)
open scoped ContDiff Topology

local notation "E₀" => CoordinateSpace

theorem exists_schwartzCoefficients_complex_near {κ : Type*} (r : κ → E₀ → ℝ)
    {K U : Set E₀} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hr : ∀ j, ContDiffOn ℝ ∞ (r j) U) :
    ∃ V : Set E₀, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∃ c : κ → SchwartzMap E₀ ℂ, ∀ j x, x ∈ V →
        (fun y : E₀ => c j y) =ᶠ[𝓝 x] (fun y => (r j y : ℂ)) := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨_,_,_,hMU,χ,hχ,hχsupp,hχloc,_,h1⟩ := exists_smooth_cutoff_on_compact_chart hL hU hLU
  let f (j : κ) (x : E₀) := (χ x : ℂ) * (r j x : ℂ)
  have hχU : tsupport χ ⊆ U := hχloc.trans hMU
  have hDiff (j : κ) : ContDiff ℝ ∞ (f j) := by
    refine contDiff_iff_contDiffAt.mpr (fun x => ?_)
    by_cases hx : x ∈ U
    · have hC := (hr j).contDiffAt (hU.mem_nhds hx)
      exact ((Complex.ofRealCLM.contDiff.comp hχ).contDiffAt).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hC)
    · have hOutside : x ∉ tsupport χ := fun hxχ => hx (hχU hxχ)
      have hf : f j =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hOutside] with y hy
        change (χ y : ℂ) * (r j y : ℂ) = 0
        rw [show χ y = 0 from image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hf
  have hc (j : κ) : HasCompactSupport (f j) := by
    apply hχsupp.of_isClosed_subset (isClosed_tsupport (f j))
    apply closure_minimal _ (isClosed_tsupport χ)
    intro x hx
    by_contra hout
    apply hx
    change (χ x : ℂ) * (r j x : ℂ) = 0
    rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport hout, Complex.ofReal_zero, zero_mul]
  refine ⟨interior L,isOpen_interior,hKL,interior_subset.trans hLU,
    fun j => (hc j).toSchwartzMap (hDiff j), fun j x hx => ?_⟩
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  change (χ y : ℂ) * (r j y : ℂ) = _
  rw [h1 y (interior_subset hy), Complex.ofReal_one, one_mul]

end Burnett.V03.Palatini
