import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function
open scoped ContDiff

/-- For a jointly smooth function on a product, the actual iterated partial
Fréchet derivative in the first variable is jointly smooth. -/
theorem contDiff_firstPartialJet {X Y F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X × Y → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : X × Y => iteratedFDeriv ℝ n (fun x => f (x, p.2)) p.1) := by
  let L := ContinuousLinearMap.inl ℝ X Y
  let C := ContinuousMultilinearMap.compContinuousLinearMapL (G := F) (fun _ : Fin n => L)
  have eq : (fun p : X × Y => iteratedFDeriv ℝ n (fun x => f (x, p.2)) p.1) =
      fun p => C (iteratedFDeriv ℝ n f p) := by
    funext p
    let g (q : X × Y) := f (q + (0, p.2))
    have transl : ContDiff ℝ ∞ (fun q : X × Y => q + (0, p.2)) :=
      (contDiff_id : ContDiff ℝ ∞ (id : X × Y → X × Y)).add contDiff_const
    have hg : ContDiff ℝ ∞ g := hf.comp transl
    have hCompose : (fun x => f (x, p.2)) = g ∘ L := by
      funext x
      change f (x, p.2) = f ((x, 0) + (0, p.2))
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    rw [hCompose, L.iteratedFDeriv_comp_right hg p.1 (by exact_mod_cast le_top)]
    have shift : L p.1 + (0, p.2) = p := by
      apply Prod.ext
      · exact add_zero p.1
      · exact zero_add p.2
    change (iteratedFDeriv ℝ n (fun q => f (q + (0, p.2))) (L p.1)).compContinuousLinearMap
      (fun _ => L) = _
    rw [iteratedFDeriv_comp_add_right, shift]
    rfl
  rw [eq]
  have smoothJet : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := by
    rw [contDiff_iff_forall_nat_le]
    intro k _
    exact hf.iteratedFDeriv_right (i := n) (by exact_mod_cast (le_top : (k : ℕ∞) + n ≤ ⊤))
  exact C.contDiff.comp smoothJet

end Burnett.Analysis.CarlesonEmbedding
