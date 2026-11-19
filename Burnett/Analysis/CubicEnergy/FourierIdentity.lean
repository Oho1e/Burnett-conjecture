import Burnett.Analysis.CubicEnergy.FourierPairing

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Burnett.RicciSymbol
open scoped ContDiff BigOperators

/-- Test the exact frequency identity against three Fourier-transformed
Schwartz functions. All pieces are actual integrable Lebesgue pairings. -/
theorem fourier_trilinear_identity (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v w : SchwartzMap E ℂ) :
    Integrable (weightedFourier (fun p => b (p.1+p.2)-b p.2) f v w) ∧
    (∫ p, weightedFourier (fun p => b (p.1+p.2)-b p.2) f v w p) =
      (∑ j, ∫ p, weightedFourier (lowTerm b j) f v w p) +
      (∑ j, ∫ p, weightedFourier (productTerm b j) f v w p) -
       ∑ j, ∫ p, weightedFourier (inputTerm b j) f v w p := by
  have parts := pieces_integrable b hb hh
  let L := fun j => weightedFourier (lowTerm b j) f v w
  let P := fun j => weightedFourier (productTerm b j) f v w
  let I := fun j => weightedFourier (inputTerm b j) f v w
  have l (j : Index) : Integrable (L j) := (parts j f v w).1
  have p (j : Index) : Integrable (P j) := (parts j f v w).2.1
  have i (j : Index) : Integrable (I j) := (parts j f v w).2.2
  have hl := integrable_finset_sum Finset.univ (fun j _ => l j)
  have hp := integrable_finset_sum Finset.univ (fun j _ => p j)
  have hi := integrable_finset_sum Finset.univ (fun j _ => i j)
  have point : weightedFourier (fun q => b (q.1+q.2)-b q.2) f v w =
      fun x => (∑ j, L j x) + (∑ j, P j x) - ∑ j, I j x := by
    funext q
    unfold L P I lowTerm productTerm inputTerm weightedFourier
    dsimp only
    rw [(commutator_symbol_decomposition b hb hh).2 q.1 q.2]
    push_cast
    simp only [sub_mul,add_mul,Finset.sum_mul]
  rw [point]
  refine ⟨(hl.add hp).sub hi,?_⟩
  have hsum : Integrable (fun q : Joint => (∑ j, L j q) + ∑ j, P j q) := hl.add hp
  simp only
  rw [integral_sub hsum hi,integral_add hl hp,
    integral_finset_sum _ (fun j _ => l j),integral_finset_sum _ (fun j _ => p j),
    integral_finset_sum _ (fun j _ => i j)]

end Burnett.A02.FrequencySplit
