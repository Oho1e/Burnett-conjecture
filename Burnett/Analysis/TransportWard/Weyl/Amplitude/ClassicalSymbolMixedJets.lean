import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalOrderZeroLeft

set_option autoImplicit false
set_option maxHeartbeats 4700000
noncomputable section

namespace Burnett.A03

open Filter Set
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff Topology

private theorem smooth_iterated_fderiv {P V : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P → V) (h : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ P V).symm.toContinuousLinearEquiv.contDiff.comp h
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => P) V).symm.toContinuousLinearEquiv.contDiff.comp
      (contDiff_infty_iff_fderiv.mp ih).2

/-- The frequency iterated derivative of a genuinely smooth two-variable
symbol is itself jointly smooth. The proof takes the derivative in the
actual right coordinate of the product. -/
theorem smooth_right_slice_iterated_fderiv {P Q V : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : P → Q → V) (h : ContDiff ℝ ∞ (Function.uncurry a)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : P × Q => iteratedFDeriv ℝ n (a p.1) p.2) := by
  let L := ContinuousLinearMap.inr ℝ P Q
  let T := ContinuousMultilinearMap.compContinuousLinearMapL
    (G := V) (fun _ : Fin n => L)
  have eq (p : P × Q) : iteratedFDeriv ℝ n (a p.1) p.2 =
      T (iteratedFDeriv ℝ n (Function.uncurry a) p) := by
    let shift (z : P × Q) := Function.uncurry a ((p.1,0)+z)
    have ds : ContDiff ℝ ∞ shift := h.comp (contDiff_const.add contDiff_id)
    have left : a p.1 = shift ∘ L := by
      funext ξ
      change a p.1 ξ = Function.uncurry a ((p.1,0) + L ξ)
      simp [L]
    rw [left,L.iteratedFDeriv_comp_right ds p.2
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
    change ContinuousMultilinearMap.compContinuousLinearMap
      (iteratedFDeriv ℝ n (fun z : P × Q => Function.uncurry a ((p.1,0)+z)) (L p.2))
      (fun _ : Fin n => L) = _
    rw [iteratedFDeriv_comp_add_left]
    have atPoint : (p.1,0) + L p.2 = p := by
      ext <;> simp [L]
    rw [atPoint]
    rfl
  rw [show (fun p : P × Q => iteratedFDeriv ℝ n (a p.1) p.2) =
    T ∘ iteratedFDeriv ℝ n (Function.uncurry a) from funext eq]
  exact T.contDiff.comp (smooth_iterated_fderiv (Function.uncurry a) h n)

/-- The actual mixed frequency and base derivatives of an everywhere
smooth symbol are jointly smooth in the chart. -/
theorem smooth_mixed_symbol_jet (a : E → E → ℂ)
    (h : ContDiff ℝ ∞ (Function.uncurry a)) (n m : ℕ) :
    ContDiff ℝ ∞ (fun p : E × E =>
      iteratedFDeriv ℝ m (fun x => iteratedFDeriv ℝ n (a x) p.2) p.1) := by
  let F (p : E × E) := iteratedFDeriv ℝ n (a p.1) p.2
  let σ (p : E × E) := (p.2,p.1)
  have sd : ContDiff ℝ ∞ σ := contDiff_snd.prodMk contDiff_fst
  have fd : ContDiff ℝ ∞ F := smooth_right_slice_iterated_fderiv a h n
  let J (ξ x : E) := F (x,ξ)
  have jd : ContDiff ℝ ∞ (Function.uncurry J) := fd.comp sd
  have Result := smooth_right_slice_iterated_fderiv J jd m
  change ContDiff ℝ ∞ ((fun p : E × E => iteratedFDeriv ℝ m (J p.1) p.2) ∘ σ)
  exact Result.comp sd

/-- The existing compact-base Fourier interface follows from ordinary
joint smoothness. -/
theorem compact_base_frequency_jets_of_joint_smooth (a : E → E → ℂ)
    (h : ContDiff ℝ ∞ (Function.uncurry a)) : CompactBaseFrequencyJets a univ := by
  refine ⟨fun x => (h.comp (contDiff_const.prodMk contDiff_id)).contDiffOn,?_ ,?_⟩
  · intro n ξ _
    exact (smooth_right_slice_iterated_fderiv a h n).comp (contDiff_id.prodMk contDiff_const)
  · intro n
    exact (smooth_right_slice_iterated_fderiv a h n).continuous.continuousOn

end Burnett.A03
