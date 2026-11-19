import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormDecay

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Filter Metric Set
open scoped ContDiff Topology

/-- Uniform control of a homogeneous scalar jet on any fixed compact annulus
from the same derivative orders on the unit sphere (ambient Cartesian derivatives). -/
theorem symbol_sphere_jet_to_annulus {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (d N : ℕ) (r R : ℝ) (hr : 0<r) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : X → ℝ) (_hs : ContDiffOn ℝ ∞ f {x | x ≠ 0})
      (_hh : ∀ t : ℝ, 0<t → ∀ x, f (t • x) = t^d * f x) (D : ℝ), 0≤D →
      (∀ n : ℕ, n≤N → ∀ u ∈ sphere (0:X) 1, ‖iteratedFDeriv ℝ n f u‖ ≤ D) →
      ∀ i : ℕ, i≤N → ∀ x : X, r≤‖x‖ → ‖x‖≤R → ‖iteratedFDeriv ℝ i f x‖ ≤ C*D := by
  let b := max 1 r⁻¹
  have b1 : 1≤b := le_max_left _ _
  refine ⟨R^d*b^N,mul_nonneg (pow_nonneg hR _) (pow_nonneg (zero_le_one.trans b1) _),?_⟩
  intro f hs hh D hD unit i hi x small large
  let U : Set X := {x | x ≠ 0}
  have ho : IsOpen U := isClosed_singleton.isOpen_compl
  have hxp : 0 < ‖x‖ := lt_of_lt_of_le hr small
  let s := ‖x‖⁻¹
  have sp : 0<s := inv_pos.mpr hxp
  have hx : x≠0 := norm_pos_iff.mp hxp
  let T : X →L[ℝ] X := s • ContinuousLinearMap.id ℝ X
  have Tval (z : X) : T z = s • z := rfl
  have Tx : T x ∈ U := smul_ne_zero sp.ne' hx
  have pre := ho.preimage T.continuous
  have order_le : (i:WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have he := T.iteratedFDerivWithin_comp_right hs ho.uniqueDiffOn pre.uniqueDiffOn (x := x) Tx order_le
  rw [iteratedFDerivWithin_of_isOpen i pre (show x ∈ T ⁻¹' U from Tx),iteratedFDerivWithin_of_isOpen i ho Tx] at he
  have fn : f ∘ T = (s^d) • f := funext (hh _ sp)
  have sm : ContDiffAt ℝ i f x := (hs.contDiffAt (ho.mem_nhds hx)).of_le order_le
  rw [fn,iteratedFDeriv_const_smul_apply sm] at he
  have op : ‖T‖ ≤ s := T.opNorm_le_bound sp.le (fun z => by rw [Tval,norm_smul,Real.norm_of_nonneg sp.le])
  have on : T x ∈ sphere (0:X) 1 := by
    simpa only [mem_sphere,dist_zero_right,Tval,s] using (norm_smul_inv_norm (𝕜 := ℝ) hx)
  have lhs : s^d * ‖iteratedFDeriv ℝ i f x‖ ≤ D * s^i := calc
    _ = ‖(s^d) • iteratedFDeriv ℝ i f x‖ := by rw [norm_smul,Real.norm_of_nonneg (pow_nonneg sp.le _)]
    _ ≤ ‖iteratedFDeriv ℝ i f (T x)‖ * ‖T‖^i := by
      rw [he]
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (iteratedFDeriv ℝ i f (T x)).norm_compContinuousLinearMap_le (fun _ => T)
    _ ≤ _ := mul_le_mul (unit i hi _ on) (pow_le_pow_left₀ (norm_nonneg _) op _) (pow_nonneg (norm_nonneg _) _) hD
  have sb : s≤b := (inv_anti₀ hr small).trans (le_max_right _ _)
  have si : s^i≤b^N := (pow_le_pow_left₀ sp.le sb _).trans (pow_le_pow_right₀ b1 hi)
  calc
    _ = ‖x‖^d * (s^d * ‖iteratedFDeriv ℝ i f x‖) := by simp only [← mul_assoc,← mul_pow,s,mul_inv_cancel₀ hxp.ne',one_pow,one_mul]
    _ ≤ R^d * (D*b^N) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) large _) (lhs.trans (mul_le_mul_of_nonneg_left si hD))
      (mul_nonneg (pow_nonneg sp.le _) (norm_nonneg _)) (pow_nonneg hR _)
    _ = _ := by ring

end Burnett.A02.FrequencySplit
