import Burnett.Analysis.AngularCaps.WedgeTriad
import Burnett.Analysis.AngularCaps.UniformLorentzAngle

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

/-- The exact signed phase of the fixed quadratic Fourier symbol. -/
def signedQuadraticPhase (m : Form) (p ξ : Vec) : ℝ :=
  quadratic m (ξ+p)-quadratic m ξ

theorem signedQuadraticPhase_eq {m : Form} (hm : Symmetric m) (p ξ : Vec) :
    signedQuadraticPhase m p ξ = 2*pairing m p ξ+quadratic m p := by
  rw [signedQuadraticPhase, quadratic_add hm, pairing_symm hm ξ p]
  ring

/-- Relative width of the actual thickened characteristic cone. -/
def InRelativeCone (m : Form) (ε : ℝ) (p : Vec) : Prop :=
  |quadratic m p| ≤ ε*‖p‖^2

private theorem abs_signedPhase_ge_pairing_sub {m : Form} (hm : Symmetric m) (p q : Vec) :
    2*|pairing m p q| ≤ |signedQuadraticPhase m p q|+|quadratic m p| := by
  have hI : signedQuadraticPhase m p q-quadratic m p = 2*pairing m p q := by
    rw [signedQuadraticPhase_eq hm,add_sub_cancel_right]
  have h : |signedQuadraticPhase m p q-quadratic m p| ≤
      |signedQuadraticPhase m p q|+|quadratic m p| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (signedQuadraticPhase m p q) (-quadratic m p)
  rwa [hI,abs_mul,abs_of_nonneg zero_le_two] at h

/-- On the closed support of the manuscript's actual low/far cutoff, a fixed cone width
`η = c κ δ²` gives the exact signed phase gap. The constants are chosen for
the family and cone prefactor before any form, scale, cutoff, or frequency. -/
theorem exists_uniform_lowFar_signedQuadraticPhase_gap {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ m ∈ K, ∀ κ : ℝ, 0 < κ → κ < 1/16 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ ϑ : ℝ → ℝ, (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1) →
      ∀ p q r : Vec, p ≠ 0 → q ≠ 0 → r ≠ 0 →
        InRelativeCone m (C*(c*κ*δ^2)) p →
        InRelativeCone m (C*(c*κ*δ^2)) q →
        InRelativeCone m (C*(c*κ*δ^2)) r →
        InLowFarTriadSupport ϑ κ δ p q r →
        b*δ^2*(‖p‖*‖q‖) ≤ |pairing m p q| ∧
        b*δ^2*(‖p‖*‖q‖) ≤ |signedQuadraticPhase m p q| := by
  obtain ⟨A,hA,hUniform⟩ := exists_uniform_projectiveWedgeSq_le_nearNullPairing hK hFrame
  let c₀ : ℝ := 1/(64*A*(1+C))
  let b : ℝ := 1/(32*A)
  have hOneC : 0 < 1+C := by linarith only [hC]
  have hc₀ : 0 < c₀ := one_div_pos.mpr (by positivity)
  have hb : 0 < b := one_div_pos.mpr (by positivity)
  refine ⟨c₀,b,hc₀,hb,?_⟩
  intro m hm κ hκ hκsmall δ hδ _ c hc hcUpper ϑ hCut hFlat p q r hp hq hr hP hQ _ hFar
  let ε := C*(c*κ*δ^2)
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hP' : |quadratic m p| ≤ ε*‖p‖^2 := hP
  have hQ' : |quadratic m q| ≤ ε*‖q‖^2 := hQ
  obtain ⟨hLow,hSeparated,_⟩ := lowFarTriadSupport_separated hCut hFlat hκ hκsmall hδ hp hq hr hFar
  have hCoefficient : C*c*κ ≤ 1/(64*A) := by
    calc
      _ ≤ C*c*1 := mul_le_mul_of_nonneg_left (by linarith only [hκsmall]) (mul_nonneg hC hc.le)
      _ ≤ (1+C)*c := by linarith only [hc]
      _ ≤ (1+C)*c₀ := mul_le_mul_of_nonneg_left hcUpper hOneC.le
      _ = _ := by dsimp only [c₀]; field_simp [hA.ne',hOneC.ne']
  have hNarrow : A*ε ≤ δ^2/64 := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCoefficient (sq_nonneg δ)) hA.le
    calc
      A*ε = A*(C*c*κ*δ^2) := by dsimp only [ε]; ring
      _ ≤ A*(1/(64*A)*δ^2) := h
      _ = _ := by field_simp [hA.ne']
  have hAngle := hSeparated.trans (hUniform m hm p q hp hq ε hP' hQ')
  have hAδ : A*(b*δ^2) = δ^2/32 := by dsimp only [b]; field_simp [hA.ne']
  have hMixed : b*δ^2 ≤ |pairing m p q|/(‖p‖*‖q‖) := by
    apply (mul_le_mul_iff_right₀ hA).mp
    rw [hAδ]
    linarith only [hAngle,hNarrow,sq_nonneg δ]
  have hProd : 0 < ‖p‖*‖q‖ := mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq)
  have hMixed' := (le_div_iff₀ hProd).mp hMixed
  have hAbsorbE : ε ≤ b*δ^2 := by
    apply (mul_le_mul_iff_right₀ hA).mp
    rw [hAδ]
    linarith only [hNarrow,sq_nonneg δ]
  have hLow' : ‖p‖ ≤ ‖q‖ := hLow.trans (by
    have h := mul_le_mul_of_nonneg_right (show 2*κ ≤ 1 by linarith only [hκsmall]) (norm_nonneg q)
    simpa only [one_mul] using h)
  have hL2 : ‖p‖^2 ≤ ‖p‖*‖q‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hLow' (norm_nonneg p)
  have hAbsorb : |quadratic m p| ≤ b*δ^2*(‖p‖*‖q‖) :=
    hP'.trans ((mul_le_mul_of_nonneg_left hL2 hε).trans
      (mul_le_mul_of_nonneg_right hAbsorbE hProd.le))
  have hPhase := abs_signedPhase_ge_pairing_sub ((hFrame m hm).elim lorentzFrame_symm) p q
  refine ⟨hMixed',?_⟩
  linarith only [hPhase,hAbsorb,hMixed']

end Burnett.Analysis.ProjectiveNullCaps
