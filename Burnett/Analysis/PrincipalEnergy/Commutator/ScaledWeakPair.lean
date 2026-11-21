import Burnett.Analysis.PrincipalEnergy.Commutator.CenteredWaveletPackets
import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledWeakTest

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ComplexConjugate

private theorem testPair_smul_left
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (c : ℂ) (f g : SchwartzMap Space ℂ) : R (c • f) g=c*R f g := by
  have hZero : R 0 g=0 := by simpa using hLin f f g 1
  calc
    _ = R (0-(-c) • f) g := by simp
    _ = _ := by rw [hLin,hZero]; ring

private theorem testPair_smul_real_right
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (hSkew : ∀ f g, R g f= -conj (R f g))
    (c : ℝ) (f g : SchwartzMap Space ℂ) : R f ((c:ℂ) • g)=(c:ℂ)*R f g := by
  calc
    _ = -conj (R ((c:ℂ) • g) f) := hSkew _ _
    _ = _ := by rw [testPair_smul_left R hLin,map_mul,Complex.conj_ofReal,← neg_mul,hSkew g f]; ring

/-- Rescale both actual tests in the normalized-ball weak bound. Their
amplitude parameters also bound the respective radius times derivative. -/
theorem weakPair_amplitude_bound
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (hSkew : ∀ f g, R g f= -conj (R f g)) {W : ℝ}
    (hWeak : ∀ (x : Space) (ρ : ℝ), 0<ρ → ∀ (f g : SchwartzMap Space ℂ),
      tsupport (f : Space → ℂ) ⊆ Metric.closedBall x ρ →
      tsupport (g : Space → ℂ) ⊆ Metric.closedBall x ρ →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∀ (j : Fin 4) z, ‖fderiv ℝ (⇑f) z (coordinateDirection j)‖≤ρ⁻¹) →
      (∀ (j : Fin 4) z, ‖fderiv ℝ (⇑g) z (coordinateDirection j)‖≤ρ⁻¹) →
      ‖R f g‖≤W*ρ^4)
    (x : Space) (ρ : ℝ) (hρ : 0<ρ) (f g : SchwartzMap Space ℂ)
    (hf : tsupport (f : Space → ℂ) ⊆ Metric.closedBall x ρ)
    (hg : tsupport (g : Space → ℂ) ⊆ Metric.closedBall x ρ)
    (A B : ℝ) (hA : 0<A) (hB : 0<B)
    (hfV : ∀ z, ‖f z‖≤A) (hgV : ∀ z, ‖g z‖≤B)
    (hfD : ∀ (j : Fin 4) z, ‖fderiv ℝ (⇑f) z (coordinateDirection j)‖≤ρ⁻¹*A)
    (hgD : ∀ (j : Fin 4) z, ‖fderiv ℝ (⇑g) z (coordinateDirection j)‖≤ρ⁻¹*B) :
    ‖R f g‖≤W*ρ^4*A*B := by
  let normal (u : SchwartzMap Space ℂ) (D : ℝ) := ((D⁻¹:ℝ):ℂ) • u
  have hSupport (u : SchwartzMap Space ℂ) (D : ℝ) :
      tsupport (normal u D : Space → ℂ) ⊆ tsupport (u : Space → ℂ) :=
    tsupport_smul_subset_right (fun _ : Space => ((D⁻¹:ℝ):ℂ)) (u : Space → ℂ)
  have hVal (u : SchwartzMap Space ℂ) (D : ℝ) (hD : 0<D) (hU : ∀ z, ‖u z‖≤D) (z : Space) :
      ‖normal u D z‖≤1 := by
    dsimp only [normal]
    rw [SchwartzMap.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hD.le)]
    exact (mul_le_mul_of_nonneg_left (hU z) (inv_nonneg.mpr hD.le)).trans_eq (inv_mul_cancel₀ hD.ne')
  have hDer (u : SchwartzMap Space ℂ) (D : ℝ) (hD : 0<D)
      (hU : ∀ (j : Fin 4) z, ‖fderiv ℝ (⇑u) z (coordinateDirection j)‖≤ρ⁻¹*D)
      (j : Fin 4) (z : Space) :
      ‖fderiv ℝ (normal u D : Space → ℂ) z (coordinateDirection j)‖≤ρ⁻¹ := by
    change ‖fderiv ℝ (((D⁻¹:ℝ):ℂ) • (u : Space → ℂ)) z (coordinateDirection j)‖≤ρ⁻¹
    rw [fderiv_const_smul u.differentiableAt,ContinuousLinearMap.smul_apply,norm_smul,
      Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hD.le)]
    exact (mul_le_mul_of_nonneg_left (hU j z) (inv_nonneg.mpr hD.le)).trans_eq (by
      rw [mul_comm ρ⁻¹ D,← mul_assoc,inv_mul_cancel₀ hD.ne',one_mul])
  have hNorm :
      ‖R (normal f A) (normal g B)‖=A⁻¹*B⁻¹*‖R f g‖ := by
    dsimp only [normal]
    rw [testPair_smul_left R hLin,testPair_smul_real_right R hLin hSkew,
      norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hA.le),Real.norm_of_nonneg (inv_nonneg.mpr hB.le),mul_assoc]
  calc
    _ = (A*B)*‖R (normal f A) (normal g B)‖ := by rw [hNorm]; field_simp [hA.ne',hB.ne']
    _ ≤ (A*B)*(W*ρ^4) := mul_le_mul_of_nonneg_left
      (hWeak x ρ hρ _ _ ((hSupport f A).trans hf) ((hSupport g B).trans hg)
        (hVal f A hA hfV) (hVal g B hB hgV) (hDer f A hA hfD) (hDer g B hB hgD)) (by positivity)
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
