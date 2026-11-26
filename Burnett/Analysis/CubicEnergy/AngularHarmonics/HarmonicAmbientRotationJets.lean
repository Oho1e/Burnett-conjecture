import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicAngularJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.A06

open Metric
open scoped BigOperators ContDiff

private def angularRotationCLM (p : Fin 4 × Fin 4) : RotationSpace →L[ℝ] RotationSpace :=
  (EuclideanSpace.proj p.1).smulRight (EuclideanSpace.single p.2 1) -
    (EuclideanSpace.proj p.2).smulRight (EuclideanSpace.single p.1 1)

private theorem angularRotationCLM_apply (p : Fin 4 × Fin 4) (x : RotationSpace) :
    angularRotationCLM p x = planeRotationGenerator p.1 p.2 x :=
  (planeRotationGenerator_eq p.1 p.2 x).symm

private theorem exists_angularRotationCLM_jetBound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (p : Fin 4 × Fin 4) (n : ℕ), n ≤ 12 → ∀ x : RoundSphere3,
      ‖iteratedFDeriv ℝ n (angularRotationCLM p) x‖ ≤ B := by
  let I := (Fin 4 × Fin 4) × Fin 13
  have hf (a : I) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ sphere (0 : RotationSpace) 1,
      ‖iteratedFDeriv ℝ a.2.val (angularRotationCLM a.1) x‖ ≤ B := by
    have h : ContDiff ℝ a.2.val (angularRotationCLM a.1) := (angularRotationCLM a.1).contDiff
    obtain ⟨B,hB⟩ := (isCompact_sphere (0 : RotationSpace) 1).exists_bound_of_continuousOn
      (h.continuous_iteratedFDeriv le_rfl).continuousOn
    exact ⟨max 0 B,le_max_left _ _,fun x hx => (hB x hx).trans (le_max_right _ _)⟩
  choose B hB hjet using hf
  refine ⟨∑ a : I, B a,Finset.sum_nonneg (fun a _ => hB a),fun p n hn x => ?_⟩
  let a : I := (p,⟨n,by omega⟩)
  exact (hjet a x x.property).trans (Finset.single_le_sum (fun b _ => hB b) (Finset.mem_univ a))

private theorem norm_iteratedFDeriv_rotation_le {f : RotationSpace → ℝ}
    {n : ℕ} (hf : ContDiff ℝ (n+1 : ℕ) f) (p : Fin 4 × Fin 4)
    (x : RoundSphere3) {M B : ℝ} (hM : 0 ≤ M)
    (h : ∀ k : ℕ, k ≤ n+1 → ‖iteratedFDeriv ℝ k f x‖ ≤ M)
    (hG : ∀ k : ℕ, k ≤ n → ‖iteratedFDeriv ℝ k (angularRotationCLM p) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (planeRotationDerivative p.1 p.2 f) x‖ ≤ (2 : ℝ)^n * (M * B) := by
  have eq : planeRotationDerivative p.1 p.2 f =
      fun y => fderiv ℝ f y (angularRotationCLM p y) := by
    funext y
    rw [planeRotationDerivative, angularRotationCLM_apply]
  have hd : ContDiff ℝ n (fderiv ℝ f) :=
    hf.fderiv_right (by simp only [Nat.cast_succ,le_refl])
  rw [eq]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ *
        ‖iteratedFDeriv ℝ (n-k) (angularRotationCLM p) x‖ :=
      norm_iteratedFDeriv_clm_apply hd (angularRotationCLM p).contDiff x le_rfl
    _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * (M * B) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hdf : ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ ≤ M := by
        rw [norm_iteratedFDeriv_fderiv]
        exact h _ (by omega)
      have hG' := hG (n-k) (Nat.sub_le _ _)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hdf hG'
        (norm_nonneg _) hM) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]

/-- A single ambient derivative bound through order twelve controls the
actual sphere rotation words through the same order. -/
theorem exists_roundRotationJetBound_of_ambientJets :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : RotationSpace → ℝ},
      ContDiff ℝ 12 f → ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ 12 → ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ k f x‖ ≤ M) →
      roundRotationJetBound 12 f (A * M) := by
  obtain ⟨B,hB,hG⟩ := exists_angularRotationCLM_jetBound
  let A := 1 + (2 : ℝ)^12 * B
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have aux (n : ℕ) (hn : n ≤ 12) {f : RotationSpace → ℝ} (hf : ContDiff ℝ n f)
      {M : ℝ} (hM : 0 ≤ M)
      (h : ∀ k : ℕ, k ≤ n → ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ k f x‖ ≤ M) :
      roundRotationJetBound n f (A^n * M) := by
    induction n generalizing f M with
    | zero =>
      intro x
      simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using h 0 le_rfl x
    | succ n ih =>
      refine ⟨fun x => ?_, fun p _ => ?_⟩
      · have hx : ‖f x‖ ≤ M := by simpa only [norm_iteratedFDeriv_zero] using h 0 (Nat.zero_le _) x
        calc
          _ ≤ M := hx
          _ = 1*M := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_pow₀ hA) hM
      · have hF : ContDiff ℝ n (planeRotationDerivative p.1 p.2 f) :=
          contDiff_planeRotationDerivative (by simpa only [Nat.cast_succ] using hf) p.1 p.2
        have ht (k : ℕ) (hk : k ≤ n) (x : RoundSphere3) :
            ‖iteratedFDeriv ℝ k (planeRotationDerivative p.1 p.2 f) x‖ ≤ A*M := by
          have hFk : ContDiff ℝ (k+1 : ℕ) f := hf.of_le (by exact_mod_cast (show k+1 ≤ n+1 by omega))
          have hb := norm_iteratedFDeriv_rotation_le hFk p x hM
            (fun j hj => h j (by omega) x) (fun j hj => hG p j (by omega) x)
          calc
            _ ≤ _ := hb
            _ ≤ (2 : ℝ)^12 * (M*B) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
            _ = ((2 : ℝ)^12 * B)*M := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hM
        have hh := ih (by omega) hF (mul_nonneg hA₀ hM) ht
        simpa only [pow_succ, mul_assoc] using hh
  exact ⟨A^12, by positivity,fun hf _ hM h => aux 12 le_rfl hf hM h⟩

end Burnett.A06
