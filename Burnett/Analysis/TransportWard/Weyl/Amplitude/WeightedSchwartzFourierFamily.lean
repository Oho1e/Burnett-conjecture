import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeFourierWeight

set_option autoImplicit false
set_option maxHeartbeats 5400000
noncomputable section

namespace Burnett.A03

open Bornology Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

section

variable {P V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem exists_weighted_schwartz_family_fourier_power
    (A : P → SchwartzMap E V) (g : P → ℝ) (gp : ∀ p, 0 < g p)
    (hA : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p, SchwartzMap.seminorm ℝ i j (A p) ≤ C*g p)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p η, ‖η‖^k * ‖𝓕 (A p : E → V) η‖ ≤ C*g p := by
  let N (p : P) : SchwartzMap E V := (g p)⁻¹ • A p
  let L : SchwartzMap E V →L[ℝ] SchwartzMap E V := SchwartzMap.fourierTransformCLM ℝ
  have nb : IsVonNBounded ℝ (range N) := by
    apply (schwartz_withSeminorms ℝ E V).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨i,j⟩
    obtain ⟨C,C0,hC⟩ := hA i j
    refine ⟨C+1,by positivity,?_⟩
    rintro _ ⟨p,rfl⟩
    have np : schwartzSeminormFamily ℝ E V (i,j) (N p) =
        (SchwartzMap.seminorm ℝ i j (A p)) / (g p) := by
      simp only [N,SchwartzMap.schwartzSeminormFamily_apply,map_smul_eq_mul,
        Real.norm_of_nonneg (inv_nonneg.mpr (gp p).le)]
      rw [div_eq_inv_mul]
    rw [np]
    exact ((div_le_iff₀ (gp p)).mpr (hC p)).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have lb := nb.image L
  obtain ⟨C,Cp,hC⟩ := (schwartz_withSeminorms ℝ E V).isVonNBounded_iff_seminorm_bounded.mp lb (k,0)
  refine ⟨C,Cp.le,?_⟩
  intro p η
  have m : L (N p) ∈ L '' (range N) := ⟨N p,mem_range_self p,rfl⟩
  have hn : SchwartzMap.seminorm ℝ k 0 (L (N p)) ≤ C := by
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using (hC _ m).le
  have b := (SchwartzMap.norm_pow_mul_le_seminorm ℝ (L (N p)) k η).trans hn
  have leval : L (N p) η = (g p)⁻¹ • 𝓕 (A p : E → V) η := by
    have eq : L (N p) = (g p)⁻¹ • L (A p) := L.map_smul _ _
    rw [eq,SchwartzMap.smul_apply]
    rfl
  rw [leval,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (gp p).le)] at b
  apply (div_le_iff₀ (gp p)).mp
  calc
    _ = ‖η‖^k * ((g p)⁻¹ * ‖𝓕 (A p : E → V) η‖) := by rw [div_eq_mul_inv]; ring
    _ ≤ C := b

/-- A family with uniform pre-Fourier Schwartz seminorms after positive
normalization has genuine uniform Fourier decay of every order. -/
theorem exists_weighted_schwartz_family_fourier_decay
    (A : P → SchwartzMap E V) (g : P → ℝ) (gp : ∀ p, 0 < g p)
    (hA : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p, SchwartzMap.seminorm ℝ i j (A p) ≤ C*g p)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p η,
      ‖𝓕 (A p : E → V) η‖ ≤ C*(1+‖η‖) ^ (-(N : ℝ))*g p := by
  obtain ⟨D,D0,hD⟩ := exists_weighted_schwartz_family_fourier_power A g gp hA 0
  obtain ⟨F,F0,hF⟩ := exists_weighted_schwartz_family_fourier_power A g gp hA N
  refine ⟨2^N * (D+F),by positivity,fun p η => ?_⟩
  have q := SchwartzMap.pow_mul_le_of_le_of_pow_mul_le (norm_nonneg η)
    (norm_nonneg (𝓕 (A p : E → V) η))
    (show ‖𝓕 (A p : E → V) η‖ ≤ D*g p by simpa only [pow_zero,one_mul] using hD p η)
    (show ‖η‖^(0+N) * ‖𝓕 (A p : E → V) η‖ ≤ F*g p by simpa only [zero_add] using hF p η)
  simp only [pow_zero,one_mul] at q
  exact q.trans_eq (by ring)

end

end Burnett.A03
