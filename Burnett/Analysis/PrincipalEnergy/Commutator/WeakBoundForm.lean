import Burnett.Analysis.PrincipalEnergy.Energy.LeibnizEnergyBound

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem comm_sub_scalar_identity (R B : Op H) (c : ℂ) :
    comm (R - c • (1 : Op H)) B = comm R B := by
  simp only [comm, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

/-- Centering a symmetric coefficient yields the weak pair bound on the
common test domain, including overlapping inputs. -/
theorem symmetric_commutator_weakPair_bound {ι : Type*} [Fintype ι] (D : ι → Op H)
    (R B : Op H) (c : ℂ) (hR : (R - c • (1 : Op H)).IsSymmetric) (hB : B.IsSymmetric)
    (K : ℝ) (hK : ∀ u, ‖B u‖ ≤ K * firstOrderEnergy D u)
    (u v : H) (ε : ℝ) (hε : 0 ≤ ε)
    (hu : ‖(R - c • (1 : Op H)) u‖ ≤ ε * ‖u‖)
    (hv : ‖(R - c • (1 : Op H)) v‖ ≤ ε * ‖v‖) :
    ‖⟪comm R B u, v⟫_ℂ‖ ≤ K * ε * (firstOrderEnergy D u * ‖v‖ + ‖u‖ * firstOrderEnergy D v) := by
  let R₀ := R - c • (1 : Op H)
  rw [← comm_sub_scalar_identity R B c]
  change ‖⟪comm R₀ B u, v⟫_ℂ‖ ≤ _
  rw [show ⟪comm R₀ B u, v⟫_ℂ = ⟪B u, R₀ v⟫_ℂ - ⟪R₀ u, B v⟫_ℂ from by
    simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, inner_sub_left]
    rw [hR (B u) v, hB (R₀ u) v]]
  have h₁ : ‖⟪B u, R₀ v⟫_ℂ‖ ≤ (K * firstOrderEnergy D u) * (ε * ‖v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (hK u) hv (norm_nonneg _) ((norm_nonneg _).trans (hK u)))
  have h₂ : ‖⟪R₀ u, B v⟫_ℂ‖ ≤ (ε * ‖u‖) * (K * firstOrderEnergy D v) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hu (hK v) (norm_nonneg _) (by positivity))
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end Burnett.Analysis.SymmetricEnergy
