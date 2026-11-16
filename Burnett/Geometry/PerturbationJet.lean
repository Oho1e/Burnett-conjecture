import Burnett.Geometry.ConnectionError

/-!
# The first-jet bound consumed by the connection error

The covariant perturbation jet is the actual first Frechet derivative
array plus its two computed background-connection terms. No second or
higher derivatives of the perturbing metrics are used.
-/

noncomputable section

namespace Burnett.Geometry.PerturbationJet

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.InversePerturbation
open scoped BigOperators Topology
open Filter

theorem abs_connection_contract_le (Γ : Connection) (h : Tensor2) (b c d : Index) :
    |∑ e, Γ e b c * h e d| ≤ 4 * ‖Γ‖ * ‖h‖ := by
  calc
    _ ≤ ∑ e, |Γ e b c * h e d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Index, ‖Γ‖ * ‖h‖ := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul (abs_firstJet_entry_le_norm Γ e b c) (abs_entry_le_norm h e d)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem abs_connection_contract_right_le (Γ : Connection) (h : Tensor2) (b c d : Index) :
    |∑ e, Γ e b d * h c e| ≤ 4 * ‖Γ‖ * ‖h‖ := by
  calc
    _ ≤ ∑ e, |Γ e b d * h c e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Index, ‖Γ‖ * ‖h‖ := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul (abs_firstJet_entry_le_norm Γ e b d) (abs_entry_le_norm h c e)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem norm_covariantJet_le (Γ : Connection) (h : Tensor2) (dh : FirstJet) :
    ‖covariantJet Γ h dh‖ ≤ ‖dh‖ + 8 * ‖Γ‖ * ‖h‖ := by
  apply norm_connection_le_of_entries _ (by positivity)
  intro b c d
  have h1 := abs_sub (dh b c d) (∑ e, Γ e b c * h e d)
  have h2 := abs_sub (dh b c d - ∑ e, Γ e b c * h e d) (∑ e, Γ e b d * h c e)
  have hj := abs_firstJet_entry_le_norm dh b c d
  have hc1 := abs_connection_contract_le Γ h b c d
  have hc2 := abs_connection_contract_right_le Γ h b c d
  unfold covariantJet
  linarith

def backgroundConnectionOn (K : Set CoordinateSpace)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) : CoordinateSpace → Connection := by
  classical
  exact fun x => if hx : x ∈ K then metricConnection g₀ x (hn₀ x hx) else 0

@[simp] theorem backgroundConnectionOn_of_mem (K : Set CoordinateSpace)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) {x : CoordinateSpace} (hx : x ∈ K) :
    backgroundConnectionOn K g₀ hn₀ x = metricConnection g₀ x (hn₀ x hx) := by
  classical
  exact dif_pos hx

/-- Compactness bounds the actual computed background connection, when
its continuity on K has been supplied from the background geometry. -/
theorem exists_pos_bound_backgroundConnection (K : Set CoordinateSpace)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hK : IsCompact K)
    (hc : ContinuousOn (backgroundConnectionOn K g₀ hn₀) K) :
    ∃ G : ℝ, 0 < G ∧ ∀ x (hx : x ∈ K), ‖metricConnection g₀ x (hn₀ x hx)‖ ≤ G := by
  obtain ⟨G, hG, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨G, hG, ?_⟩
  intro x hx
  simpa only [backgroundConnectionOn_of_mem _ _ _ hx] using hb _ ⟨x, hx, rfl⟩

/-- The actual degree-one coordinate derivative of h is the raw jet input.
Uniform convergence gives eventual norm(h)<=1; no covariant-jet bound is
assumed in this theorem. -/
theorem eventually_bound_perturbationCovariantJet
    (K : Set CoordinateSpace)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) {D G : ℝ} (hG : 0 ≤ G)
    (hΓ : ∀ x (hx : x ∈ K), ‖metricConnection g₀ x (hn₀ x hx)‖ ≤ G)
    (hraw : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x‖ ≤ D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    ∀ᶠ n in atTop, ∀ x (hx : x ∈ K),
      ‖perturbationCovariantJet g₀ (g n) x (hn₀ x hx)‖ ≤ D + 8 * G := by
  have hsmall := Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one
  filter_upwards [hraw, hsmall] with n hdn hsn
  intro x hx
  have hh : ‖metricComponents (g n) x - metricComponents g₀ x‖ ≤ 1 := by
    have hd := hsn x hx
    rw [dist_comm, dist_eq_norm] at hd
    exact hd.le
  have hbound := norm_covariantJet_le (metricConnection g₀ x (hn₀ x hx))
    (metricComponents (g n) x - metricComponents g₀ x)
    (coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x)
  change ‖perturbationCovariantJet g₀ (g n) x (hn₀ x hx)‖ ≤
    ‖coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x‖ +
      8 * ‖metricConnection g₀ x (hn₀ x hx)‖ * ‖metricComponents (g n) x - metricComponents g₀ x‖
    at hbound
  apply hbound.trans
  have hp : 8 * ‖metricConnection g₀ x (hn₀ x hx)‖ *
      ‖metricComponents (g n) x - metricComponents g₀ x‖ ≤ 8 * G := by
    have hm := mul_le_mul (hΓ x hx) hh (norm_nonneg _) hG
    nlinarith
  linarith [hdn x hx]

/-- The connection-error convergence now consumes the raw first-jet bound
and compact background connection continuity; it has no separate J-bound
premise. The inverse inputs are supplied by the separate inverse-field line. -/
theorem metricConnectionError_tendstoUniformlyOn_of_rawJet
    (K : Set CoordinateSpace) (hK : IsCompact K)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hd₀ : ∀ x ∈ K, DifferentiableComponentsAt (metricComponents g₀) x)
    (hd : ∀ n x, x ∈ K → DifferentiableComponentsAt (metricComponents (g n)) x)
    (hcΓ : ContinuousOn (backgroundConnectionOn K g₀ hn₀) K)
    {B D : ℝ} (hD : 0 ≤ D)
    (hbase : ∀ x (hx : x ∈ K), ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ B)
    (hsmall : ∀ᶠ n in atTop, ∀ x (hx : x ∈ K),
      16 * ‖metricComponents (g n) x - metricComponents g₀ x‖ *
        ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ 1/2)
    (hraw : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x‖ ≤ D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K := by
  obtain ⟨G, hG, hΓ⟩ := exists_pos_bound_backgroundConnection K g₀ hn₀ hK hcΓ
  apply metricConnectionError_tendstoUniformlyOn K g₀ g hn₀ hn hs₀ hs hd₀ hd
    (H := D + 8*G) (by positivity) hbase
  · exact eventually_bound_perturbationCovariantJet K g₀ g hn₀ hG.le hΓ hraw hconv
  · exact hsmall
  · exact hconv

end Burnett.Geometry.PerturbationJet
