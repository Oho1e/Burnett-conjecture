import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientWindowTelescoping
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotRadianBlock

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Filter Finset
open scoped ContDiff Topology BigOperators

def narrowReferenceOrbitPartial (A : Joint → ℂ) (s : ℝ) (N : ℕ) (p : Joint) : ℂ :=
  ∑ k ∈ range (N+1), radianHighReferenceBlock A (dyadicCoefficientScale s k) p

def narrowReferenceOrbitSymbol (A : Joint → ℂ) (s : ℝ) (p : Joint) : ℂ :=
  ∑' k : ℕ, radianHighReferenceBlock A (dyadicCoefficientScale s k) p

private theorem τ_pos : 0<tau := mul_pos (by norm_num) Real.pi_pos

theorem narrowReferenceOrbit_reindex (s : ℝ) {N j : ℕ} (hj : j≤N) :
    dyadicScale (dyadicCoefficientScale s N) j = dyadicCoefficientScale s (N-j) := by
  unfold dyadicScale dyadicCoefficientScale
  have n : (2:ℝ)^N = 2^(N-j)*2^j := by
    conv_lhs => rw [← Nat.sub_add_cancel hj,pow_add]
  rw [n]
  field_simp

private theorem orbitRadius_bounds {A : Joint → ℂ}
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4)
    {s : ℝ} (hs : 0<s) (p : Joint) (h : radianHighReferenceBlock A s p≠0) :
    1≤(s/tau)*‖p.2‖ ∧ (s/tau)*‖p.2‖≤5/4 := by
  have hNonzero : A ((s/tau) • p)≠0 := fun h0 => h (by simp only [radianHighReferenceBlock,h0,smul_zero])
  have H := hBand ((s/tau) • p) hNonzero
  simpa only [Prod.smul_snd,norm_smul,Real.norm_of_nonneg (div_nonneg hs.le τ_pos.le)] using H

private theorem narrowReferenceOrbit_nonzero_unique {A : Joint → ℂ}
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4)
    {s : ℝ} (hs : 0<s) (p : Joint) {i j : ℕ}
    (hi : radianHighReferenceBlock A (dyadicCoefficientScale s i) p≠0)
    (hj : radianHighReferenceBlock A (dyadicCoefficientScale s j) p≠0) : i=j := by
  have excl (k l : ℕ) (hk : k<l)
      (hₖ : radianHighReferenceBlock A (dyadicCoefficientScale s k) p≠0)
      (hₗ : radianHighReferenceBlock A (dyadicCoefficientScale s l) p≠0) : False := by
    have scₗ : dyadicCoefficientScale s l≤dyadicCoefficientScale s (k+1) := by
      unfold dyadicCoefficientScale
      exact div_le_div_of_nonneg_left hs.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hk))
    have scHalf : dyadicCoefficientScale s l ≤ (1/2)*dyadicCoefficientScale s k := by
      have he := dyadicCoefficientScale_succ s k
      linarith only [scₗ,he]
    have u := (orbitRadius_bounds hBand (dyadicCoefficientScale_pos hs _) p hₖ).2
    have v := (orbitRadius_bounds hBand (dyadicCoefficientScale_pos hs _) p hₗ).1
    have cmp := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right scHalf τ_pos.le) (norm_nonneg p.2)
    rw [mul_div_assoc,mul_assoc] at cmp
    linarith only [u,v,cmp]
  exact le_antisymm (le_of_not_gt (fun h => excl j i h hj hi)) (le_of_not_gt (fun h => excl i j h hi hj))

/-- A pointwise narrow orbit has at most one active summand at every
frequency. Its true radian symbols converge along the nested cutoffs. -/
theorem narrowReferenceOrbitPartial_tendsto (A : Joint → ℂ)
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4)
    {s : ℝ} (hs : 0<s) (p : Joint) :
    Tendsto (fun N => narrowReferenceOrbitPartial A s N p) atTop (𝓝 (narrowReferenceOrbitSymbol A s p)) := by
  classical
  let b k := radianHighReferenceBlock A (dyadicCoefficientScale s k) p
  change Tendsto (fun N => ∑ k ∈ range (N+1), b k) atTop (𝓝 (∑' k, b k))
  by_cases hex : ∃ i, b i≠0
  · obtain ⟨i,hi⟩ := hex
    have hz (j : ℕ) (hj : j≠i) : b j=0 := by
      by_contra hn
      exact hj (narrowReferenceOrbit_nonzero_unique hBand hs p hn hi)
    have eq : ∑' k, b k = b i := tsum_eq_single i hz
    rw [eq]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop i] with N hN
    exact (sum_eq_single i (fun k _ hki => hz k hki)
      (fun h => (h (mem_range.mpr (Nat.lt_succ_of_le hN))).elim)).symm
  · push_neg at hex
    simp only [hex,sum_const_zero,tsum_zero,tendsto_const_nhds]

/-- Every finite narrow reference symbol is uniformly bounded by the high
frequency modulus, with a constant depending only on the reference symbol. -/
theorem exists_narrowReferenceOrbitPartial_order_bound (A : Joint → ℂ)
    (hA : Continuous A) (ha : HasCompactSupport A)
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4) :
    ∃ M : ℝ, 0≤M ∧ ∀ {s : ℝ}, 0<s → ∀ N p, ‖narrowReferenceOrbitPartial A s N p‖≤M*‖p.2‖ := by
  obtain ⟨p₀,hB⟩ := hA.norm.exists_forall_ge_of_hasCompactSupport ha.norm
  let B := ‖A p₀‖
  have B0 : 0≤B := norm_nonneg _
  refine ⟨B/tau,div_nonneg B0 τ_pos.le,?_⟩
  intro s hs N p
  let b k := radianHighReferenceBlock A (dyadicCoefficientScale s k) p
  change ‖∑ k ∈ range (N+1), b k‖ ≤ _
  by_cases hex : ∃ i ∈ range (N+1), b i≠0
  · obtain ⟨i,hi,hin⟩ := hex
    have hk (j : ℕ) (hj : j≠i) : b j=0 := by
      by_contra hn
      exact hj (narrowReferenceOrbit_nonzero_unique hBand hs p hn hin)
    rw [sum_eq_single i (fun j _ hji => hk j hji) (fun h => (h hi).elim)]
    let r := dyadicCoefficientScale s i
    have hr : 0<r := dyadicCoefficientScale_pos hs _
    have lo := (orbitRadius_bounds hBand hr p hin).1
    change ‖r⁻¹ • A ((r/tau) • p)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    have hSize : r⁻¹ ≤ ‖p.2‖/tau := by
      apply (inv_le_iff_one_le_mul₀ hr).mpr
      simpa only [div_mul_eq_mul_div,mul_comm r ‖p.2‖] using
        (show 1 ≤ (r/tau)*‖p.2‖ from lo)
    exact (mul_le_mul (hSize) (hB _) (norm_nonneg _) (div_nonneg (norm_nonneg _) τ_pos.le)).trans_eq (by ring)
  · push_neg at hex
    rw [sum_eq_zero hex,norm_zero]
    positivity

end Burnett.A06
