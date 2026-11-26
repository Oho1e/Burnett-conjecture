import Burnett.Analysis.CubicEnergy.HighSlotCommutator.NarrowReferenceCoefficientBound
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.NarrowReferenceOrbitLimit

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Metric Finset Set
open scoped ENNReal NNReal ContDiff BigOperators

/-- The narrow reference estimate applies to the manuscript's actual
regularized low-Cartesian symbol in every selected ring where its fixed
infrared factor is one. The radian conversion and cutoff argument are exact. -/
theorem exists_narrowCartesian_highSlot_radian_sum_bound
    (a : E → ℂ) (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ^2, χ x = 0)
    (ha : ContDiff ℝ ∞ a)
    (hBand : ∀ q, a q≠0 → 1≤‖q‖ ∧ ‖q‖≤5/4)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (n : ℕ),
      (∀ j ∈ range n, ∀ p : Joint, a ((dyadicScale t j/tau) • p.2) ≠ 0 → η ‖p.2‖=1) →
      ∀ f g h : SchwartzMap E ℂ,
      ‖∑ j ∈ range n, radianHighCommutatorPair
        (fun p : Joint => a ((dyadicScale t j/tau) • p.2) * regularizedLowCartesianSymbol η χ b p)
        (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 := by
  let A := lowCartesianHighAnnularReference a χ b
  obtain ⟨hc,hA⟩ := lowCartesianHighAnnularReference_regular a χ b
    (by norm_num : (0:ℝ)<1) hρ hχ hcut ha hBand hV hContains hb
  have hA_support (p : Joint) (hp : A p ≠ 0) : 1≤‖p.2‖ ∧ ‖p.2‖≤5/4 ∧ ‖p.1‖≤(1/2)*‖p.2‖ := by
    obtain ⟨hl,hu,hp'⟩ := lowCartesianHighAnnularReference_support a χ b hρ hcut hBand p hp
    exact ⟨hl,hu,hp'.trans (mul_le_mul_of_nonneg_right hρ' (norm_nonneg _))⟩
  obtain ⟨M,hM,bound⟩ := exists_narrowReference_unfilteredCoefficient_bound A hc hA hA_support
  refine ⟨M,hM,?_⟩
  intro D L hD t ht n hIR f g h
  have eq (j : ℕ) (hj : j ∈ range n) :
      (fun p : Joint => a ((dyadicScale t j/tau) • p.2)*regularizedLowCartesianSymbol η χ b p) =
        radianHighReferenceBlock A (dyadicScale t j) :=
    (funext fun p => radianHighReferenceBlock_eq_regularizedLowCartesianSymbol a η χ b
      (show 0<dyadicScale t j by unfold dyadicScale; positivity) p (hIR j hj p)).symm
  have replace :
      (∑ j ∈ range n, radianHighCommutatorPair
        (fun p : Joint => a ((dyadicScale t j/tau) • p.2) * regularizedLowCartesianSymbol η χ b p)
        (fun x => (D x).re) f g h) =
        referenceUnfilteredCoefficientPairSum A D f g h t (range n) := by
    unfold referenceUnfilteredCoefficientPairSum
    exact sum_congr rfl fun j hj => by rw [eq j hj]
  rw [replace]
  exact bound D L hD ht n f g h

/-- A single high-frequency narrow orbit of the manuscript's Cartesian symbol,
with the untruncated operator-scale sum. The initial band is above the
threshold where the fixed infrared factor becomes one. -/
theorem exists_narrowCartesian_highOrbit_radian_bound_paper
    (inputL2 : Bool)
    (a : E → ℂ) (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ^2, χ x = 0)
    (ha : ContDiff ℝ ∞ a)
    (hBand : ∀ q, a q≠0 → 1≤‖q‖ ∧ ‖q‖≤5/4)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {s : ℝ}, 0<s → (∀ R≥tau/s, η R=1) → ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (fun p : Joint => ∑' k : ℕ,
        a ((dyadicCoefficientScale s k/tau) • p.2)*regularizedLowCartesianSymbol η χ b p)
        (fun x => (D x).re) f g h‖ₑ ≤ (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  let A := lowCartesianHighAnnularReference a χ b
  obtain ⟨hc,hA⟩ := lowCartesianHighAnnularReference_regular a χ b
    (by norm_num : (0:ℝ)<1) hρ hχ hcut ha hBand hV hContains hb
  have hA_support (p : Joint) (hp : A p ≠ 0) : 1≤‖p.2‖ ∧ ‖p.2‖≤5/4 ∧ ‖p.1‖≤(1/2)*‖p.2‖ := by
    obtain ⟨hl,hu,hp'⟩ := lowCartesianHighAnnularReference_support a χ b hρ hcut hBand p hp
    exact ⟨hl,hu,hp'.trans (mul_le_mul_of_nonneg_right hρ' (norm_nonneg _))⟩
  obtain ⟨M,hM,bound⟩ := exists_narrowReferenceOrbit_radian_commutator_bound_paper inputL2 A hc hA hA_support
  refine ⟨M,hM,?_⟩
  intro D L hD s hs hIR f g h
  have hτ : 0<tau := mul_pos (by norm_num) Real.pi_pos
  have bandEq (k : ℕ) (p : Joint) :
      a ((dyadicCoefficientScale s k/tau) • p.2)*regularizedLowCartesianSymbol η χ b p =
        radianHighReferenceBlock A (dyadicCoefficientScale s k) p := by
    let r := dyadicCoefficientScale s k
    have hr : 0<r := dyadicCoefficientScale_pos hs _
    refine (radianHighReferenceBlock_eq_regularizedLowCartesianSymbol a η χ b hr p ?_).symm
    intro hp
    have lo := (hBand _ hp).1
    rw [norm_smul,Real.norm_of_nonneg (div_nonneg hr.le hτ.le)] at lo
    have hupper : r≤s := div_le_self hs.le (one_le_pow₀ (by norm_num))
    have lower := lo.trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hupper hτ.le) (norm_nonneg _))
    apply hIR
    apply (div_le_iff₀ hs).mpr
    have lo' := (le_div_iff₀ hτ).mp (by simpa only [div_mul_eq_mul_div] using lower)
    simpa only [one_mul,mul_comm s ‖p.2‖] using lo'
  have eq : (fun p : Joint => ∑' k : ℕ,
      a ((dyadicCoefficientScale s k/tau) • p.2)*regularizedLowCartesianSymbol η χ b p) =
      narrowReferenceOrbitSymbol A s := by
    funext p
    unfold narrowReferenceOrbitSymbol
    exact tsum_congr fun k => bandEq k p
  rw [eq]
  exact bound D L hD hs f g h

theorem exists_narrowCartesian_highOrbit_radian_bound
    (a : E → ℂ) (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ^2, χ x = 0)
    (ha : ContDiff ℝ ∞ a)
    (hBand : ∀ q, a q≠0 → 1≤‖q‖ ∧ ‖q‖≤5/4)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {s : ℝ}, 0<s → (∀ R≥tau/s, η R=1) → ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (fun p : Joint => ∑' k : ℕ,
        a ((dyadicCoefficientScale s k/tau) • p.2)*regularizedLowCartesianSymbol η χ b p)
        (fun x => (D x).re) f g h‖ₑ ≤ (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_narrowCartesian_highOrbit_radian_bound_paper false a η χ b hρ hρ' hχ hcut ha hBand hV hContains hb

end Burnett.A06
