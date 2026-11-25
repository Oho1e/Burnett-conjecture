import Burnett.Analysis.AllScaleTransfer.ActualEnlargedCapFiniteFactor
import Burnett.Analysis.AllScaleTransfer.ParabolicTrilinearEndpoint
import Burnett.Analysis.AllScaleTransfer.ActualCapDyadicRemainderTail

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section

namespace Burnett.A05

open Set MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ENNReal

local instance : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem triLpMass_toReal_L3 (f g w : SchwartzMap E ℂ) :
    (triLpMass f g w 3 3 3).toReal =
      ‖f.toLp 3 volume‖ * ‖g.toLp 3 volume‖ * ‖w.toLp 3 volume‖ := by
  simp only [triLpMass, ENNReal.toReal_mul, ENNReal.ofReal_ofNat, SchwartzMap.toLp, Lp.norm_toLp]

/-- The three factors use the same Jacobian, in the exact cubic mass
appearing in the radian estimates. -/
theorem triLpMass_pullbackTrilinearFactor_L3_cancel (A : E ≃L[ℝ] E) (f g w : SchwartzMap E ℂ) :
    (linearJacobian A)⁻¹ *
      (triLpMass (pullbackTrilinearFactor A f) (pullbackTrilinearFactor A g)
        (pullbackTrilinearFactor A w) 3 3 3).toReal = (triLpMass f g w 3 3 3).toReal := by
  rw [triLpMass_toReal_L3, triLpMass_toReal_L3]
  rw [← mul_assoc, ← mul_assoc]
  exact inverseDual_L3_product_cancel A (f.memLp 3 volume) (g.memLp 3 volume) (w.memLp 3 volume)

/-- All three nonzero Fourier factors lie in the same physical cap
support after restoring the same frequency coordinates. -/
theorem radianWeight_pullback_nonzero_cap_support
    (A : E ≃L[ℝ] E) (b : E → ℝ) (u : Fin 3 → SchwartzMap E ℂ)
    (hSupport : ∀ i, tsupport (radianFourier (u i : E → ℂ)) ⊆ tsupport b)
    (p : Joint) (hp : radianWeight (fun _ => 1) (pullbackTrilinearFactor A (u 0))
      (pullbackTrilinearFactor A (u 1)) (pullbackTrilinearFactor A (u 2)) p ≠ 0) :
    A p.1 ∈ tsupport b ∧ A p.2 ∈ tsupport b ∧ A (-(p.1+p.2)) ∈ tsupport b := by
  let F (i : Fin 3) := radianFourier (pullbackTrilinearFactor A (u i) : E → ℂ)
  have hF (i : Fin 3) {ξ : E} (hξ : F i ξ ≠ 0) : A ξ ∈ tsupport b :=
    tsupport_radianFourier_pullbackTrilinearFactor_subset A (u i) b (hSupport i)
      (subset_tsupport _ hξ)
  change ((1 : ℝ) : ℂ) * F 0 p.1 * F 1 p.2 * F 2 (-(p.1+p.2)) ≠ 0 at hp
  have h0 : F 0 p.1 ≠ 0 := fun e => hp (by rw [e, mul_zero, zero_mul, zero_mul])
  have h1 : F 1 p.2 ≠ 0 := fun e => hp (by rw [e, mul_zero, zero_mul])
  have h2 : F 2 (-(p.1+p.2)) ≠ 0 := fun e => hp (by rw [e, mul_zero])
  exact ⟨hF 0 h0, hF 1 h1, hF 2 h2⟩

/-- The actual three projected finite factors supply the support premise
for the transformed tail, with independent radial cutoffs in the slots. -/
theorem exists_actual_finite_cap_tail_factors
    (metric : Form) (δ : ℝ) {η : ℝ} (hη : 0 < η) (outer enlarged : ℝ)
    {w : Vec} (hw : w ≠ 0) (A : E ≃L[ℝ] E)
    (I : Fin 3 → Finset ℤ) (ε : Fin 3 → ℤ → ℂ) (f : Fin 3 → SchwartzMap E ℂ) :
    let b := enlargedCapMultiplier metric δ η outer enlarged w
    ∃ u : Fin 3 → SchwartzMap E ℂ,
      (∀ i x, u i x = radianAction b (finiteIntegerRadialTruncation (I i) (ε i) (f i)) x) ∧
      (∀ p : Joint, radianWeight (fun _ => 1) (pullbackTrilinearFactor A (u 0))
          (pullbackTrilinearFactor A (u 1)) (pullbackTrilinearFactor A (u 2)) p ≠ 0 →
        A p.1 ∈ tsupport b ∧ A p.2 ∈ tsupport b ∧ A (-(p.1+p.2)) ∈ tsupport b) := by
  intro b
  choose u hAction hFourier hSupport using fun i : Fin 3 =>
    exists_enlargedCap_finiteIntegerRadialTruncation_schwartz metric δ hη outer enlarged hw
      (I i) (ε i) (f i)
  exact ⟨u, hAction, radianWeight_pullback_nonzero_cap_support A b u (fun i => (hSupport i).trans inter_subset_left)⟩

/-- Each gap uses the same change of variables in its original physical
integral, with the gap cutoffs evaluated in the transformed coordinates. -/
theorem radianTrilinearForm_dyadicGap_pullback
    (A : E ≃L[ℝ] E) (m : Joint → ℂ) (s : ℕ) (f g w : SchwartzMap E ℂ) :
    radianTrilinearForm
        (radianLowGapSymbol (m ∘ pairedFrequencyEquiv A) s ∘ (pairedFrequencyEquiv A).symm) f g w =
      (linearJacobian A)⁻¹ • radianTrilinearForm (radianLowGapSymbol (m ∘ pairedFrequencyEquiv A) s)
        (pullbackTrilinearFactor A f) (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A w) := by
  let n := radianLowGapSymbol (m ∘ pairedFrequencyEquiv A) s
  have comp : (n ∘ (pairedFrequencyEquiv A).symm) ∘ pairedFrequencyEquiv A = n := by
    funext p
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  simpa only [comp] using radianTrilinearForm_pairedFrequency A (n ∘ (pairedFrequencyEquiv A).symm) f g w

end Burnett.A05
