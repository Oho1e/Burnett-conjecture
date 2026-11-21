import Burnett.Analysis.PrincipalEnergy.Commutator.FarWaveletPair
import Burnett.Analysis.PrincipalEnergy.Commutator.InverseFifthTail

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate

/-- An integrable input majorant outside the doubled output ball controls
the actual pairing after mean-zero subtraction in the target variable. -/
theorem meanZero_separatedPair_tail_bound {K : Space → Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds K C)
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hPair : ∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
      ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
      R f g = ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
        ∂((volume : Measure Space).prod volume))
    (f g : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) (hg : (∫ z, g z)=0)
    (x : Space) (s : ℝ) (hs : 0<s) (hfS : ∀ z, f z≠0 → 2*s≤‖x-z‖)
    (hgS : ∀ w, g w≠0 → ‖x-w‖≤s)
    (B : Space → ℝ) (hB : Integrable B) (hMaj : ∀ z, ‖f z‖*inverseFifthTail (2*s) (x-z)≤B z) :
    ‖R f g‖≤C*s*(∫ w, ‖g w‖)*(∫ z, B z) := by
  have hGap (w z : Space) (hz : f z≠0) (hw : g w≠0) : s≤‖w-z‖ := by
    have hTri := norm_add_le (x-w) (w-z)
    rw [show x-w+(w-z)=x-z by abel] at hTri
    linarith [hfS z hz,hgS w hw]
  have hX (z : Space) (hz : f z≠0) : s≤‖x-z‖ := by linarith [hfS z hz]
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  let I (p : Space × Space) := conj (g p.1)*((K p.1 p.2-K x p.2)*f p.2)
  have hRep : Integrable I μ ∧ R f g=∫ p, I p ∂μ :=
    meanZero_separatedPair_eq_kernelDifference hK R hPair f g hf hg x s hs hGap hX
  let Q (p : Space × Space) := ‖g p.1‖*B p.2
  have hQ : Integrable Q μ := (g.integrable (μ := (volume : Measure Space))).norm.mul_prod hB
  have hA : Integrable (fun p => (C*s)*Q p) μ := hQ.const_mul _
  have hBnonneg (z : Space) : 0≤B z :=
    (mul_nonneg (norm_nonneg _) (inverseFifthTail_nonneg _ _)).trans (hMaj z)
  have hDom (p : Space × Space) : ‖I p‖≤(C*s)*Q p := by
    by_cases hf₀ : f p.2=0
    · simp only [I,hf₀,mul_zero,norm_zero]
      exact mul_nonneg (mul_nonneg hK.const_nonneg hs.le) (mul_nonneg (norm_nonneg _) (hBnonneg _))
    by_cases hg₀ : g p.1=0
    · simp [I,Q,hg₀]
    have hFar := hfS p.2 hf₀
    have hPos : 0<‖x-p.2‖ := (mul_pos (by norm_num) hs).trans_le hFar
    have hShift : ‖x-p.1‖≤‖x-p.2‖/2 := by linarith [hgS p.1 hg₀]
    have hDiff : ‖K p.1 p.2-K x p.2‖≤(C*s)*inverseFifthTail (2*s) (x-p.2) := by
      rw [norm_sub_rev,inverseFifthTail,if_pos hFar]
      exact (hK.target x p.1 p.2 (sub_ne_zero.mp (norm_pos_iff.mp hPos)) hShift).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hgS p.1 hg₀) hK.const_nonneg) (by positivity))
    calc
      _ = ‖K p.1 p.2-K x p.2‖*(‖f p.2‖*‖g p.1‖) := by
        dsimp only [I]
        rw [norm_mul,Complex.norm_conj,norm_mul]
        ring
      _ ≤ ((C*s)*inverseFifthTail (2*s) (x-p.2))*(‖f p.2‖*‖g p.1‖) :=
        mul_le_mul_of_nonneg_right hDiff (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (C*s)*(‖g p.1‖*(‖f p.2‖*inverseFifthTail (2*s) (x-p.2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMaj _) (norm_nonneg _))
        (mul_nonneg hK.const_nonneg hs.le)
  calc
    _ = ‖∫ p, I p ∂μ‖ := congrArg norm hRep.2
    _ ≤ ∫ p, ‖I p‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (C*s)*Q p ∂μ := integral_mono hRep.1.norm hA hDom
    _ = _ := by
      have hPQ : (∫ p, Q p ∂μ)=(∫ w, ‖g w‖)*(∫ z, B z) :=
        integral_prod_mul (fun w : Space => ‖g w‖) B
      rw [integral_const_mul,hPQ]
      ring

end Burnett.Analysis.CarlesonEmbedding
