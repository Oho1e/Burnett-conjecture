import Burnett.Analysis.FrozenTransport.UniformCubicCoefficientBox
import Burnett.Analysis.FrozenTransport.ActualThinCubicReplacement

set_option autoImplicit false
set_option maxRecDepth 5600
set_option maxHeartbeats 9500000
noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz)
open Burnett.C03 (ProjectedPatchLpBounds projectedGaugeComplement)
open scoped ComplexConjugate ContDiff ENNReal Topology

private theorem cubic_product_tail
    (error difference pair : ℕ → ℝ) (K R B : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hPair₀ : ∀ n, 0 ≤ pair n)
    (hA : ∀ n, error n ≤ K * difference n * (pair n)^2)
    (hD : ∀ ε > 0, ∀ᶠ n in atTop, difference n ≤ R + ε)
    (hP : ∀ ε > 0, ∀ᶠ n in atTop, pair n ≤ B + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, error n ≤ K * R * B^2 + ε := by
  intro ε hε
  let f (t : ℝ) := K * (R + t) * (B + t)^2
  have hCont : Continuous f := by fun_prop
  have hNear : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, f t < f 0 + ε :=
    (hCont.continuousWithinAt : ContinuousWithinAt f (Set.Ioi 0) 0).eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  have hPos : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hs, ht⟩ := (hNear.and hPos).exists
  filter_upwards [hD t ht, hP t ht] with n hd hp
  calc
    _ ≤ K * difference n * (pair n)^2 := hA n
    _ ≤ f t := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd hK) (pow_le_pow_left₀ (hPair₀ n) hp 2)
        (sq_nonneg _) (mul_nonneg hK (add_nonneg hR ht.le))
    _ ≤ _ := by simpa only [f, add_zero] using hs.le

/-- Whole-space cubic replacement with one constant for all admissible
coefficient matrices in the same box. The physical and gauge fields still
come from the single original input of each patch. -/
theorem exists_uniform_completeCubic_actualThinReplacement
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ), 0 ≤ B →
      ∀ (c : EnergyIndex OrderedPair → OrderedPair → ℝ)
        (q : Index → Index → OrderedPair → OrderedPair → OrderedPair → ℝ),
      (∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l) →
      (∀ k l, |c k l| ≤ B) → (∀ a d i j k, |q a d i j k| ≤ B) →
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (hz : ∀ n a b x, conj (z n a b x) = z n a b x)
        (P : Set E) (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ grad → 0 ≤ Ce → 0 ≤ ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
      let T := actualThinScreenMultiplier m wi wo hm hη i o
      let diff (n : ℕ) (a : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) a.1 a.2 -
          multiplierCoordinateDerivative T (z n) a.1 a.2
      let mass := ((volume : Measure E) P).toReal
      (∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * mass ^ (1 / 3 : ℝ) + ε) →
      let u (n : ℕ) := originalCubicPhysical (z n) (hz n)
      let v (n : ℕ) := originalCubicThinScreen m wi wo hm hη i o (z n) (hz n)
      let G (n : ℕ) := originalCubicGauge (z n) (hz n)
      ∀ ε > 0, ∀ᶠ n in atTop,
        |completeCubicEnergy c q (fixedInfraredSymbol cut add b) (u n + G n) -
          completeCubicEnergy c q (fixedInfraredSymbol cut add b) (v n + G n)| ≤
          (C * B * (D + 1) * Ce * (4 * (64 * grad) + Ce)^2) * ell ^ alpha * mass + ε := by
  obtain ⟨C, hC, hEnergy⟩ := fixed_infrared_complete_uniform_coefficient_box (J := OrderedPair) cut add hcut hadd
  refine ⟨C, hC, ?_⟩
  intro B hB c q hc hcBox hqBox b hb hom D hD jet m wi wo hm η hη i o z hz P value grad Ce ell alpha
    hg hCe hEll hEll1 hAlpha hValue hSource T diff mass hDiff u v G
  let u₀ (n : ℕ) (k : OrderedPair) := projectionFullSchwartz (z n) k.1 k.2
  let v₀ (n : ℕ) := actualThinSchwartzField m wi wo hm hη i o (z n)
  let G₀ (n : ℕ) (k : OrderedPair) := projectedGaugeComplement (z n) k.1 k.2
  let M := mass ^ (1 / 3 : ℝ)
  let K := C * B * (D + 1)
  let Cp := 4 * (64 * grad) + Ce
  have hGradDiff : ∀ ε > 0, ∀ᶠ n in atTop,
      euclideanFieldGradientL3 (u₀ n - v₀ n) ≤ Ce * ell ^ alpha * M + ε := by
    intro ε hε
    filter_upwards [hDiff ε hε] with n hn
    exact (actualThinSchwartz_cubicGradientDifference m wi wo hm hη i o (z n)).le.trans hn
  obtain ⟨hU, hV, hG, hGrad⟩ := actualLinearFields_C03_budget m wi wo hm hη i o z P value grad hValue hSource
  have hm₀ : 0 ≤ mass := ENNReal.toReal_nonneg
  have hM : 0 ≤ M := Real.rpow_nonneg hm₀ _
  have hEllA : ell ^ alpha ≤ 1 := Real.rpow_le_one hEll hEll1 hAlpha
  have hW := cubicPatch_W13_budgets u₀ v₀ G₀ (64 * grad) Ce (ell ^ alpha) M
    hCe hEllA hM hU hV hG hGrad hGradDiff
  let error (n : ℕ) := |completeCubicEnergy c q (fixedInfraredSymbol cut add b) (u n + G n) -
    completeCubicEnergy c q (fixedInfraredSymbol cut add b) (v n + G n)|
  let Wd (n : ℕ) := euclideanFieldW13 (↑(u n - v n) : OrderedPair → SchwartzMap E ℂ)
  let Wp (n : ℕ) := euclideanFieldW13 (↑(u n + G n) : OrderedPair → SchwartzMap E ℂ) +
    euclideanFieldW13 (↑(v n + G n) : OrderedPair → SchwartzMap E ℂ)
  have hA (n : ℕ) : error n ≤ K * Wd n * (Wp n)^2 := by
    have h := hEnergy B hB c q hc hcBox hqBox b hb hom D hD jet (u n + G n) (v n + G n)
    rw [add_sub_add_right_eq_sub] at h
    exact h
  have hPair₀ (n : ℕ) : 0 ≤ Wp n := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hBound := cubic_product_tail error Wd Wp K (Ce * ell ^ alpha * M) (Cp * M)
    (by dsimp [K]; positivity) (by positivity) hPair₀ hA
    (fun ε hε => (hW ε hε).mono fun _ h => h.1) (fun ε hε => (hW ε hε).mono fun _ h => h.2)
  have hMass : M * M^2 = mass := by
    dsimp [M]
    rw [pow_two, ← Real.rpow_add_of_nonneg hm₀ (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3), ← Real.rpow_add_of_nonneg hm₀
        (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3 + 1 / 3)]
    rw [show (1 / 3 : ℝ) + (1 / 3 + 1 / 3) = 1 by norm_num, Real.rpow_one]
  have hScale : K * (Ce * ell ^ alpha * M) * (Cp * M)^2 =
      (K * Ce * Cp^2) * ell ^ alpha * mass := by
    rw [← hMass]
    ring
  simpa only [hScale] using hBound

end Burnett.C02
