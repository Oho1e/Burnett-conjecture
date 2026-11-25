import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianSymbol
import Mathlib.MeasureTheory.Group.Prod
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false

noncomputable section

namespace Burnett.A06

open Filter MeasureTheory
open Burnett.A02.FrequencySplit (E Joint radianFourier tau)
open scoped ComplexConjugate RealInnerProductSpace

/-- Reindex the same low frequency and interchange the high input and output. -/
def highAdjointFrequencies : Joint ≃ᵐ Joint where
  toFun x := (-x.1, x.2 + x.1)
  invFun x := (-x.1, x.2 + x.1)
  left_inv x := by
    apply Prod.ext
    · simp
    · change x.2 + x.1 + -x.1 = x.2
      abel
  right_inv x := by
    apply Prod.ext
    · simp
    · change x.2 + x.1 + -x.1 = x.2
      abel
  measurable_toFun := measurable_fst.neg.prodMk (measurable_snd.add measurable_fst)
  measurable_invFun := measurable_fst.neg.prodMk (measurable_snd.add measurable_fst)

theorem measurePreserving_highAdjointFrequencies :
    MeasurePreserving highAdjointFrequencies (volume : Measure Joint) volume := by
  let μ : Measure E := volume
  rw [Measure.volume_eq_prod E E]
  have add := measurePreserving_prod_add μ μ
  have neg := (Measure.measurePreserving_neg μ).prod (MeasurePreserving.id μ)
  convert neg.comp add using 1
  funext x
  change (-x.1, x.2 + x.1) = (-x.1, x.1 + x.2)
  rw [add_comm]

/-- The scalar high-slot adjoint symbol in the convention of manuscript line 1443. -/
def highAdjointSymbol (b : Joint → ℂ) (x : Joint) : ℂ :=
  conj (b (highAdjointFrequencies x))

theorem highAdjointSymbol_involution (b : Joint → ℂ) :
    highAdjointSymbol (highAdjointSymbol b) = b := by
  funext x
  change conj (conj (b (highAdjointFrequencies.symm (highAdjointFrequencies x)))) = b x
  rw [MeasurableEquiv.symm_apply_apply, starRingEnd_self_apply]

/-- The pulled-back true Cartesian symbol uses its original high infrared cutoff
on the new high output. Both high frequencies stay quantitatively comparable. -/
theorem regularizedLowCartesianSymbol_highAdjointSupport
    (η χ : ℝ → ℝ) (c : Joint → ℂ) {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1)
    (hχ : ∀ s ≥ ρ ^ 2, χ s = 0) (hη : ∀ s ≤ R, η s = 0)
    (x : Joint) (h : highAdjointSymbol (regularizedLowCartesianSymbol η χ c) x ≠ 0) :
    ‖x.1‖ < ρ * ‖x.2 + x.1‖ ∧
      ‖x.1‖ < (ρ / (1 - ρ)) * ‖x.2‖ ∧
      (1 - ρ) * ‖x.2 + x.1‖ ≤ ‖x.2‖ ∧
      ‖x.2‖ ≤ (1 + ρ) * ‖x.2 + x.1‖ ∧
      R < ‖x.2 + x.1‖ ∧ (1 - ρ) * R < ‖x.2‖ := by
  have hb : regularizedLowCartesianSymbol η χ c (highAdjointFrequencies x) ≠ 0 :=
    fun hz => h (by simp [highAdjointSymbol, hz])
  have hnew : R < ‖x.2 + x.1‖ := by
    by_contra! hle
    apply hb
    change η ‖x.2 + x.1‖ • _ = (0 : ℂ)
    rw [hη _ hle, zero_smul]
  have hsupp : ‖x.1‖ < ρ * ‖x.2 + x.1‖ := by
    by_contra! hle
    apply hb
    have low := lowCartesianSymbol_eq_zero_outside χ c hρ hχ
      (x := highAdjointFrequencies x) (by simpa [highAdjointFrequencies] using hle)
    rw [regularizedLowCartesianSymbol, low, smul_zero]
  have hupper : ‖x.2 + x.1‖ ≤ ‖x.2‖ + ‖x.1‖ := norm_add_le _ _
  have hlower : ‖x.2‖ ≤ ‖x.2 + x.1‖ + ‖x.1‖ := by
    simpa using norm_add_le (x.2 + x.1) (-x.1)
  have hcmp : (1 - ρ) * ‖x.2 + x.1‖ ≤ ‖x.2‖ := by linarith
  have hpositive : 0 < 1 - ρ := sub_pos.mpr hρsmall
  refine ⟨hsupp, ?_, hcmp, by linarith, hnew, ?_⟩
  · have hex : ρ * ‖x.2 + x.1‖ ≤ (ρ / (1 - ρ)) * ‖x.2‖ := by
      rw [show (ρ / (1 - ρ)) * ‖x.2‖ = (ρ * ‖x.2‖) / (1 - ρ) by ring]
      apply (le_div_iff₀ hpositive).mpr
      simpa only [mul_assoc, mul_comm ‖x.2 + x.1‖] using mul_le_mul_of_nonneg_left hcmp hρ
    exact hsupp.trans_le hex
  · exact (mul_lt_mul_of_pos_left hnew hpositive).trans_le hcmp

theorem radianFourier_conj_neg (f : E → ℂ) (p : E) :
    radianFourier (fun x => conj (f x)) (-p) = conj (radianFourier f p) := by
  unfold radianFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_right, neg_neg, map_mul, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, neg_mul, mul_neg]

def radianHighPairWeight (b : Joint → ℂ) (f u v : E → ℂ) (x : Joint) : ℂ :=
  b x * radianFourier f x.1 * radianFourier u x.2 *
    conj (radianFourier v (x.2 + x.1))

/-- The fixed normalization for the sesquilinear Fourier pairing on the two
four-dimensional frequency variables. -/
def radianHighPair (b : Joint → ℂ) (f u v : E → ℂ) : ℂ :=
  (tau ^ 8)⁻¹ • ∫ x, radianHighPairWeight b f u v x

/-- Exact scalar Fourier adjunction. The high slots exchange and the same low
field is conjugated. Whenever the pairing is integrable this is the ordinary
Fourier integral identity, with the same normalization on both sides. -/
theorem radianHighPair_highAdjoint (b : Joint → ℂ) (f u v : E → ℂ) :
    radianHighPair (highAdjointSymbol b) (fun x => conj (f x)) v u =
      conj (radianHighPair b f u v) := by
  unfold radianHighPair
  rw [show (conj ((tau ^ 8)⁻¹ • ∫ x, radianHighPairWeight b f u v x)) =
      (tau ^ 8)⁻¹ • conj (∫ x, radianHighPairWeight b f u v x) from
    (Complex.conjCLE.toContinuousLinearMap.map_smul _ _)]
  rw [← integral_conj, ← measurePreserving_highAdjointFrequencies.integral_comp'
      (fun x => conj (radianHighPairWeight b f u v x))]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  have hhigh : (x.2 + x.1) + -x.1 = x.2 := by abel
  simp only [radianHighPairWeight, highAdjointSymbol, map_mul, starRingEnd_self_apply]
  change conj (b (highAdjointFrequencies x)) * radianFourier (fun y => conj (f y)) x.1 *
    radianFourier v x.2 * conj (radianFourier u (x.2 + x.1)) = _
  change _ = conj (b (highAdjointFrequencies x)) * conj (radianFourier f (-x.1)) *
    conj (radianFourier u (x.2 + x.1)) * radianFourier v ((x.2 + x.1) + -x.1)
  have hf := radianFourier_conj_neg f (-x.1)
  rw [neg_neg] at hf
  rw [hhigh, hf]
  ring

/-- Fourier pairing for Bényi–Oh's commutator sign, with a real coefficient in
the high input or moved from the output onto the test field. -/
def radianHighCommutatorPair (b : Joint → ℂ) (d : E → ℝ) (f u v : E → ℂ) : ℂ :=
  radianHighPair b f (fun x => (d x : ℂ) * u x) v -
    radianHighPair b f u (fun x => (d x : ℂ) * v x)

theorem radianHighCommutatorPair_highAdjoint
    (b : Joint → ℂ) (d : E → ℝ) (f u v : E → ℂ) :
    radianHighCommutatorPair (highAdjointSymbol b) d (fun x => conj (f x)) v u =
      -conj (radianHighCommutatorPair b d f u v) := by
  rw [radianHighCommutatorPair, radianHighPair_highAdjoint, radianHighPair_highAdjoint]
  simp only [radianHighCommutatorPair, map_sub, neg_sub]

end Burnett.A06
