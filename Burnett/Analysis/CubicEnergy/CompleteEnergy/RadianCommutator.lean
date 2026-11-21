import Burnett.Analysis.CubicEnergy.CompleteEnergy.PaperPairing
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.Fourier
open scoped FourierTransform ComplexConjugate ContDiff

private def conjugateSchwartz (w : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (w : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp (w.smooth _)
  decay' := by
    intro k n
    obtain ⟨C,hC⟩ := w.decay' k n
    exact ⟨C,fun x => by rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]; exact hC x⟩

private theorem unitFrequency_pair (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v w : SchwartzMap E ℂ) :
    let a := fun p : Joint => b (p.1+p.2)-b p.2
    Integrable (bilinearFourierWeight a f v w) ∧
    (∫ x, physicalCommutator b f v x * w x) = ∫ p, bilinearFourierWeight a f v w p := by
  dsimp only
  let W := conjugateSchwartz w
  have htest (x : E) : conj (W x) = w x := starRingEnd_self_apply _
  have hFourier (x : E) : conj (𝓕 (W : E → ℂ) x) = 𝓕 (w : E → ℂ) (-x) := by
    change conj (𝓕 (fun y => conj (w y)) x) = _
    rw [fourier_conj_eq_conj_inverse,starRingEnd_self_apply,Real.fourierIntegralInv_eq_fourierIntegral_neg]
  have hw (a : Joint → ℝ) : weightedFourier a f v W = bilinearFourierWeight a f v w := by
    funext y
    change _ * conj (𝓕 (W : E → ℂ) (y.1+y.2)) = _ * 𝓕 (w : E → ℂ) (-(y.1+y.2))
    rw [hFourier]
    rfl
  obtain ⟨hInt,hFreq⟩ := fourier_trilinear_identity b hb hh f v W
  refine ⟨by simpa only [hw] using hInt,?_⟩
  simpa only [htest,hw] using
    ((physical_commutator_pairing_decomposition b hb hh f v W).2.trans hFreq.symm)

def radianCommutator (b : E → ℝ) (f v : SchwartzMap E ℂ) (x : E) : ℂ :=
  radianAction b (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) v.hasTemperateGrowth f) x -
    f x * radianAction b v x

/-- The physical commutator against a bilinear test, with both Fourier
integrals, the negative sum frequency and the literal paper normalization. -/
theorem radian_commutator_pairing (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (f v w : SchwartzMap E ℂ) :
    Integrable (fun x => radianCommutator b f v x * w x) ∧
    Integrable (radianWeight (fun p => b (p.1+p.2)-b p.2) f v w) ∧
    (∫ x, radianCommutator b f v x * w x) =
      (tau^8)⁻¹ • ∫ p, radianWeight (fun q => b (q.1+q.2)-b q.2) f v w p := by
  letI := jointVolume_haar
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let B := fun z : E => b (tau • z)
  have B_eq : B = fun z => tau*b z := funext (hh tau hτ)
  have hs : ContDiffOn ℝ ∞ B {x | x ≠ 0} := by rw [B_eq]; exact contDiffOn_const.mul hb
  have hhom (t : ℝ) (ht : 0<t) (z : E) : B (t • z) = t*B z := by
    rw [B_eq]; dsimp only; rw [hh t ht]; ring
  have hphys (x : E) : radianCommutator b f v x = physicalCommutator B f v x := by
    simp only [radianCommutator,radianAction_eq_orderOne]; rfl
  have law := unitFrequency_pair B hs hhom f v w
  let a := fun p : Joint => b (p.1+p.2)-b p.2
  have pullback : (fun p : Joint => radianWeight a f v w (tau • p)) =
      bilinearFourierWeight (fun p => B (p.1+p.2)-B p.2) f v w := by
    funext p
    simp only [a,B,radianWeight,bilinearFourierWeight,Prod.smul_fst,Prod.smul_snd,
      ← smul_add,← smul_neg,radianFourier_scaled]
  simp_rw [hphys]
  refine ⟨(physical_commutator_bilinear_test B hs hhom f v w).1,
    (integrable_comp_smul_iff volume _ hτ.ne').1 (pullback ▸ law.1),?_⟩
  rw [radianWeight_integral]
  simpa only [B,Prod.smul_fst,Prod.smul_snd,smul_add] using law.2

end Burnett.A02.FrequencySplit
