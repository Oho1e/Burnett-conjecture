import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLowCoefficientSum
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLowCoefficientGeometry
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotRadianBlock
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotAdjoint

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal NNReal FourierTransform ComplexConjugate BigOperators

private theorem radianHighPair_eq_ordinary (m : Joint → ℂ) (f g h : E → ℂ) :
    radianHighPair m f g h =
      ∫ p : Joint, m (tau • p) * 𝓕 f p.1 * 𝓕 g p.2 * conj (𝓕 h (p.1+p.2)) := by
  letI := jointVolume_haar
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have dimJoint : Module.finrank ℝ Joint = 8 := by rw [Module.finrank_prod,dimE]
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have eq := Measure.integral_comp_smul_of_nonneg (volume : Measure Joint)
    (radianHighPairWeight m f g h) tau (hR := ht.le)
  rw [dimJoint] at eq
  rw [radianHighPair, ← eq]
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianHighPairWeight,Prod.smul_fst,Prod.smul_snd,← smul_add,radianFourier_scaled,
    add_comm p.2 p.1]

private def multiplySchwartz (C g : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) C.hasTemperateGrowth g

private theorem multiplySchwartz_apply (C g : SchwartzMap E ℂ) (x : E) :
    multiplySchwartz C g x = C x * g x := mul_comm _ _

/-- The two actual high-slot commutator terms admit the same three window
insertions for a coefficient supported in the stated low-frequency ball. -/
theorem highSlotBlockPair_windowed_eq_radian_of_lowCoefficient
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ε : ℝ} (hlo : 0 < lo) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hε₀ : 0 ≤ ε) (hε : ε < (1-ρ)*lo)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b d : SchwartzMap E ℂ) (u v w : ℝ)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (u • z) = 1)
    (hIn : ∀ z : E, lo-ε ≤ ‖z‖ → ‖z‖ ≤ hi+ε → a (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo-ε ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi+ε → b (w • z) = 1)
    (s : ℝ) (c : E → ℝ) (C : SchwartzMap E ℂ)
    (hReal : ∀ x, C x = (c x : ℂ))
    (hC : ∀ z : E, 𝓕 (C : E → ℂ) z ≠ 0 → ‖s • z‖ ≤ ε)
    (f g h : SchwartzMap E ℂ) :
    highSlotBlockPair A s c (windowTest d f (u*s)) (windowTest a g (v*s)) (windowTest b h (w*s)) =
      radianHighCommutatorPair (radianHighReferenceBlock A s) c f g h := by
  let F := windowTest d f (u*s)
  let G := windowTest a g (v*s)
  let H := windowTest b h (w*s)
  have geom (p : Joint) (hp : A (s • p) ≠ 0) (z : E) (hz : ‖s • z‖ ≤ ε) :
      ‖s • p.1‖ ≤ ρ*hi ∧
      (lo-ε ≤ ‖s • (p.2-z)‖ ∧ ‖s • (p.2-z)‖ ≤ hi+ε) ∧
      ((1-ρ)*lo-ε ≤ ‖s • (p.1+p.2-z)‖ ∧ ‖s • (p.1+p.2-z)‖ ≤ (1+ρ)*hi+ε) := by
    obtain ⟨hl,hu,hp⟩ := hBand (s • p) hp
    have zbound := lowCoefficient_shifted_annuli hlo hρ hρ' hε ⟨hl,hu⟩ hp hz
    simpa only [smul_sub,smul_add] using zbound.2.2
  have fwin (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (F : E → ℂ) p.1 = 𝓕 (f : E → ℂ) p.1 := by
    rw [show F = windowTest d f (u*s) from rfl,windowTest_fourier,← smul_smul,
      hLow _ (geom p hp 0 (by simpa using hε₀)).1,mul_one]
  have gwin (p : Joint) (hp : A (s • p) ≠ 0) (z : E) (hz : ‖s • z‖ ≤ ε) :
      𝓕 (G : E → ℂ) (p.2-z) = 𝓕 (g : E → ℂ) (p.2-z) := by
    have hb := (geom p hp z hz).2.1
    rw [show G = windowTest a g (v*s) from rfl,windowTest_fourier,← smul_smul,
      hIn _ hb.1 hb.2,mul_one]
  have hwin (p : Joint) (hp : A (s • p) ≠ 0) (z : E) (hz : ‖s • z‖ ≤ ε) :
      𝓕 (H : E → ℂ) (p.1+p.2-z) = 𝓕 (h : E → ℂ) (p.1+p.2-z) := by
    have hb := (geom p hp z hz).2.2
    rw [show H = windowTest b h (w*s) from rfl,windowTest_fourier,← smul_smul,
      hOut _ hb.1 hb.2,mul_one]
  have gprod (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (fun x : E => (c x : ℂ)*G x) p.2 = 𝓕 (fun x : E => (c x : ℂ)*g x) p.2 := by
    simp_rw [← hReal]
    exact fourier_schwartz_product_replace C G g _ (fun z hz => gwin p hp z (hC z hz))
  have hprod (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (fun x : E => (c x : ℂ)*H x) (p.1+p.2) = 𝓕 (fun x : E => (c x : ℂ)*h x) (p.1+p.2) := by
    simp_rw [← hReal]
    exact fourier_schwartz_product_replace C H h _ (fun z hz => hwin p hp z (hC z hz))
  have ref (p : Joint) : radianHighReferenceBlock A s (tau • p) = s⁻¹ • A (s • p) := by
    rw [radianHighReferenceBlock,smul_smul,div_mul_cancel₀ _ (mul_pos (by norm_num) Real.pi_pos).ne']
  change highSlotBlockPair A s c F G H = _
  rw [highSlotBlockPair_eq_radianHighCommutatorPair A ha hA s c F G H
    (multiplySchwartz C G) (multiplySchwartz C H)
    (fun x => by rw [multiplySchwartz_apply,hReal])
    (fun x => by rw [multiplySchwartz_apply,hReal])]
  simp_rw [radianHighCommutatorPair,radianHighPair_eq_ordinary,ref]
  congr 1
  · apply integral_congr_ae
    filter_upwards with p
    by_cases hzero : A (s • p) = 0
    · simp only [hzero,smul_zero,zero_mul]
    · have he := hwin p hzero 0 (by simpa using hε₀)
      simp only [sub_zero] at he
      rw [fwin p hzero,gprod p hzero,he]
  · apply integral_congr_ae
    filter_upwards with p
    by_cases hzero : A (s • p) = 0
    · simp only [hzero,smul_zero,zero_mul]
    · have he := gwin p hzero 0 (by simpa using hε₀)
      simp only [sub_zero] at he
      rw [fwin p hzero,he,hprod p hzero]

/-- A genuinely uniform estimate of the original radian high-slot pairings
on the spectrally low coefficient branch of a fixed reference family. -/
theorem exists_lowCoefficientRadianBlocks_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ε : ℝ} (hlo : 0 < lo) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hε₀ : 0 ≤ ε) (hε : ε < (1-ρ)*lo)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b d : SchwartzMap E ℂ)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (u • z) = 1)
    (hIn : ∀ z : E, lo-ε ≤ ‖z‖ → ‖z‖ ≤ hi+ε → a (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo-ε ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi+ε → b (w • z) = 1) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (L : ℝ≥0)
      (c : Fin n → E → ℝ) (C : Fin n → SchwartzMap E ℂ),
      (∀ i x, C i x = (c i x : ℂ)) → (∀ i, LipschitzWith L (c i)) →
      (∀ i z, 𝓕 (C i : E → ℂ) z ≠ 0 → ‖dyadicScale t (i : ℕ) • z‖ ≤ ε) →
      ∀ f g h : SchwartzMap E ℂ,
        ‖∑ i : Fin n, radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t (i : ℕ)))
          (c i) f g h‖ₑ ≤ (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨M,hM,bound⟩ := exists_highSlotWindowedBlock_sum_bound_paper inputL2 A ha hA a b d hca hcb ca cb hu hv hw
  refine ⟨M,hM,?_⟩
  intro t ht n L c C hReal hLip hFreq f g h
  have eq (i : Fin n) : highSlotWindowedBlock A a b d u v w t (c i) f g h i =
      radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t (i : ℕ))) (c i) f g h :=
    highSlotBlockPair_windowed_eq_radian_of_lowCoefficient A ha hA hlo hρ hρ' hε₀ hε hBand
      a b d u v w hLow hIn hOut _ (c i) (C i) (hReal i) (hFreq i) f g h
  simpa only [eq] using bound ht n L c hLip f g h

theorem exists_lowCoefficientRadianBlocks_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ε : ℝ} (hlo : 0 < lo) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hε₀ : 0 ≤ ε) (hε : ε < (1-ρ)*lo)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b d : SchwartzMap E ℂ)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (u • z) = 1)
    (hIn : ∀ z : E, lo-ε ≤ ‖z‖ → ‖z‖ ≤ hi+ε → a (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo-ε ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi+ε → b (w • z) = 1) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (L : ℝ≥0)
      (c : Fin n → E → ℝ) (C : Fin n → SchwartzMap E ℂ),
      (∀ i x, C i x = (c i x : ℂ)) → (∀ i, LipschitzWith L (c i)) →
      (∀ i z, 𝓕 (C i : E → ℂ) z ≠ 0 → ‖dyadicScale t (i : ℕ) • z‖ ≤ ε) →
      ∀ f g h : SchwartzMap E ℂ,
        ‖∑ i : Fin n, radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t (i : ℕ)))
          (c i) f g h‖ₑ ≤ (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_lowCoefficientRadianBlocks_sum_bound_paper false A ha hA hlo hρ hρ' hε₀ hε hBand a b d hca hcb ca cb hu hv hw
    hLow hIn hOut

end Burnett.A06
