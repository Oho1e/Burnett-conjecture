import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLowCoefficientInsertion
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianSymbol

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.A06

open MeasureTheory Set Metric Filter
open Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open scoped FourierTransform ContDiff ENNReal NNReal ComplexConjugate Topology

/-- The annular reference for the manuscript's actual low-Cartesian symbol. -/
def lowCartesianHighAnnularReference (a : E → ℂ) (χ : ℝ → ℝ) (b : Joint → ℂ)
    (p : Joint) : ℂ :=
  a p.2 * (tau • lowCartesianSymbol χ b p)

theorem lowCartesianHighAnnularReference_support
    (a : E → ℂ) (χ : ℝ → ℝ) (b : Joint → ℂ) {lo hi ρ : ℝ}
    (hρ : 0 ≤ ρ) (hχ : ∀ x ≥ ρ^2, χ x = 0)
    (hBand : ∀ q, a q ≠ 0 → lo ≤ ‖q‖ ∧ ‖q‖ ≤ hi)
    (p : Joint) (hp : lowCartesianHighAnnularReference a χ b p ≠ 0) :
    lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖ := by
  have hnonzero : a p.2 ≠ 0 := by
    intro he
    exact hp (by simp [lowCartesianHighAnnularReference,he])
  obtain ⟨hl,hu⟩ := hBand p.2 hnonzero
  refine ⟨hl,hu,le_of_not_gt ?_⟩
  intro he
  exact hp (by rw [lowCartesianHighAnnularReference,
    lowCartesianSymbol_eq_zero_outside χ b hρ hχ he.le,smul_zero,mul_zero])

/-- The actual Cartesian annular reference is a compact smooth joint
symbol, using its original smooth extension in the normalized variables. -/
theorem lowCartesianHighAnnularReference_regular
    (a : E → ℂ) (χ : ℝ → ℝ) (b : Joint → ℂ) {lo hi ρ : ℝ}
    (hlo : 0 < lo) (hρ : 0 ≤ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hcut : ∀ x ≥ ρ^2, χ x = 0) (ha : ContDiff ℝ ∞ a)
    (hBand : ∀ q, a q ≠ 0 → lo ≤ ‖q‖ ∧ ‖q‖ ≤ hi)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    HasCompactSupport (lowCartesianHighAnnularReference a χ b) ∧
      ContDiff ℝ ∞ (lowCartesianHighAnnularReference a χ b) := by
  constructor
  · apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : E) (ρ*hi)).prod (isCompact_closedBall (0 : E) hi))
    intro p hp
    obtain ⟨_,hq,hp⟩ := lowCartesianHighAnnularReference_support a χ b hρ hcut hBand p hp
    exact ⟨mem_closedBall_zero_iff.mpr (hp.trans (mul_le_mul_of_nonneg_left hq hρ)),
      mem_closedBall_zero_iff.mpr hq⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.2 = 0
    · have near : ∀ᶠ z : Joint in 𝓝 p, ‖z.2‖ < lo :=
        (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simpa [hp] using hlo)
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [near] with z hz
      have hz0 : a z.2 = 0 := by
        by_contra hz0
        exact hz.not_ge (hBand _ hz0).1
      simp only [lowCartesianHighAnnularReference,hz0,zero_mul]
    · exact (ha.contDiffAt.comp p contDiffAt_snd).mul
        ((lowCartesianSymbol_contDiffAt χ b hρ hχ hcut hV hContains hb hp).const_smul tau)

/-- On any band where the fixed high infrared cutoff is one, the exact
physical reference block is the actual original high-frequency block. -/
theorem radianHighReferenceBlock_eq_regularizedLowCartesianSymbol
    (a : E → ℂ) (η χ : ℝ → ℝ) (b : Joint → ℂ)
    {s : ℝ} (hs : 0 < s) (p : Joint)
    (hη : a ((s/tau) • p.2) ≠ 0 → η ‖p.2‖ = 1) :
    radianHighReferenceBlock (lowCartesianHighAnnularReference a χ b) s p =
      a ((s/tau) • p.2) * regularizedLowCartesianSymbol η χ b p := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  unfold radianHighReferenceBlock lowCartesianHighAnnularReference
  rw [Prod.smul_snd]
  by_cases ha : a ((s/tau) • p.2) = 0
  · simp only [ha,zero_mul,smul_zero]
  · rw [regularizedLowCartesianSymbol,hη ha,one_smul,
      lowCartesianSymbol_smul χ b _ (div_pos hs ht),smul_smul]
    have eq : tau * (s/tau) = s := by field_simp [ht.ne']
    rw [eq,← mul_smul_comm,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]

private def conjugateCoefficient (D : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (D : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp D.smooth'
  decay' k n := by
    obtain ⟨C, _, hC⟩ := D.decay k n
    refine ⟨C, fun x => ?_⟩
    rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
    exact hC x

private theorem conjugateCoefficient_fourier (D : SchwartzMap E ℂ) (z : E) :
    𝓕 (conjugateCoefficient D : E → ℂ) z = conj (𝓕 (D : E → ℂ) (-z)) := by
  rw [← radianFourier_scaled, ← radianFourier_scaled, smul_neg]
  change radianFourier (fun x => conj (D x)) (tau • z) = _
  simpa only [neg_neg] using (radianFourier_conj_neg D (-(tau • z)))

private def inverseProfile (a : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm a

/-- The fixed L¹ mass controlling the Lipschitz norm of a low-pass window. -/
def coefficientWindowMass (a : SchwartzMap E ℂ) : ℝ≥0 :=
  (∫ z : E, ‖inverseProfile a z‖).toNNReal

/-- The actual low-pass window is a fixed integrable convolution after
rescaling the relative physical variable. -/
private theorem windowTest_eq_scaled_convolution (a D : SchwartzMap E ℂ)
    {s : ℝ} (hs : 0 < s) (x : E) :
    windowTest a D s x = ∫ z : E, inverseProfile a z * D (x-s • z) := by
  let K := fun z : E => inverseProfile a z * D (x-s • z)
  have loc := windowTest_translate a D s 0 hs x (0 : E)
  simp only [smul_zero,sub_zero] at loc
  rw [loc,shifted_window_physical a D s hs]
  have formula (y : E) :
      ((s^4)⁻¹ • ((SchwartzMap.fourierTransformCLE ℂ).symm a) (s⁻¹ • (x-y)+0)) * D y =
        (s^4)⁻¹ • K (s⁻¹ • (x-y)) := by
    unfold K inverseProfile
    rw [add_zero, smul_smul, mul_inv_cancel₀ hs.ne',one_smul,sub_sub_cancel,smul_mul_assoc]
  simp_rw [formula]
  let Q := fun z : E => (s^4)⁻¹ • K (s⁻¹ • z)
  change (∫ y : E, Q (x-y)) = _
  have hm := (volume : Measure E).measurePreserving_sub_left x
  rw [hm.integral_comp (Homeomorph.subLeft x).measurableEmbedding Q]
  unfold Q
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume K hs.le,
    show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin,smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hs.ne'),one_smul]

private theorem windowTest_uniformLipschitz (a D : SchwartzMap E ℂ)
    {L : ℝ≥0} (hD : LipschitzWith L D) :
    ∀ {s : ℝ}, 0 < s →
      LipschitzWith (coefficientWindowMass a*L) (windowTest a D s : E → ℂ) := by
  let φ := inverseProfile a
  have hB : (coefficientWindowMass a : ℝ) = ∫ z : E, ‖φ z‖ :=
    Real.coe_toNNReal _ (integral_nonneg (fun _ => norm_nonneg _))
  intro s hs
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have integ (w : E) : Integrable (fun z : E => φ z * D (w-s • z)) := by
    have hcont : Continuous (fun z : E => D (w-s • z)) :=
      D.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))
    refine (φ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 D)).mono'
      (φ.continuous.mul hcont).aestronglyMeasurable ?_
    filter_upwards with z
    change ‖φ z * D (w-s • z)‖ ≤ ‖φ z‖ * SchwartzMap.seminorm ℝ 0 0 D
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (D.norm_le_seminorm ℝ _) (norm_nonneg _)
  rw [dist_eq_norm,windowTest_eq_scaled_convolution a D hs,windowTest_eq_scaled_convolution a D hs,
    ← integral_sub (integ x) (integ y)]
  have hdom : Integrable (fun z : E => ‖φ z‖ * ((L : ℝ)*dist x y)) :=
    φ.integrable.norm.mul_const _
  calc
    _ ≤ ∫ z : E, ‖φ z * D (x-s • z) - φ z * D (y-s • z)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : E, ‖φ z‖ * ((L : ℝ)*dist x y) := by
      apply integral_mono ((integ x).sub (integ y)).norm hdom
      intro z
      change ‖φ z * D (x-s • z) - φ z * D (y-s • z)‖ ≤ _
      rw [← mul_sub,norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hD.dist_le_mul (x-s • z) (y-s • z)
    _ = _ := by rw [integral_mul_const,NNReal.coe_mul,hB]; ring

/-- A fixed actual low-pass profile produces real coefficients with the
stated low Fourier support and a scale-independent Lipschitz budget. -/
theorem exists_actual_spectralLowCoefficient
    (a D : SchwartzMap E ℂ) (ε : ℝ)
    (ha : ∀ z : E, a z ≠ 0 → ‖z‖ ≤ ε) {L : ℝ≥0} (hD : LipschitzWith L D) :
    ∀ {s : ℝ}, 0 < s →
      ∃ C : SchwartzMap E ℂ, ∃ c : E → ℝ,
        (∀ x, c x = (windowTest a D s x).re) ∧ (∀ x, C x = (c x : ℂ)) ∧
        LipschitzWith (coefficientWindowMass a*L) c ∧
        ∀ z : E, 𝓕 (C : E → ℂ) z ≠ 0 → ‖s • z‖ ≤ ε := by
  intro s hs
  have bound := windowTest_uniformLipschitz a D hD hs
  let U := windowTest a D s
  let C := (2⁻¹ : ℂ) • (U + conjugateCoefficient U)
  let c := fun x : E => (U x).re
  refine ⟨C,c,fun _ => rfl,?_,?_,?_⟩
  · intro x
    change (2⁻¹ : ℂ) * (U x + conj (U x)) = ((U x).re : ℂ)
    have half : (2⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    rw [half]
    apply Complex.ext
    · simp [Complex.mul_re,Complex.add_re]
      ring
    · simp [Complex.mul_im,Complex.add_im]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := bound.dist_le_mul x y
    change |(U x).re - (U y).re| ≤ _
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using h)
  · intro z hz
    by_contra! h
    have z0 : a (s • z) = 0 := by
      by_contra hz; exact (not_le_of_gt h) (ha _ hz)
    have neg0 : a (s • (-z)) = 0 := by
      by_contra hz
      apply (not_le_of_gt h)
      simpa only [smul_neg,norm_neg] using ha _ hz
    apply hz
    change (SchwartzMap.fourierTransformCLM ℂ C) z = 0
    unfold C
    rw [map_smul,map_add]
    simp only [SchwartzMap.smul_apply,SchwartzMap.add_apply,SchwartzMap.fourierTransformCLM_apply,
      conjugateCoefficient_fourier,U,windowTest_fourier,z0,neg0,mul_zero,map_zero,add_zero,smul_zero]

/-- Applying a single fixed low-pass to the same input coefficient at each
scale yields the uniform low-coefficient branch of the actual radian form. -/
theorem exists_lowpassCoefficientRadianBlocks_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ε : ℝ} (hlo : 0 < lo) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hε₀ : 0 ≤ ε) (hε : ε < (1-ρ)*lo)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b d cProfile : SchwartzMap E ℂ) (hCup : ∀ z, cProfile z ≠ 0 → ‖z‖ ≤ ε)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (u • z) = 1)
    (hIn : ∀ z : E, lo-ε ≤ ‖z‖ → ‖z‖ ≤ hi+ε → a (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo-ε ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi+ε → b (w • z) = 1) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (L : ℝ≥0) (D : SchwartzMap E ℂ),
      LipschitzWith L D → ∀ (f g h : SchwartzMap E ℂ),
        ‖∑ i : Fin n, radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t (i : ℕ)))
          (fun x => (windowTest cProfile D (dyadicScale t (i : ℕ)) x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨M,hM,bound⟩ := exists_lowCoefficientRadianBlocks_sum_bound_paper inputL2 A ha hA hlo hρ hρ' hε₀ hε
    hBand a b d hca hcb ca cb hu hv hw hLow hIn hOut
  refine ⟨(coefficientWindowMass cProfile : ℝ≥0∞)*M,ENNReal.mul_lt_top ENNReal.coe_lt_top hM,?_⟩
  intro t ht n L D hD f g h
  have positive (i : Fin n) : 0 < dyadicScale t (i : ℕ) := by unfold dyadicScale; positivity
  choose C c hcEq hReal hLip hFreq using
    fun i : Fin n => exists_actual_spectralLowCoefficient cProfile D ε hCup hD (positive i)
  have hc : c = fun (i : Fin n) x => (windowTest cProfile D (dyadicScale t (i : ℕ)) x).re :=
    funext fun i => funext (hcEq i)
  have est := bound ht n (coefficientWindowMass cProfile * L) c C hReal hLip hFreq f g h
  rw [hc, ENNReal.coe_mul] at est
  exact est.trans_eq (by ring)

theorem exists_lowpassCoefficientRadianBlocks_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ε : ℝ} (hlo : 0 < lo) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hε₀ : 0 ≤ ε) (hε : ε < (1-ρ)*lo)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b d cProfile : SchwartzMap E ℂ) (hCup : ∀ z, cProfile z ≠ 0 → ‖z‖ ≤ ε)
    (hca : HasCompactSupport (a : E → ℂ)) (hcb : HasCompactSupport (b : E → ℂ))
    (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    {u v w : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (u • z) = 1)
    (hIn : ∀ z : E, lo-ε ≤ ‖z‖ → ‖z‖ ≤ hi+ε → a (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo-ε ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi+ε → b (w • z) = 1) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (L : ℝ≥0) (D : SchwartzMap E ℂ),
      LipschitzWith L D → ∀ (f g h : SchwartzMap E ℂ),
        ‖∑ i : Fin n, radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t (i : ℕ)))
          (fun x => (windowTest cProfile D (dyadicScale t (i : ℕ)) x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_lowpassCoefficientRadianBlocks_sum_bound_paper false A ha hA hlo hρ hρ' hε₀ hε hBand
    a b d cProfile hCup hca hcb ca cb hu hv hw hLow hIn hOut

end Burnett.A06
