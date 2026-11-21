import Burnett.Analysis.PrincipalEnergy.Commutator.ActualConstantCarleson
import Burnett.Analysis.PrincipalEnergy.Quantization.FullActionProperties
import Burnett.Analysis.PrincipalEnergy.Commutator.ParaproductCover
import Burnett.Analysis.CenteredMaximal.MaximalStrong

set_option autoImplicit false
set_option maxHeartbeats 2700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Metric Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.CenteredMaximal
open scoped BigOperators ENNReal NNReal ComplexConjugate

private abbrev UnitVolume : ℝ := (volume : Measure Space).real (ball (0:Space) 1)

private theorem unitVolume_pos : 0 < UnitVolume :=
  ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

private theorem real_closedBall_volume (x : Space) (R : ℝ) (hR : 0≤R) :
    (volume : Measure Space).real (closedBall x R) = R^4*UnitVolume := by
  rw [Measure.addHaar_real_closedBall volume x hR,finrank_euclideanSpace_fin]

private theorem real_ball_volume (x : Space) (R : ℝ) (hR : 0≤R) :
    (volume : Measure Space).real (ball x R) = R^4*UnitVolume := by
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x R]
  exact real_closedBall_volume x R hR

private def maximalSchwartz (f : SchwartzMap Space ℂ) : Space → ℝ≥0∞ :=
  centeredMax (fun y => ‖f y‖ₑ)

private theorem maximalSchwartz_ne_top (f : SchwartzMap Space ℂ) (y : Space) :
    maximalSchwartz f y ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (centeredMax_le_const _ (ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 f)) (fun z => ?_) y)
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (SchwartzMap.norm_le_seminorm ℝ f z)

private theorem norm_integral_ball_le_maximalSchwartz (f : SchwartzMap Space ℂ)
    (y : Space) (s : ℝ) (hs : 0<s) :
    (∫ z in closedBall y s, ‖f z‖) ≤ (volume : Measure Space).real (closedBall y s)*
      (maximalSchwartz f y).toReal := by
  let S := closedBall y s
  let μ : Measure Space := volume
  have hDiv : (∫⁻ z in S, ‖f z‖ₑ) / μ S ≤ maximalSchwartz f y :=
    le_iSup (fun r : {t : ℝ // 0<t} => (∫⁻ z in closedBall y r, ‖f z‖ₑ) / μ (closedBall y r)) ⟨s,hs⟩
  have hVol : μ S ≠ ⊤ := measure_closedBall_lt_top.ne
  have hPositive : μ S ≠ 0 := (measure_closedBall_pos μ y hs).ne'
  have hMul := (ENNReal.div_le_iff_le_mul (.inl hPositive) (.inl hVol)).mp hDiv
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top (maximalSchwartz_ne_top f y) hVol) hMul
  rw [← ofReal_integral_norm_eq_lintegral_enorm f.integrable.integrableOn,
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _)), ENNReal.toReal_mul,
    mul_comm] at hReal
  exact hReal

private def compactAverageBound (φ : SchwartzMap Space ℂ) : ℝ :=
  16 * SchwartzMap.seminorm ℝ 0 0 φ * UnitVolume

private theorem compactAverageBound_nonneg (φ : SchwartzMap Space ℂ) :
    0 ≤ compactAverageBound φ := by
  unfold compactAverageBound
  exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) unitVolume_pos.le

/-- The actual compact smoothing of a Schwartz input at one point is
dominated by the centered maximal function at every point of its scale ball. -/
theorem compactWaveletAction_le_local_maximal (φ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z = 0) (f : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) (x y : Space) (hy : y∈ball x s) :
    ‖compactWaveletAction φ s f x‖ ≤ compactAverageBound φ*(maximalSchwartz f y).toReal := by
  let A := SchwartzMap.seminorm ℝ 0 0 φ
  let K := compactWaveletKernel φ s
  let S := closedBall x s
  let C := (s^4)⁻¹*A
  have hC : 0≤C := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hMajor (z : Space) : ‖K (x-z) * f z‖ ≤ S.indicator (fun w => C*‖f w‖) z := by
    rw [norm_mul]
    by_cases hz : z∈S
    · rw [indicator_of_mem hz]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      change ‖(s^4)⁻¹ • φ (s⁻¹ • (x-z))‖ ≤ C
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (s^4)⁻¹)]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) (by positivity)
    · have hz' : s < ‖x-z‖ := by simpa [S,mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
      have h := hφ (s⁻¹ • (x-z)) (by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),← div_eq_inv_mul]
        exact (one_lt_div₀ hs).mpr hz')
      simp [K,compactWaveletKernel,h,indicator_of_notMem hz]
  have hSubset : S ⊆ closedBall y (2*s) := by
    intro z hz
    apply mem_closedBall.mpr
    have h₁ := mem_closedBall.mp hz
    have h₂ := mem_ball.mp hy
    linarith [dist_triangle z x y, show dist x y < s by simpa only [dist_comm] using h₂]
  calc
    _ ≤ ∫ z, ‖K (x-z)*f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, S.indicator (fun w => C*‖f w‖) z :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        ((f.integrable.norm.const_mul C).indicator measurableSet_closedBall)
        (Eventually.of_forall hMajor)
    _ = C*(∫ z in S, ‖f z‖) := by rw [integral_indicator measurableSet_closedBall,integral_const_mul]
    _ ≤ C*(∫ z in closedBall y (2*s), ‖f z‖) := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set f.integrable.norm.integrableOn (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hSubset)) hC
    _ ≤ C*((volume : Measure Space).real (closedBall y (2*s))*(maximalSchwartz f y).toReal) :=
      mul_le_mul_of_nonneg_left (norm_integral_ball_le_maximalSchwartz f y _ (by positivity)) hC
    _ = _ := by
      rw [real_closedBall_volume y _ (by positivity)]
      unfold compactAverageBound C A
      field_simp [hs.ne']
      ring

private theorem compactBase_commutatorConstant_integrable {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (r : SchwartzMap Space ℂ) :
    Integrable (coefficientCommutatorConstant a r) volume := by
  obtain ⟨D,_,hOrd⟩ := ha.order 0
  have hzero : Continuous (fun x => a x 0) := hCont.comp (continuous_id.prodMk continuous_const)
  have hprod : Integrable (fun x => r x * a x 0) volume := by
    have h := (r.integrable (μ := (volume : Measure Space))).bdd_mul
      hzero.aestronglyMeasurable ⟨D,fun x => by
      simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero,norm_zero,add_zero] using hOrd x 0⟩
    simpa only [mul_comm] using h
  exact hprod.sub (firstOrderAction_integrable_of_compactBase hBase hCont r)

private theorem integral_sq_to_lintegral {v : Space → ℂ} {μ : Measure Space} (hv : MemLp v 2 μ) :
    ENNReal.ofReal (∫ x, ‖v x‖^2 ∂μ) = ∫⁻ x, ‖v x‖ₑ ^ (2:ℕ) ∂μ := by
  rw [ofReal_integral_eq_lintegral_ofReal (hv.integrable_norm_pow (p := 2) (by decide))
    (Eventually.of_forall fun _ => sq_nonneg _)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm]

/-- A genuine finite paraproduct's coefficient times the lower factor
has uniform vertical L² energy, with the actual compact-base T(1). -/
theorem exists_compactBase_commutatorConstant_weighted_wavelet_square_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (ψ φ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0) (hφ : ∀ z, 1<‖z‖ → φ z = 0) :
    ∃ A : ℝ≥0∞, A≠⊤ ∧ ∀ (r f : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) → ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ),
        (∑ j ∈ J, ∫⁻ x,
          ‖compactWaveletAction ψ (compactWaveletScale t j) (coefficientCommutatorConstant a r) x *
            compactWaveletAction φ (compactWaveletScale t j) f x‖ₑ ^ (2:ℕ)) ≤
        A * (ENNReal.ofReal (U+(L:ℝ)))^2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℕ) := by
  obtain ⟨C,hC,hCarleson⟩ := exists_compactBase_commutatorConstant_wavelet_carleson ha hBase hCont ψ hψ hMean
  obtain ⟨D,hD,hSquare⟩ := exists_compactWaveletAction_square_bound ψ hMean
  let V := UnitVolume
  let P := compactAverageBound φ
  let K := maximalConstant 2
  let A := (256:ℝ≥0∞)*ENNReal.ofReal (C/V)*(ENNReal.ofReal P)^2*K
  have hP : 0≤P := compactAverageBound_nonneg φ
  have hK : K≠⊤ := (maximalConstant_finite 2).ne
  refine ⟨A,by dsimp [A]; finiteness,?_⟩
  intro r f L U hU hLip hR t ht J
  let s := compactWaveletScale t
  let b := coefficientCommutatorConstant a r
  let Q (j : ℕ) := compactWaveletAction ψ (s j) b
  let F (j : ℕ) (x : Space) := ‖compactWaveletAction φ (s j) f x‖
  let M (x : Space) := P*(maximalSchwartz f x).toReal
  let ν (j : ℕ) : Measure Space := volume.withDensity (fun x => ‖Q j x‖ₑ ^ (2:ℕ))
  let B := ENNReal.ofReal (C/V)*(ENNReal.ofReal (U+(L:ℝ)))^2
  have hs (j : ℕ) : 0<s j := div_pos ht (pow_pos (by norm_num) _)
  have hs' (j : ℕ) : s j≤t := div_le_self ht.le (one_le_pow₀ (by norm_num))
  have hb₁ := compactBase_commutatorConstant_integrable ha.frequency hBase hCont r
  have hb₂ := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  have hQLp : ∀ j, MemLp (Q j) 2 volume := (hSquare t ht J b hb₁ hb₂).1
  have hMeasQ (j : ℕ) : Measurable (fun x => ‖Q j x‖ₑ^(2:ℕ)) :=
    (compactWaveletAction_continuous ψ (s j) (hs j) b hb₁).measurable.enorm.pow_const _
  have hMeasF (j : ℕ) : Measurable (F j) :=
    (compactWaveletAction_continuous φ (s j) (hs j) f f.integrable).norm.measurable
  have hMeasM : Measurable M := measurable_const.mul (centeredMax_measurable _).ennreal_toReal
  have hPack (c : Space) (R : ℝ) (hRpos : 0<R) :
      (∑ j ∈ J.filter (fun j => s j ≤ R), ν j (ball c R)) ≤ B*volume (ball c R) := by
    have hMass (j : ℕ) : ν j (ball c R) = ENNReal.ofReal (∫ x in ball c R, ‖Q j x‖^2) := by
      dsimp only [ν]
      rw [withDensity_apply _ measurableSet_ball]
      exact (integral_sq_to_lintegral ((hQLp j).restrict _)).symm
    have hCap := hCarleson r L U hU hLip hR c R t hRpos ht
      (J.filter (fun j => s j≤R)) (fun j hj => (Finset.mem_filter.mp hj).2)
    have hVol : volume (ball c R) = ENNReal.ofReal (R^4*V) := by
      rw [← real_ball_volume c R hRpos.le]
      exact (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    simp_rw [hMass]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))]
    refine (ENNReal.ofReal_le_ofReal hCap).trans_eq ?_
    have hUV : 0≤U+(L:ℝ) := add_nonneg hU L.coe_nonneg
    rw [hVol,show C*(U+(L:ℝ))^2*R^4 = (C/V)*(U+(L:ℝ))^2*(R^4*V) by
      field_simp [show V≠0 from unitVolume_pos.ne']]
    rw [ENNReal.ofReal_mul (mul_nonneg (div_nonneg hC unitVolume_pos.le) (sq_nonneg _)),
      ENNReal.ofReal_mul (div_nonneg hC unitVolume_pos.le),ENNReal.ofReal_pow hUV]
  have hEmbed := finite_ball_carleson_square_le J s t (fun j _ => ⟨hs j,hs' j⟩) ν B
    (by dsimp [B]; finiteness) hPack F hMeasF (fun _ _ => norm_nonneg _) M hMeasM
    (fun _ => mul_nonneg hP ENNReal.toReal_nonneg)
    (fun j _ x y hy => compactWaveletAction_le_local_maximal φ hφ f (s j) (hs j) x y hy)
  have hPair (j : ℕ) :
      (∫⁻ x, ENNReal.ofReal ((F j x)^2) ∂ν j) =
        ∫⁻ x, ‖Q j x * compactWaveletAction φ (s j) f x‖ₑ^(2:ℕ) := by
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul volume (hMeasQ j) ((hMeasF j).pow_const _).ennreal_ofReal]
    simp only [Pi.mul_apply,F,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm,enorm_mul,mul_pow]
  simp_rw [hPair] at hEmbed
  have hMax := centeredMax_strong_moment (fun y : Space => ‖f y‖ₑ) f.continuous.measurable.enorm 2 (by norm_num)
  have hMSq : (∫⁻ x, ENNReal.ofReal ((M x)^2)) ≤
      (ENNReal.ofReal P)^2*K * ∫⁻ x, ‖f x‖ₑ^(2:ℕ) := by
    have hPoint (x : Space) : ENNReal.ofReal ((M x)^2) =
        (ENNReal.ofReal P)^2*(maximalSchwartz f x)^(2:ℕ) := by
      dsimp only [M]
      rw [mul_pow,ENNReal.ofReal_mul (sq_nonneg P),ENNReal.ofReal_pow hP,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (maximalSchwartz_ne_top f x)]
    simp_rw [hPoint]
    rw [lintegral_const_mul' _ _ (by finiteness : (ENNReal.ofReal P)^2 ≠ ⊤)]
    rw [mul_assoc]
    apply mul_le_mul_left'
    simpa only [maximalSchwartz,ENNReal.rpow_two] using hMax
  refine hEmbed.trans ((mul_le_mul_left' hMSq (256*B)).trans_eq ?_)
  dsimp only [B,A,K]
  ac_rfl

/-- One smooth paraproduct scale, tested in the complex L² pairing. -/
def compactWaveletParaproductTerm (ψ φ : SchwartzMap Space ℂ) (s : ℝ)
    (b : Space → ℂ) (f g : SchwartzMap Space ℂ) : ℂ :=
  ∫ x, conj (compactWaveletAction ψ s g x) *
    (compactWaveletAction ψ s b x * compactWaveletAction φ s f x)

def compactWaveletParaproductPair (ψ φ : SchwartzMap Space ℂ) (t : ℝ) (J : Finset ℕ)
    (b : Space → ℂ) (f g : SchwartzMap Space ℂ) : ℂ :=
  ∑ j ∈ J, compactWaveletParaproductTerm ψ φ (compactWaveletScale t j) b f g

private theorem toLp_sq_eq_integral {f : Space → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 := by
  rw [l2_norm_sq_integral]
  exact integral_congr_ae ((MemLp.coeFn_toLp hf).fun_comp (fun z : ℂ => ‖z‖^2))

private theorem complex_l2_pair_le {f g : Space → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖∫ x, conj (g x)*f x‖ ≤ ‖hf.toLp f‖*‖hg.toLp g‖ := by
  have h : (∫ x, conj (g x)*f x) = inner ℂ (hg.toLp g) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf,MemLp.coeFn_toLp hg] with x hx hy
    rw [RCLike.inner_apply', hx,hy]
  rw [h,mul_comm]
  exact norm_inner_le_norm _ _

/-- The sum of the absolute pairings of the actual compact-base T(1)
paraproduct is uniformly bounded on the original pair of L² inputs. -/
theorem exists_compactBase_commutatorConstant_paraproduct_abs_sum_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (ψ φ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0) (hφ : ∀ z, 1<‖z‖ → φ z = 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r f g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) → ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ),
        (∑ j ∈ J, ‖compactWaveletParaproductTerm ψ φ (compactWaveletScale t j)
          (coefficientCommutatorConstant a r) f g‖) ≤
          C*(U+(L:ℝ))*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  obtain ⟨A,hA,hWeighted⟩ := exists_compactBase_commutatorConstant_weighted_wavelet_square_bound
    ha hBase hCont ψ φ hψ hMean hφ
  obtain ⟨D,hD,hSquare⟩ := exists_compactWaveletAction_square_bound ψ hMean
  let C := Real.sqrt A.toReal * Real.sqrt D
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro r f g L U hU hLip hR t ht J
  let b := coefficientCommutatorConstant a r
  let s := compactWaveletScale t
  let F (j : ℕ) (x : Space) := compactWaveletAction ψ (s j) b x * compactWaveletAction φ (s j) f x
  let G (j : ℕ) := compactWaveletAction ψ (s j) g
  let P := compactAverageBound φ
  let B := SchwartzMap.seminorm ℝ 0 0 f
  have hP : 0≤P := compactAverageBound_nonneg φ
  have hB : 0≤B := apply_nonneg _ _
  have hV : 0≤U+(L:ℝ) := add_nonneg hU L.coe_nonneg
  have hs (j : ℕ) : 0<s j := div_pos ht (pow_pos (by norm_num) _)
  have hb₁ := compactBase_commutatorConstant_integrable ha.frequency hBase hCont r
  have hb₂ := coefficientCommutatorConstant_memLp ha.frequency hBase hCont r
  have hQ := (hSquare t ht J b hb₁ hb₂).1
  obtain ⟨hG,hGSq⟩ := hSquare t ht J g g.integrable (g.memLp 2 volume)
  have hF (j : ℕ) : MemLp (F j) 2 volume := by
    refine (hQ j).of_le_mul (c := P*B) ((hQ j).1.mul
      (compactWaveletAction_continuous φ (s j) (hs j) f f.integrable).aestronglyMeasurable) ?_
    filter_upwards with x
    have hFinite : (maximalSchwartz f x).toReal ≤ B := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (centeredMax_le_const (fun y => ‖f y‖ₑ) (ENNReal.ofReal B) (fun y => by
          change ‖f y‖ₑ ≤ ENNReal.ofReal B
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (SchwartzMap.norm_le_seminorm ℝ f y)) x)
      rw [ENNReal.toReal_ofReal hB] at h
      exact h
    have hLocal := compactWaveletAction_le_local_maximal φ hφ f (s j) (hs j) x x (mem_ball_self (hs j))
    change ‖compactWaveletAction ψ (s j) b x * compactWaveletAction φ (s j) f x‖ ≤
      P*B*‖compactWaveletAction ψ (s j) b x‖
    rw [norm_mul,mul_comm ‖compactWaveletAction ψ (s j) b x‖]
    exact mul_le_mul_of_nonneg_right (hLocal.trans (mul_le_mul_of_nonneg_left hFinite hP)) (norm_nonneg _)
  let W (j : ℕ) := ‖(hF j).toLp (F j)‖
  let Z (j : ℕ) := ‖(hG j).toLp (G j)‖
  have hWSq : (∑ j ∈ J, W j^2) ≤ A.toReal*(U+(L:ℝ))^2*‖f.toLp 2 volume‖^2 := by
    have h := hWeighted r f L U hU hLip hR t ht J
    change (∑ j ∈ J, ∫⁻ x, ‖F j x‖ₑ^(2:ℕ)) ≤ _ at h
    simp_rw [← integral_sq_to_lintegral (hF _),← toLp_sq_eq_integral (hF _)] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
      ← integral_sq_to_lintegral (f.memLp 2 volume),← schwartz_toLp_norm_sq f,
      ← ENNReal.ofReal_pow hV,← ENNReal.ofReal_toReal hA,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hZSq : (∑ j ∈ J, Z j^2) ≤ D*‖g.toLp 2 volume‖^2 := by
    dsimp only [Z]
    simp_rw [toLp_sq_eq_integral]
    simpa only [schwartz_toLp_norm_sq] using hGSq
  have hPair : (∑ j ∈ J, ‖compactWaveletParaproductTerm ψ φ (s j) b f g‖) ≤ ∑ j ∈ J, W j*Z j :=
    Finset.sum_le_sum fun j _ => complex_l2_pair_le (hF j) (hG j)
  have hNonneg : 0 ≤ ∑ j ∈ J, ‖compactWaveletParaproductTerm ψ φ (s j) b f g‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply (sq_le_sq₀ hNonneg (by positivity)).mp
  calc
    _ ≤ (∑ j ∈ J, W j*Z j)^2 := pow_le_pow_left₀ hNonneg hPair 2
    _ ≤ (∑ j ∈ J, W j^2)*(∑ j ∈ J, Z j^2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (A.toReal*(U+(L:ℝ))^2*‖f.toLp 2 volume‖^2)*(D*‖g.toLp 2 volume‖^2) :=
      mul_le_mul hWSq hZSq (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = _ := by
      dsimp only [C]
      simp only [mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg,Real.sq_sqrt hD]
      ring

/-- The finite smooth paraproduct built from the actual compact-base T(1)
is bounded on the original pair of L² inputs, uniformly in the scales. -/
theorem exists_compactBase_commutatorConstant_paraproduct_pair_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (ψ φ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z = 0) (hMean : (∫ z, ψ z) = 0) (hφ : ∀ z, 1<‖z‖ → φ z = 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r f g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) → ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ),
        ‖compactWaveletParaproductPair ψ φ t J (coefficientCommutatorConstant a r) f g‖ ≤
          C*(U+(L:ℝ))*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  obtain ⟨C,hC,hAbs⟩ := exists_compactBase_commutatorConstant_paraproduct_abs_sum_bound ha hBase hCont ψ φ hψ hMean hφ
  refine ⟨C,hC,fun r f g L U hU hLip hR t ht J => ?_⟩
  unfold compactWaveletParaproductPair
  exact (norm_sum_le _ _).trans (hAbs r f g L U hU hLip hR t ht J)

end Burnett.Analysis.CarlesonEmbedding
