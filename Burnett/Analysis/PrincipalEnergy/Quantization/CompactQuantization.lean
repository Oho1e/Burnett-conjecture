import Burnett.Analysis.PrincipalEnergy.Quantization.CompactFrequencyL2
import Burnett.Analysis.PrincipalEnergy.Quantization.WeightedFourier

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Function MeasureTheory Filter Burnett.Fourier Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.AngularCommutator (fourierL2Equiv_symm_eq_inverse_ae_of_integrable)
open Burnett.Microlocal.HminusReverse
open scoped FourierTransform ENNReal

private def recoveryPhase (x η : E) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * inner ℝ η x) : ℂ) * Complex.I)

private theorem recoveryPhase_norm (x η : E) : ‖recoveryPhase x η‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem recoveryPhase_continuous (x : E) : Continuous (recoveryPhase x) := by
  unfold recoveryPhase
  fun_prop

private theorem recoveryPhase_add (x η ξ : E) :
    recoveryPhase x (η+ξ) = recoveryPhase x η * recoveryPhase x ξ := by
  unfold recoveryPhase
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_left]
  push_cast
  ring

private theorem normalizedSymbol_mul_weighted (a : E → E → ℂ) (f : SchwartzMap E ℂ) (x ξ : E) :
    normalizedBaseSymbol a x ξ * firstOrderWeightedFourier f ξ = a x ξ * (𝓕 (f : E → ℂ)) ξ := by
  let W := 1 + ‖ξ‖
  have hW : W ≠ 0 := by dsimp [W]; positivity
  change (W⁻¹ • a x ξ) * (W • (𝓕 (f : E → ℂ)) ξ) = _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hW, one_smul]

/-- The exact Bochner frequency action recovers the full physical left
quantization by inverse Fourier transform on every actual Schwartz test. -/
theorem firstOrderAction_eq_frequencyInverse {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hs : Continuous (uncurry a))
    (f : SchwartzMap E ℂ) (x : E) :
    firstOrderAction a f x =
      (𝓕⁻ (compactFrequencyAction a (firstOrderWeightedFourier f))) x := by
  obtain ⟨C,_,hEnv,hDom⟩ := normalizedBaseFourier_dominated ha
  let V : Measure E := volume
  let P := V.prod V
  let w := firstOrderWeightedFourier f
  let p := normalizedBaseFourier a
  let G (q : E × E) := recoveryPhase x q.1 * (p (q.1-q.2) q.2 * w q.2)
  let S (q : E × E) : E × E := (q.1-q.2,q.2)
  let T (q : E × E) : E × E := (q.1+q.2,q.2)
  let env (k : E) := C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹
  have hS : MeasurePreserving S P P := measurePreserving_sub_prod V V
  have hT : MeasurePreserving T P P := measurePreserving_add_prod V V
  have hScont : Continuous S := (continuous_fst.sub continuous_snd).prodMk continuous_snd
  have hG : Continuous G := by
    have hp := (normalizedBaseFourier_joint_continuous ha hs).comp hScont
    exact ((recoveryPhase_continuous x).comp continuous_fst).mul
      (hp.mul ((firstOrderWeightedFourier_continuous f).comp continuous_snd))
  have hM : Integrable (fun q : E × E => env q.1 * ‖w q.2‖) P :=
    hEnv.mul_prod (firstOrderWeightedFourier_integrable f).norm
  have hMA : Integrable (fun q : E × E => env q.1 * ‖w q.2‖) (Measure.map S P) := by
    rw [hS.map_eq]
    exact hM
  have hI : Integrable G P := by
    have hMS := (integrable_map_measure hMA.aestronglyMeasurable hS.measurable.aemeasurable).mp hMA
    refine hMS.mono' hG.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    change ‖recoveryPhase x q.1 * (p (q.1-q.2) q.2 * w q.2)‖ ≤ _
    rw [norm_mul, recoveryPhase_norm, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hDom (q.1-q.2) q.2) (norm_nonneg _)
  have hIT : Integrable (G ∘ T) P := by
    have hIA : Integrable G (Measure.map T P) := by rw [hT.map_eq]; exact hI
    exact (integrable_map_measure hIA.aestronglyMeasurable hT.measurable.aemeasurable).mp hIA
  have hReconstruct (ξ : E) :
      (∫ k, recoveryPhase x k * p k ξ) = normalizedBaseSymbol a x ξ := by
    simpa only [Real.fourierIntegralInv_eq', recoveryPhase, smul_eq_mul] using
      normalizedBaseFourier_inverse ha x ξ
  have hFubini : (∫ η, recoveryPhase x η * compactFrequencyAction a w η) =
      ∫ ξ, recoveryPhase x ξ * (a x ξ * (𝓕 (f : E → ℂ)) ξ) := by
    calc
      _ = ∫ q, G q ∂P := by
        rw [integral_prod G hI]
        apply integral_congr_ae
        filter_upwards with η
        simp only [G, V, compactFrequencyAction, compactFrequencyKernel, p, ← integral_const_mul]
      _ = ∫ q, (G ∘ T) q ∂P := by
        have hGm : AEStronglyMeasurable G (Measure.map T P) := by
          rw [hT.map_eq]
          exact hG.aestronglyMeasurable
        change (∫ q, G q ∂P) = ∫ q, G (T q) ∂P
        rw [← integral_map hT.measurable.aemeasurable hGm, hT.map_eq]
      _ = _ := by
        rw [integral_prod_symm _ hIT]
        apply integral_congr_ae
        filter_upwards with ξ
        have point (k : E) :
            (G ∘ T) (k,ξ) = recoveryPhase x ξ * ((recoveryPhase x k * p k ξ) * w ξ) := by
          dsimp only [Function.comp_apply, G, T]
          rw [add_sub_cancel_right, recoveryPhase_add]
          ring
        simp_rw [point]
        rw [integral_const_mul, integral_mul_const, hReconstruct,
          normalizedSymbol_mul_weighted]
  rw [firstOrderAction, Real.fourierIntegralInv_eq', Real.fourierIntegralInv_eq']
  exact hFubini.symm

/-- Compact-base scalar (H^1\to L^2) for the actual full left quantization
on Schwartz tests, with the genuine four-direction Sobolev energy. -/
theorem exists_compactBase_firstOrderAction_h1_to_l2 {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hs : Continuous (uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap E ℂ,
      ∃ hB : MemLp (firstOrderAction a f) 2 (volume : Measure E),
        ‖hB.toLp (firstOrderAction a f)‖ ^ 2 ≤ C ^ 2 * schwartzH1Energy f := by
  obtain ⟨C,hC,hEnv,hDom⟩ := normalizedBaseFourier_dominated ha
  let D := ∫ k : E, C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹
  have hD : 0 ≤ D := integral_nonneg (fun _ => by positivity)
  refine ⟨Real.sqrt 2 * D, mul_nonneg (Real.sqrt_nonneg _) hD, ?_⟩
  intro f
  let w := firstOrderWeightedFourier f
  let g := compactFrequencyAction a w
  have hw₂ := firstOrderWeightedFourier_memLp f
  obtain ⟨hG₁,hG₂,hBound⟩ := compactFrequencyAction_integrable_and_norm_le ha hs C hC.le
    hEnv hDom w (firstOrderWeightedFourier_continuous f).measurable
    (firstOrderWeightedFourier_integrable f) hw₂
  have hInv := fourierL2Equiv_symm_eq_inverse_ae_of_integrable g hG₁ hG₂
  let q := fourierL2Equiv.symm (hG₂.toLp g)
  have hEq : (q : E → ℂ) =ᵐ[volume] firstOrderAction a f := by
    filter_upwards [hInv] with x hx
    exact hx.trans (firstOrderAction_eq_frequencyInverse ha hs f x).symm
  have hB : MemLp (firstOrderAction a f) 2 volume := (Lp.memLp q).ae_eq hEq
  have hB_eq : hB.toLp (firstOrderAction a f) = q := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hB).trans hEq.symm
  refine ⟨hB,?_⟩
  rw [hB_eq, show ‖q‖ = ‖hG₂.toLp g‖ from LinearIsometryEquiv.norm_map ..]
  calc
    _ ≤ (D * ‖hw₂.toLp w‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hBound
    _ = D^2 * ‖hw₂.toLp w‖^2 := by ring
    _ ≤ D^2 * (2 * schwartzH1Energy f) :=
      mul_le_mul_of_nonneg_left (firstOrderWeightedFourier_h1_bound f) (sq_nonneg _)
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]; ring

end Burnett.Analysis.FirstOrderDyadic
