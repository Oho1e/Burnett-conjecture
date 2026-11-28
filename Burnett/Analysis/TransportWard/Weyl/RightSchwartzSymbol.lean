import Burnett.Analysis.TransportWard.Weyl.FrozenScalarCommutator
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichFrequency

/-! Exact right multiplication on the same physical left Fourier action. -/

set_option autoImplicit false
set_option maxHeartbeats 6900000
set_option maxRecDepth 4700

noncomputable section

namespace Burnett.V03

open Function MeasureTheory Filter Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped FourierTransform ContDiff RealInnerProductSpace

open private fourier_scalarSchwartzProduct
  from Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichSymbol

/-- The actual inverse-Fourier factor of the coefficient, with cycles in
the integration variable. -/
def coefficientFourierFactor (c : SchwartzMap E ℂ) (x η : E) : ℂ :=
  patchFourierPhase η x * 𝓕 (c : E → ℂ) η

private theorem continuous_coefficientPhase (x : E) : Continuous (fun η : E => patchFourierPhase η x) := by
  have hEq : (fun η : E => patchFourierPhase η x) = patchFourierPhase x := by
    funext η
    simp only [Burnett.Microlocal.Overlap.baseFourierPhase, real_inner_comm η x]
  rw [hEq]
  exact (radian_base_phase_smooth x).continuous

theorem coefficientFourierFactor_continuous (c : SchwartzMap E ℂ) (x : E) :
    Continuous (coefficientFourierFactor c x) :=
  (continuous_coefficientPhase x).mul (SchwartzMap.fourierTransformCLM ℂ c).continuous

/-- The exact left symbol for multiplication by the specified Schwartz
coefficient on the input side. -/
def rightSchwartzSymbol (a : E → E → ℂ) (c : SchwartzMap E ℂ) (x ξ : E) : ℂ :=
  ∫ η, coefficientFourierFactor c x η * a x (ξ + η)

theorem firstOrderAction_rightSchwartzSymbol {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (c u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (rightSchwartzSymbol a c) u x =
      firstOrderAction a (scalarSchwartzProduct c u) x ∧
    Integrable (leftActionIntegrand (rightSchwartzSymbol a c) u x) volume := by
  let V : Measure E := volume
  let P (η : E) := patchFourierPhase η x
  let U := SchwartzMap.fourierTransformCLM ℂ c
  let F := SchwartzMap.fourierTransformCLM ℂ u
  let A (ζ ξ : E) : ℂ := P ζ * (a x ζ * (U (ζ-ξ)*F ξ))
  have hP (v : E) : ‖P v‖ = 1 := patch_fourier_phase_norm _ _
  have hPadd (v w : E) : P (v+w) = P v * P w := patch_fourier_phase_add v w x
  have hPM : Continuous P := continuous_coefficientPhase x
  have hAc : Continuous (uncurry A) :=
    (hPM.comp continuous_fst).mul (((ha.smooth x).continuous.comp continuous_fst).mul
      ((U.continuous.comp (continuous_fst.sub continuous_snd)).mul (F.continuous.comp continuous_snd)))
  let S (p : E × E) := (p.1+p.2,p.2)
  have hS : MeasurePreserving S (V.prod V) (V.prod V) := measurePreserving_add_prod V V
  obtain ⟨C,hC,hFreq⟩ := ha.order 0
  have hGrowth (ξ : E) : ‖a x ξ‖ ≤ C*(1+‖ξ‖) := by
    simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hFreq x ξ
  have hB : Integrable ((uncurry A) ∘ S) (V.prod V) := by
    refine (((integrable_schwartz_weighted U 1).mul_prod (integrable_schwartz_weighted F 1)).const_mul C).mono'
      (hAc.comp ((continuous_fst.add continuous_snd).prodMk continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    change ‖A (p.1+p.2) p.2‖ ≤ C*(((1+‖p.1‖)^1*‖U p.1‖)*((1+‖p.2‖)^1*‖F p.2‖))
    have hW : 1+‖p.1+p.2‖ ≤ (1+‖p.1‖)*(1+‖p.2‖) := by
      nlinarith only [norm_add_le p.1 p.2,mul_nonneg (norm_nonneg p.1) (norm_nonneg p.2)]
    simp only [A,add_sub_cancel_right,norm_mul,hP,one_mul,pow_one]
    calc
      _ ≤ (C*((1+‖p.1‖)*(1+‖p.2‖)))*(‖U p.1‖*‖F p.2‖) :=
        mul_le_mul_of_nonneg_right ((hGrowth _).trans (mul_le_mul_of_nonneg_left hW hC))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have hA : Integrable (uncurry A) (V.prod V) := (hS.integrable_comp hAc.aestronglyMeasurable).mp hB
  have hMove : (∫ p, A (p.1+p.2) p.2 ∂(V.prod V)) = ∫ p, A p.1 p.2 ∂(V.prod V) := by
    change (∫ p, uncurry A (S p) ∂(V.prod V)) = _
    rw [← integral_map (f := uncurry A) hS.measurable.aemeasurable
      (by rw [hS.map_eq]; exact hAc.aestronglyMeasurable),hS.map_eq]
    rfl
  have hLeft (ξ : E) : leftActionIntegrand (rightSchwartzSymbol a c) u x ξ = ∫ η, A (η+ξ) ξ := by
    change P ξ * (∫ η, P η * (𝓕 (c : E → ℂ)) η * a x (ξ+η)) * (𝓕 (u : E → ℂ)) ξ = _
    change P ξ * (∫ η, P η * U η * a x (ξ+η)) * F ξ = _
    calc
      _ = (P ξ * F ξ) * (∫ η, P η * U η * a x (ξ+η)) := by ring
      _ = ∫ η, (P ξ * F ξ) * (P η * U η * a x (ξ+η)) := (integral_const_mul _ _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with η
        simp only [A,hPadd,add_sub_cancel_right,add_comm ξ η]
        ring
  refine ⟨?_,hB.integral_prod_right.congr (Eventually.of_forall fun ξ => (hLeft ξ).symm)⟩
  calc
    _ = ∫ ξ, ∫ η, A (η+ξ) ξ := by rw [firstOrderAction_eq_leftActionIntegrand]; simp only [hLeft]
    _ = ∫ p, A (p.1+p.2) p.2 ∂(V.prod V) := (integral_prod_symm _ hB).symm
    _ = ∫ p, A p.1 p.2 ∂(V.prod V) := hMove
    _ = ∫ ζ, ∫ ξ, A ζ ξ := (integral_integral hA).symm
    _ = _ := by
      rw [firstOrderAction_eq_leftActionIntegrand]
      apply integral_congr_ae
      filter_upwards with ζ
      simp only [leftActionIntegrand,fourier_scalarSchwartzProduct]
      change (∫ ξ, A ζ ξ) = P ζ * a x ζ * (∫ ξ, U (ζ-ξ)*F ξ)
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [A]
      ring

theorem coefficientFourier_zeroMoment (c : SchwartzMap E ℂ) (x : E) :
    (∫ η, coefficientFourierFactor c x η) = c x := by
  let U := SchwartzMap.fourierTransformCLM ℂ c
  have h := congrFun (c.continuous.fourier_inversion c.integrable U.integrable) x
  simpa only [U, SchwartzMap.fourierTransformCLM_apply, Real.fourierIntegralInv_eq',
    coefficientFourierFactor, Burnett.Microlocal.Overlap.baseFourierPhase, tau, smul_eq_mul] using h

theorem coefficientFourier_firstMoment (c : SchwartzMap E ℂ) (k : Fin 4) (x : E) :
    Complex.I * (∫ η, coefficientFourierFactor c x η * (η k : ℂ)) =
      (tau : ℂ)⁻¹ * (frozenSchwartzCoordinatePartial k c) x := by
  have hp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hn : (tau : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let d := frozenSchwartzCoordinatePartial k c
  have hfour (η : E) : 𝓕 (d : E → ℂ) η = Complex.I * ((tau : ℂ) * (η k : ℂ)) * 𝓕 (c : E → ℂ) η := by
    change 𝓕 ((frozenSchwartzCoordinatePartial k c : SchwartzMap E ℂ) : E → ℂ) η = _
    rw [frozenSchwartzCoordinatePartial, Burnett.Analysis.HminusWeightedDual.fourier_pderiv,
      coordinateDirection, EuclideanSpace.inner_single_right]
    simp only [one_mul, conj_trivial, tau]
    push_cast
    ring
  have hMoment : (∫ η, coefficientFourierFactor d x η) =
      (tau : ℂ) * (Complex.I * (∫ η, coefficientFourierFactor c x η * (η k : ℂ))) := by
    rw [← mul_assoc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with η
    simp only [coefficientFourierFactor, hfour]
    ring
  rw [coefficientFourier_zeroMoment] at hMoment
  change _ = (tau : ℂ)⁻¹ * d x
  rw [hMoment, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end Burnett.V03
