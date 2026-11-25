import Burnett.Analysis.TransportPatches.OriginalGlobalDefectNorm

set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 4300000
noncomputable section

namespace Burnett.C02

open MeasureTheory Filter Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau radianFourier radianFourier_scaled)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ComplexConjugate FourierTransform

/-- The Schwartz action of an actual bounded smooth symbol with temperate
derivatives in the same standard Fourier convention as its (L^2) multiplier. -/
def transportSchwartzMultiplier (a : BoundedSymbol E) (ha : Function.HasTemperateGrowth (a : E → ℂ)) :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap.comp
    ((SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ha).comp
      (SchwartzMap.fourierTransformCLE ℂ).toContinuousLinearMap)

theorem transportSchwartzMultiplier_fourier (a : BoundedSymbol E)
    (ha : Function.HasTemperateGrowth (a : E → ℂ)) (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (transportSchwartzMultiplier a ha f : E → ℂ) ξ = a ξ * 𝓕 (f : E → ℂ) ξ := by
  change SchwartzMap.fourierTransformCLE ℂ
    ((SchwartzMap.fourierTransformCLE ℂ).symm
      (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ha
        (SchwartzMap.fourierTransformCLE ℂ f))) ξ = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact mul_comm _ _

theorem transportSchwartzMultiplier_toLp (a : BoundedSymbol E)
    (ha : Function.HasTemperateGrowth (a : E → ℂ)) (f : SchwartzMap E ℂ) :
    (transportSchwartzMultiplier a ha f).toLp 2 volume = fourierMultiplier a (f.toLp 2 volume) := by
  apply fourierL2Equiv.injective
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [fourierL2Equiv_schwartz_ae (transportSchwartzMultiplier a ha f),
    symbolL2_ae a (fourierL2Equiv (f.toLp 2 volume)), fourierL2Equiv_schwartz_ae f] with ξ hOut hM hIn
  rw [hOut, transportSchwartzMultiplier_fourier, hM, hIn]

theorem transportSchwartzMultiplier_coordinateDerivative (a : BoundedSymbol E)
    (ha : Function.HasTemperateGrowth (a : E → ℂ)) (f : SchwartzMap E ℂ) (d : Fin 4) :
    coordinateDerivative d (transportSchwartzMultiplier a ha f) =
      transportSchwartzMultiplier a ha (coordinateDerivative d f) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ξ
  change 𝓕 (coordinateDerivative d (transportSchwartzMultiplier a ha f) : E → ℂ) ξ =
    𝓕 (transportSchwartzMultiplier a ha (coordinateDerivative d f) : E → ℂ) ξ
  have derivative (w : SchwartzMap E ℂ) :
      𝓕 (coordinateDerivative d w : E → ℂ) ξ = Complex.I * (((tau • ξ) d : ℝ) : ℂ) * 𝓕 (w : E → ℂ) ξ := by
    rw [← radianFourier_scaled, ← radianFourier_scaled, radianFourier_coordinateDerivative]
  rw [derivative, transportSchwartzMultiplier_fourier, transportSchwartzMultiplier_fourier, derivative]
  ring

private theorem realFourier_reflection (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : E) :
    conj (𝓕 (f : E → ℂ) ξ) = 𝓕 (f : E → ℂ) (-ξ) := by
  have h := fourier_conj_eq_conj_inverse (f : E → ℂ) (-ξ)
  rw [show (fun x => conj (f x)) = (f : E → ℂ) from funext hf] at h
  rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, neg_neg] at h
  exact h.symm

/-- A real, even symbol preserves the pointwise real Schwartz fields used in
the complete physical cubic form. -/
theorem transportSchwartzMultiplier_real (a : BoundedSymbol E)
    (ha : Function.HasTemperateGrowth (a : E → ℂ))
    (hSym : ∀ ξ, conj (a ξ) = a (-ξ)) (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x)
    (x : E) : conj (transportSchwartzMultiplier a ha f x) = transportSchwartzMultiplier a ha f x := by
  let w := transportSchwartzMultiplier a ha f
  let W : E → ℂ := 𝓕 (w : E → ℂ)
  have hW : (fun ξ => conj (W ξ)) = (fun ξ => W (-ξ)) := by
    funext ξ
    dsimp only [W, w]
    rw [transportSchwartzMultiplier_fourier, transportSchwartzMultiplier_fourier, map_mul, hSym,
      realFourier_reflection f hf]
  have hinv : 𝓕⁻ W = (w : E → ℂ) :=
    w.continuous.fourier_inversion w.integrable (SchwartzMap.fourierTransformCLM ℂ w).integrable
  change conj (w x) = w x
  rw [← hinv]
  rw [← fourier_conj_eq_conj_inverse, hW, ← Real.fourierIntegralInv_eq_fourierIntegral_comp_neg]

variable {J : Type*}

/-- Actual ordered matrix multiplier acting on the original matrix Schwartz
input. All rows contain the exterior support of the inverse Fourier output. -/
def ClassicalMatrixMultiplier.schwartzOutput (T : ClassicalMatrixMultiplier J)
    (hT : ∀ k i, Function.HasTemperateGrowth (T.full k i : E → ℂ))
    (z : ProjectionSchwartzMatrix) (k : J) : SchwartzMap E ℂ :=
  ∑ i : OrderedPair, transportSchwartzMultiplier (T.full k i) (hT k i) (z i.1 i.2)

theorem ClassicalMatrixMultiplier.schwartzOutput_toLp (T : ClassicalMatrixMultiplier J)
    (hT : ∀ k i, Function.HasTemperateGrowth (T.full k i : E → ℂ))
    (z : ProjectionSchwartzMatrix) (k : J) :
    (T.schwartzOutput hT z k).toLp 2 volume =
      T.output (fun i => (z i.1 i.2).toLp 2 volume) k := by
  change SchwartzMap.toLpCLM ℂ ℂ 2 volume
    (∑ i : OrderedPair, transportSchwartzMultiplier (T.full k i) (hT k i) (z i.1 i.2)) = _
  rw [map_sum, ClassicalMatrixMultiplier.output]
  simp only [SchwartzMap.toLpCLM_apply, transportSchwartzMultiplier_toLp]

theorem ClassicalMatrixMultiplier.schwartzOutput_coordinateDerivative (T : ClassicalMatrixMultiplier J)
    (hT : ∀ k i, Function.HasTemperateGrowth (T.full k i : E → ℂ))
    (z : ProjectionSchwartzMatrix) (d : Fin 4) (k : J) :
    (coordinateDerivative d (T.schwartzOutput hT z k)).toLp 2 volume =
      multiplierCoordinateDerivative T z d k := by
  rw [ClassicalMatrixMultiplier.schwartzOutput, map_sum]
  simp_rw [transportSchwartzMultiplier_coordinateDerivative]
  exact T.schwartzOutput_toLp hT (fun i j => coordinateDerivative d (z i j)) k

theorem ClassicalMatrixMultiplier.schwartzOutput_real (T : ClassicalMatrixMultiplier J)
    (hT : ∀ k i, Function.HasTemperateGrowth (T.full k i : E → ℂ))
    (hSym : ∀ k i ξ, conj (T.full k i ξ) = T.full k i (-ξ))
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) (k : J) (x : E) :
    conj (T.schwartzOutput hT z k x) = T.schwartzOutput hT z k x := by
  let eval : SchwartzMap E ℂ →+ ℂ :=
    { toFun := fun f => f x
      map_zero' := by simp only [SchwartzMap.zero_apply]
      map_add' := fun _ _ => by simp only [SchwartzMap.add_apply] }
  change conj (eval (∑ i : OrderedPair, transportSchwartzMultiplier (T.full k i) (hT k i) (z i.1 i.2))) =
    eval (∑ i : OrderedPair, transportSchwartzMultiplier (T.full k i) (hT k i) (z i.1 i.2))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact transportSchwartzMultiplier_real _ _ (hSym k i) _ (hz i.1 i.2) x

end Burnett.C02
