import Burnett.Analysis.Fourier.Projection

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Filter Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def sharpSymbol (S : Set V) (hS : MeasurableSet S) : BoundedSymbol V where
  toFun := S.indicator (fun _ => 1)
  measurable := aestronglyMeasurable_const.indicator hS
  bound := 1
  bound_nonneg := zero_le_one
  norm_le ξ := by
    by_cases hx : ξ ∈ S <;> simp [hx]

theorem sharpSymbol_apply_mem {S : Set V} (hS : MeasurableSet S) {ξ : V} (hξ : ξ ∈ S) :
    sharpSymbol S hS ξ = 1 := by
  exact Set.indicator_of_mem hξ (fun _ => (1 : ℂ))

theorem sharpSymbol_apply_notMem {S : Set V} (hS : MeasurableSet S) {ξ : V} (hξ : ξ ∉ S) :
    sharpSymbol S hS ξ = 0 := by
  exact Set.indicator_of_notMem hξ (fun _ => (1 : ℂ))

theorem sharp_spectral_idempotent {S : Set V} (hS : MeasurableSet S) (u : ComplexL2 V) :
    symbolL2 (sharpSymbol S hS) (symbolL2 (sharpSymbol S hS) u) =
      symbolL2 (sharpSymbol S hS) u := by
  apply Lp.ext
  filter_upwards [symbolL2_ae (sharpSymbol S hS) (symbolL2 (sharpSymbol S hS) u),
    symbolL2_ae (sharpSymbol S hS) u] with ξ hn hu
  rw [hn, hu]
  by_cases hx : ξ ∈ S
  · rw [sharpSymbol_apply_mem hS hx, one_mul, one_mul]
  · rw [sharpSymbol_apply_notMem hS hx, zero_mul, zero_mul]

theorem sharp_spectral_orthogonal {S : Set V} (hS : MeasurableSet S) (u v : ComplexL2 V) :
    inner ℂ (u - symbolL2 (sharpSymbol S hS) u) (symbolL2 (sharpSymbol S hS) v) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub u (symbolL2 (sharpSymbol S hS) u),
    symbolL2_ae (sharpSymbol S hS) u, symbolL2_ae (sharpSymbol S hS) v] with ξ hsub hu hv
  rw [hsub]
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [hu, hv]
  change inner ℂ (u ξ - sharpSymbol S hS ξ * u ξ) (sharpSymbol S hS ξ * v ξ) = 0
  by_cases hx : ξ ∈ S
  · simp [sharpSymbol_apply_mem hS hx]
  · simp [sharpSymbol_apply_notMem hS hx]

/-- A genuine sharp orthogonal Fourier projection on the complete L²
space, defined by the characteristic symbol in frequency space. -/
def sharpFourierProjection (S : Set V) (hS : MeasurableSet S) :
    ComplexL2 V →L[ℂ] ComplexL2 V := fourierMultiplier (sharpSymbol S hS)

theorem sharpFourierProjection_idempotent {S : Set V} (hS : MeasurableSet S) (u : ComplexL2 V) :
    sharpFourierProjection S hS (sharpFourierProjection S hS u) = sharpFourierProjection S hS u := by
  apply (fourierL2Equiv (V := V)).injective
  change fourierL2Equiv (fourierMultiplier _ (fourierMultiplier _ u)) =
    fourierL2Equiv (fourierMultiplier _ u)
  rw [fourier_fourierMultiplier, fourier_fourierMultiplier, sharp_spectral_idempotent]

theorem sharpFourierProjection_orthogonal {S : Set V} (hS : MeasurableSet S) (u v : ComplexL2 V) :
    inner ℂ (u - sharpFourierProjection S hS u) (sharpFourierProjection S hS v) = 0 := by
  calc
    _ = inner ℂ (fourierL2Equiv (u - sharpFourierProjection S hS u))
        (fourierL2Equiv (sharpFourierProjection S hS v)) :=
      (fourierL2Equiv.inner_map_map _ _).symm
    _ = 0 := by
      change inner ℂ (fourierL2Equiv (u - fourierMultiplier _ u))
        (fourierL2Equiv (fourierMultiplier _ v)) = 0
      rw [map_sub, fourier_fourierMultiplier, fourier_fourierMultiplier]
      exact sharp_spectral_orthogonal hS _ _

theorem symbolL2_congr_ae (m n : BoundedSymbol V) (h : (m : V → ℂ) =ᵐ[volume] n)
    (u : ComplexL2 V) : symbolL2 m u = symbolL2 n u := by
  apply Lp.ext
  filter_upwards [symbolL2_ae m u, symbolL2_ae n u, h] with ξ hm hn hmn
  rw [hm, hn, hmn]

theorem fourierMultiplier_congr_ae (m n : BoundedSymbol V)
    (h : (m : V → ℂ) =ᵐ[volume] n) : fourierMultiplier m = fourierMultiplier n := by
  ext u
  rw [fourierMultiplier_apply, fourierMultiplier_apply, symbolL2_congr_ae m n h]

end Burnett.Fourier
