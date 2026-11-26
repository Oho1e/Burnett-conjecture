import Burnett.Analysis.TransportPatches.ActualPatchPhysicalGaugeLp

set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.V08

open Matrix Burnett.P01
open Burnett.A02.FrequencySplit (E radianFourier)
open scoped BigOperators Matrix

open private complexFrequency complexDirectionProjection from
  Burnett.Analysis.GaugeProjection.GaugeProjectionFourier
open private directionProjectionEntry_ratio from
  Burnett.Analysis.GaugeProjection.GaugeProjectionSymbol

/-- The normalized low gauge potential `|p| v` on a unit direction.
The formula is polynomial in all direction and tensor coordinates. -/
def normalizedGaugePotential (ω : E) (G : ComplexComponents) : ComplexCovector :=
  let w := complexFrequency ω
  let v := G *ᵥ w
  v - ((w ⬝ᵥ v) / 2) • w

/-- Symmetrized tensor amplitude in the unit low direction. -/
def normalizedGaugeAmplitude (ω : E) (v : ComplexCovector) : ComplexComponents :=
  vecMulVec (complexFrequency ω) v + vecMulVec v (complexFrequency ω)

private theorem complexDirectionProjection_unit (ω : E) (hω : ‖ω‖ = 1) :
    complexDirectionProjection ω = 1 - vecMulVec (complexFrequency ω) (complexFrequency ω) := by
  ext a b
  change (directionProjectionEntry a b ω : ℂ) = _
  rw [directionProjectionEntry_ratio, hω]
  simp only [one_pow, div_one, Complex.ofReal_sub, Complex.ofReal_mul, Matrix.sub_apply,
    vecMulVec_apply, complexFrequency, Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

/-- The actual complement of the two transverse projections is a pure
gauge amplitude for the original complex symmetric Fourier tensor. -/
theorem uncutGaugeComplement_eq_normalizedAmplitude (ω : E) (hω : ‖ω‖ = 1)
    (H : ComplexComponents) (hH : Hᵀ = H) :
    H - complexDirectionProjection ω * H * complexDirectionProjection ω =
      normalizedGaugeAmplitude ω (normalizedGaugePotential ω H) := by
  let w := complexFrequency ω
  have hv : w ᵥ* H = H *ᵥ w := by rw [← mulVec_transpose, hH]
  rw [complexDirectionProjection_unit ω hω]
  change H - (1 - vecMulVec w w) * H * (1 - vecMulVec w w) =
    vecMulVec w (H *ᵥ w - ((w ⬝ᵥ (H *ᵥ w)) / 2) • w) +
      vecMulVec (H *ᵥ w - ((w ⬝ᵥ (H *ᵥ w)) / 2) • w) w
  simp only [sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul, mul_vecMulVec, hv,
    vecMulVec_mulVec, op_smul_eq_smul]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, vecMulVec_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, dotProduct_comm (H *ᵥ w) w]
  ring

private theorem uncutComplexGaugeProjection_apply (ξ : E) (H : ComplexComponents) (i j : Fin 4) :
    (complexDirectionProjection ξ * H * complexDirectionProjection ξ) i j =
      ∑ a : Fin 4, ∑ b : Fin 4, (gaugeProjectionSymbol i j a b ξ : ℂ) * H a b := by
  simp only [complexDirectionProjection, gaugeProjectionSymbol, directionProjectionEntry, Matrix.mul_apply,
    Matrix.map_apply, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- On the actual global infrared-cut complement, the exact low gauge
amplitude at a nonzero frequency is represented by its unit direction. -/
theorem projectedGaugeComplement_eq_normalizedGauge
    (z : ProjectionSchwartzMatrix) (hSym : ∀ i j, z i j = z j i)
    (ξ : E) (hξ : ξ ≠ 0) (i j : Fin 4) :
    let ω := ‖ξ‖⁻¹ • ξ
    let H : ComplexComponents := fun a b => radianFourier (z a b) ξ
    radianFourier (Burnett.C03.projectedGaugeComplement z i j) ξ =
      (gaugeProjectionInfrared ‖ξ‖ : ℂ) * normalizedGaugeAmplitude ω (normalizedGaugePotential ω H) i j := by
  dsimp only
  let ω := ‖ξ‖⁻¹ • ξ
  let H : ComplexComponents := fun a b => radianFourier (z a b) ξ
  have hLen : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hω : ‖ω‖ = 1 := by
    change ‖‖ξ‖⁻¹ • ξ‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hLen.le), inv_mul_cancel₀ hLen.ne']
  have hH : Hᵀ = H := by
    ext a b
    change radianFourier (z b a) ξ = radianFourier (z a b) ξ
    rw [hSym b a]
  rw [Burnett.C03.projectedGaugeComplement_radianFourier, ← uncutGaugeComplement_eq_normalizedAmplitude ω hω H hH]
  congr 1
  change H i j - (∑ a : Fin 4, ∑ b : Fin 4, (gaugeProjectionSymbol i j a b ξ : ℂ) * H a b) =
    H i j - (complexDirectionProjection ω * H * complexDirectionProjection ω) i j
  rw [uncutComplexGaugeProjection_apply]
  simp only [ω, gaugeProjectionSymbol_scale _ _ _ _ _ (inv_pos.mpr hLen)]

end Burnett.V08
