import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
import Burnett.Analysis.AngularCaps.FarAngularPhase

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V04

open Burnett.V03 Burnett.Analysis.TransportWardSymbol Burnett.Analysis.ProjectiveNullCaps
open scoped BigOperators ContDiff ComplexConjugate Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι]

/-- Complexification of the derivative of the actual Gamma--Gamma coefficient. -/
def densityCoefficientDirection (S : ι → Mat) (G : Mat) (s t : ActionSlot ι) (H : ι → ℂ) : ℂ :=
  ∑ k, (fderiv ℝ (metricActionCoefficient S s t) G (S k) : ℂ) * H k

theorem densityCoefficientDirection_ofReal (S : ι → Mat) (G : Mat) (s t : ActionSlot ι)
    (H : ι → ℝ) :
    densityCoefficientDirection S G s t (fun k => (H k : ℂ)) =
      (fderiv ℝ (metricActionCoefficient S s t) G (assembleMetricComponents S H) : ℂ) := by
  rw [assembleMetricComponents_apply, map_sum]
  push_cast
  simp only [densityCoefficientDirection, map_smul, smul_eq_mul, Complex.ofReal_mul, mul_comm]

theorem hasDerivAt_metricActionCoefficient_direction (S : ι → Mat) (G : Mat)
    (hG : G ∈ nonsingularMetricDomain) (s t : ActionSlot ι) (H : ι → ℝ) :
    HasDerivAt (fun ε : ℝ => metricActionCoefficient S s t (G + ε • assembleMetricComponents S H))
      (densityCoefficientDirection S G s t (fun k => (H k : ℂ))).re 0 := by
  have hSmooth := (contDiffOn_metricActionCoefficient S s t).contDiffAt
    (isOpen_nonsingularMetricDomain.mem_nhds hG)
  have hC₁ : ContDiffAt ℝ 1 (metricActionCoefficient S s t) G := by
    simpa only [Nat.cast_one] using contDiffAt_infty.mp hSmooth 1
  have hC := hC₁.differentiableAt le_rfl
  have hPath : HasDerivAt (fun ε : ℝ => G + ε • assembleMetricComponents S H)
      (assembleMetricComponents S H) 0 := by
    simpa only [one_smul, zero_add] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (assembleMetricComponents S H)).const_add G)
  rw [densityCoefficientDirection_ofReal, Complex.ofReal_re]
  have hMetric : HasFDerivAt (metricActionCoefficient S s t)
      (fderiv ℝ (metricActionCoefficient S s t) G) (G + (0 : ℝ) • assembleMetricComponents S H) := by
    simpa only [zero_smul, add_zero] using hC.hasFDerivAt
  exact hMetric.comp_hasDerivAt 0 hPath

/-- The term with the undifferentiated metric in the first slot. -/
def frozenDensityCubicTerm (S : ι → Mat) (G : Mat) (H : ι → ℂ)
    (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) : ℂ :=
  ∑ s : ActionSlot ι, ∑ t : ActionSlot ι,
    densityCoefficientDirection S G s t H * ((q s.1 : ℂ) * J s.2) * ((r t.1 : ℂ) * L t.2)

/-- Signed cyclic sum of the genuine density derivative with two Fourier derivatives. -/
def frozenDensityCubicVertex (S : ι → Mat) (G : Mat)
    (p : Vec) (H : ι → ℂ) (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) : ℂ :=
  -(frozenDensityCubicTerm S G H q J r L +
    frozenDensityCubicTerm S G J r L p H +
    frozenDensityCubicTerm S G L p H q J)

theorem frozenDensityCubicTerm_swap (S : ι → Mat) (G : Mat) (H : ι → ℂ)
    (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) :
    frozenDensityCubicTerm S G H q J r L = frozenDensityCubicTerm S G H r L q J := by
  unfold frozenDensityCubicTerm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [densityCoefficientDirection, metricActionCoefficient_swap S t s]
  ring

theorem frozenDensityCubicVertex_highSwap (S : ι → Mat) (G : Mat)
    (p : Vec) (H : ι → ℂ) (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) :
    frozenDensityCubicVertex S G p H q J r L = frozenDensityCubicVertex S G p H r L q J := by
  unfold frozenDensityCubicVertex
  rw [frozenDensityCubicTerm_swap S G H r L q J, frozenDensityCubicTerm_swap S G L q J p H,
    frozenDensityCubicTerm_swap S G J p H r L]
  ring

theorem frozenDensityCubicTerm_smul (S : ι → Mat) (G : Mat) (H : ι → ℂ)
    (a : ℝ) (q : Vec) (J : ι → ℂ) (b : ℝ) (r : Vec) (L : ι → ℂ) :
    frozenDensityCubicTerm S G H (a • q) J (b • r) L =
      (a : ℂ) * (b : ℂ) * frozenDensityCubicTerm S G H q J r L := by
  simp only [frozenDensityCubicTerm, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frozenDensityCubicVertex_smul (S : ι → Mat) (G : Mat) (a : ℝ)
    (p : Vec) (H : ι → ℂ) (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) :
    frozenDensityCubicVertex S G (a • p) H (a • q) J (a • r) L =
      ((a ^ 2 : ℝ) : ℂ) * frozenDensityCubicVertex S G p H q J r L := by
  simp only [frozenDensityCubicVertex, frozenDensityCubicTerm_smul, Complex.ofReal_pow]
  ring

theorem frozenDensityCubicVertex_conj (S : ι → Mat) (G : Mat)
    (p : Vec) (H : ι → ℂ) (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) :
    conj (frozenDensityCubicVertex S G p H q J r L) =
      frozenDensityCubicVertex S G p (fun i => conj (H i))
        q (fun i => conj (J i)) r (fun i => conj (L i)) := by
  simp only [frozenDensityCubicVertex, frozenDensityCubicTerm, densityCoefficientDirection,
    map_neg, map_add, map_sum, map_mul, Complex.conj_ofReal]

end Burnett.V04
