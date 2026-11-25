import Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents
import Burnett.Analysis.GaugeProjection.ProjectedPhysicalDensity
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

/-! Parseval expresses each projected energy using unprojected Schwartz inputs. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.P01

open Function MeasureTheory Filter Set Matrix Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AngularDyadicKernel (fourierMultiplier_schwartz_eq_inverse_mul_ae)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.SeparablePositive (inner_fourierMultiplier_left fourierMultiplier_product
  productSymbol conjugateSymbol productSymbol_apply conjugateSymbol_apply)
open scoped BigOperators ComplexConjugate ContDiff FourierTransform InnerProduct Matrix Topology

open private regularizedProjectionComponentSymbol_eq_off_ball
  from Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

/-- The actual product symbol for the squared norm of one output component. -/
def projectionEnergyComponentSymbol (k i j : OrderedPair) : BoundedSymbol E :=
  productSymbol (conjugateSymbol (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2))
    (regularizedProjectionComponentSymbol k.1 k.2 j.1 j.2)

def projectionEnergyPrincipalSymbol (k i j : OrderedPair) (ξ : E) : ℂ :=
  conj (principalProjectionComponentSymbol k.1 k.2 i.1 i.2 ξ) *
    principalProjectionComponentSymbol k.1 k.2 j.1 j.2 ξ

theorem projectionEnergyPrincipalSymbol_apply (k i j : OrderedPair) (ξ : E) :
    projectionEnergyPrincipalSymbol k i j ξ =
      principalGaugeProjectionMatrix ξ k i * principalGaugeProjectionMatrix ξ k j := by
  simp only [projectionEnergyPrincipalSymbol, principalProjectionComponentSymbol_apply,
    principalGaugeProjectionMatrix, Complex.conj_ofReal]

theorem projectionEnergyPrincipalSymbol_conj (k i j : OrderedPair) (ξ : E) :
    conj (projectionEnergyPrincipalSymbol k i j ξ) = projectionEnergyPrincipalSymbol k i j ξ := by
  rw [projectionEnergyPrincipalSymbol_apply]
  simp only [principalGaugeProjectionMatrix, map_mul, Complex.conj_ofReal]

theorem projectionEnergyPrincipalSymbol_smoothOn (k i j : OrderedPair) :
    ContDiffOn ℝ ∞ (projectionEnergyPrincipalSymbol k i j) ({0}ᶜ : Set E) := by
  rw [show projectionEnergyPrincipalSymbol k i j = (fun ξ =>
    (gaugeProjectionSymbol k.1 k.2 i.1 i.2 ξ : ℂ) *
      (gaugeProjectionSymbol k.1 k.2 j.1 j.2 ξ : ℂ)) from
    funext (projectionEnergyPrincipalSymbol_apply k i j)]
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (gaugeProjectionSymbol_contDiffOn k.1 k.2 i.1 i.2)).mul
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (gaugeProjectionSymbol_contDiffOn k.1 k.2 j.1 j.2))

theorem projectionEnergyPrincipalSymbol_scale (k i j : OrderedPair) (t : ℝ) (ht : 0 < t) (ξ : E) :
    projectionEnergyPrincipalSymbol k i j (t • ξ) = projectionEnergyPrincipalSymbol k i j ξ := by
  simp only [projectionEnergyPrincipalSymbol_apply, principalGaugeProjectionMatrix,
    gaugeProjectionSymbol_scale _ _ _ _ t ht]

theorem projectionEnergyComponentSymbol_smooth (k i j : OrderedPair) :
    ContDiff ℝ ∞ (projectionEnergyComponentSymbol k i j : E → ℂ) := by
  have h (l : OrderedPair) : ContDiff ℝ ∞ (fun ξ : E =>
      (regularizedGaugeProjectionSymbol k.1 k.2 l.1 l.2 (tau • ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((regularizedGaugeProjectionSymbol_contDiff k.1 k.2 l.1 l.2).comp
      (contDiff_const.smul contDiff_id))
  change ContDiff ℝ ∞ (fun ξ : E => conj
    (regularizedGaugeProjectionSymbol k.1 k.2 i.1 i.2 (tau • ξ) : ℂ) *
    (regularizedGaugeProjectionSymbol k.1 k.2 j.1 j.2 (tau • ξ) : ℂ))
  simpa only [Complex.conj_ofReal] using (h i).mul (h j)

theorem projectionEnergyComponentSymbol_eq_principal_of_large (k i j : OrderedPair) (ξ : E)
    (hξ : 2 / tau < ‖ξ‖) :
    projectionEnergyComponentSymbol k i j ξ = projectionEnergyPrincipalSymbol k i j ξ := by
  have ho : ξ ∉ Metric.closedBall 0 (2 / tau) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (not_le_of_gt hξ)
  simp only [projectionEnergyComponentSymbol, projectionEnergyPrincipalSymbol, productSymbol_apply,
    conjugateSymbol_apply, regularizedProjectionComponentSymbol_eq_off_ball _ _ _ _ _ ho]

private theorem fourierMultiplier_classicalLeftPairing (m : BoundedSymbol E) (f v : SchwartzMap E ℂ) :
    inner ℂ (v.toLp 2 volume) (fourierMultiplier m (f.toLp 2 volume)) =
      classicalLeftPairing (fun _ ξ => m ξ) v f := by
  unfold classicalLeftPairing
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [v.coeFn_toLp 2 volume, fourierMultiplier_schwartz_eq_inverse_mul_ae m f] with x hx hMx
  rw [hx, hMx, RCLike.inner_apply']
  rfl

theorem projectionEnergyComponentSymbol_actualPairing (k i j : OrderedPair) (f v : SchwartzMap E ℂ) :
    inner ℂ (v.toLp 2 volume) (fourierMultiplier (projectionEnergyComponentSymbol k i j) (f.toLp 2 volume)) =
      classicalLeftPairing (fun _ ξ => projectionEnergyComponentSymbol k i j ξ) v f :=
  fourierMultiplier_classicalLeftPairing (projectionEnergyComponentSymbol k i j) f v

/-- Parseval moves both Fourier multipliers onto one entry of the unprojected
input, whose original physical support can still be used in the limit. -/
theorem projectionFullSchwartz_component_norm_sq_eq_energyPairings
    (w : ProjectionSchwartzMatrix) (k : OrderedPair) :
    ‖(projectionFullSchwartz w k.1 k.2).toLp 2 volume‖^2 =
      (∑ i : OrderedPair, ∑ j : OrderedPair,
        inner ℂ ((w i.1 i.2).toLp 2 volume)
          (fourierMultiplier (projectionEnergyComponentSymbol k i j) ((w j.1 j.2).toLp 2 volume))).re := by
  let u (i : OrderedPair) := (w i.1 i.2).toLp 2 volume
  let P (i : OrderedPair) := regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2
  have hProj : (projectionFullSchwartz w k.1 k.2).toLp 2 volume =
      ∑ i : OrderedPair, fourierMultiplier (P i) (u i) := by
    change schwartzLpMap (projectionFullSchwartz w k.1 k.2) = _
    simp only [projectionFullSchwartz, map_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact gaugeProjectionComponent_toLp_eq_multiplier k.1 k.2 i j (w i j)
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hProj, sum_inner]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_fourierMultiplier_left]
  change inner ℂ (u i) (fourierMultiplier (conjugateSymbol (P i)) (fourierMultiplier (P j) (u j))) =
    inner ℂ (u i) (fourierMultiplier (productSymbol (conjugateSymbol (P i)) (P j)) (u j))
  rw [fourierMultiplier_product]

/-- Finite summation of the real principal product symbols gives a diagonal
entry of the projected covariance. -/
theorem sum_projectionEnergyPrincipalSymbol_mul_matrix (k : OrderedPair) (ξ : E)
    (N : Matrix OrderedPair OrderedPair ℂ) :
    (∑ i : OrderedPair, ∑ j : OrderedPair, projectionEnergyPrincipalSymbol k i j ξ * N i j) =
      (principalGaugeProjectionMatrix ξ * N * (principalGaugeProjectionMatrix ξ)ᴴ) k k := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, projectionEnergyPrincipalSymbol_apply,
    principalGaugeProjectionMatrix, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Burnett.P01
