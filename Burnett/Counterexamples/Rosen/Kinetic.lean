import Burnett.Counterexamples.Rosen.Curvature
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Rosen multiscale example

The null graph measure, its moments, and the canonical Hamilton pairing.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale.Transport
open scoped ContDiff BigOperators Topology
open Burnett.RosenMultiscale

abbrev Coordinate := Fin 4 → ℝ

def coordinateBasis (i : Fin 4) : Coordinate := Pi.single i 1

def du : Coordinate := coordinateBasis 0

/-- The actual matrix nonsingular inverse, explicitly avoiding the Pi inverse. -/
def inverseMetric (G : CoordinateMetric) : CoordinateMetric :=
  @Inv.inv CoordinateMetric Matrix.inv G

theorem inverseMetric_eq_adjugate (G : CoordinateMetric) :
    inverseMetric G = Ring.inverse G.det • G.adjugate := rfl

/-- The original canonical half quadratic inverse-metric Hamiltonian. -/
def P (g : Coordinate → CoordinateMetric) (x ξ : Coordinate) : ℝ :=
  (∑ i, ∑ j, inverseMetric (g x) i j * ξ i * ξ j) / 2

def basePartial (i : Fin 4) (a : Coordinate → Coordinate → ℝ)
    (x ξ : Coordinate) : ℝ :=
  fderiv ℝ (fun y => a y ξ) x (coordinateBasis i)

def momentumPartial (i : Fin 4) (a : Coordinate → Coordinate → ℝ)
    (x ξ : Coordinate) : ℝ :=
  fderiv ℝ (a x) ξ (coordinateBasis i)

def canonicalHamilton (g : Coordinate → CoordinateMetric)
    (a : Coordinate → Coordinate → ℝ) (x ξ : Coordinate) : ℝ :=
  ∑ i, (momentumPartial i (P g) x ξ * basePartial i a x ξ -
    basePartial i (P g) x ξ * momentumPartial i a x ξ)

def blockQuadratic (b d v s t : ℝ) (ξ : Coordinate) : ℝ :=
  (∑ i, ∑ j, inversePulledMetricAt b d v s t i j * ξ i * ξ j) / 2

theorem blockQuadratic_eq_coordinates (b d v s t : ℝ) (ξ : Coordinate) :
    blockQuadratic b d v s t ξ =
      -(b⁻¹) * ξ 0 * ξ 1 + (d * v / b^2) * (ξ 1)^2 +
        (s⁻¹ * (ξ 2)^2 + t⁻¹ * (ξ 3)^2) / 2 := by
  simp [blockQuadratic, inversePulledMetricAt, Fin.sum_univ_succ]
  ring

theorem P_du_entry (g : Coordinate → CoordinateMetric) (x : Coordinate) :
    P g x du = inverseMetric (g x) 0 0 / 2 := by
  simp [P, du, coordinateBasis, Fin.sum_univ_succ]

theorem inverseMetric_pulledRosenField (B ψ : ℝ → ℝ) (x : Coordinate)
    (hB : B (x 0) ≠ 0) :
    inverseMetric (pulledRosenField B ψ x) =
      inversePulledMetricAt (B (x 0)) (deriv B (x 0)) (x 1)
        (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))) := by
  change (pulledMetricAt (B (x 0)) (deriv B (x 0)) (x 1)
      (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))))⁻¹ = _
  exact pulledMetricAt_inv _ _ _ _ _ hB
    (mul_ne_zero (pow_ne_zero _ hB) (Real.exp_pos _).ne')
    (mul_ne_zero (pow_ne_zero _ hB) (Real.exp_pos _).ne')

theorem originalRosenField_eq_block (B ψ : ℝ → ℝ) (x : Coordinate) :
    originalRosenField B ψ x =
      pulledMetricAt 1 0 (x 1)
        (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [originalRosenField, pulledMetricAt]

theorem inverseMetric_originalRosenField (B ψ : ℝ → ℝ) (x : Coordinate)
    (hB : B (x 0) ≠ 0) :
    inverseMetric (originalRosenField B ψ x) =
      inversePulledMetricAt 1 0 (x 1)
        (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))) := by
  rw [originalRosenField_eq_block]
  change (pulledMetricAt 1 0 (x 1)
      (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))))⁻¹ = _
  exact pulledMetricAt_inv _ _ _ _ _ (by norm_num)
    (mul_ne_zero (pow_ne_zero _ hB) (Real.exp_pos _).ne')
    (mul_ne_zero (pow_ne_zero _ hB) (Real.exp_pos _).ne')

theorem inverseMetric_pulledRosen_du_du (B ψ : ℝ → ℝ) (x : Coordinate) :
    inverseMetric (pulledRosenField B ψ x) 0 0 = 0 := by
  by_cases hb : B (x 0) = 0
  · have hd : (pulledRosenField B ψ x).det = 0 := by
      simp [pulledRosenField, pulledMetricAt_det, hb]
    rw [inverseMetric_eq_adjugate, hd]
    simp
  · rw [inverseMetric_pulledRosenField B ψ x hb]
    simp [inversePulledMetricAt]

theorem inverseMetric_originalRosen_du_du (B ψ : ℝ → ℝ) (x : Coordinate) :
    inverseMetric (originalRosenField B ψ x) 0 0 = 0 := by
  by_cases hb : B (x 0) = 0
  · have hd : (originalRosenField B ψ x).det = 0 := by
      rw [originalRosenField_eq_block, pulledMetricAt_det]
      simp [screenX, screenZ, hb]
    rw [inverseMetric_eq_adjugate, hd]
    simp
  · rw [inverseMetric_originalRosenField B ψ x hb]
    simp [inversePulledMetricAt]

theorem P_pulledRosen_du (B ψ : ℝ → ℝ) (x : Coordinate) :
    P (pulledRosenField B ψ) x du = 0 := by
  rw [P_du_entry, inverseMetric_pulledRosen_du_du, zero_div]

theorem P_originalRosen_du (B ψ : ℝ → ℝ) (x : Coordinate) :
    P (originalRosenField B ψ) x du = 0 := by
  rw [P_du_entry, inverseMetric_originalRosen_du_du, zero_div]

theorem P_pulledRosen_eq_blockQuadratic (B ψ : ℝ → ℝ) (x ξ : Coordinate)
    (hB : B (x 0) ≠ 0) :
    P (pulledRosenField B ψ) x ξ =
      blockQuadratic (B (x 0)) (deriv B (x 0)) (x 1)
        (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))) ξ := by
  unfold P blockQuadratic
  rw [inverseMetric_pulledRosenField B ψ x hB]

theorem P_originalRosen_eq_blockQuadratic (B ψ : ℝ → ℝ) (x ξ : Coordinate)
    (hB : B (x 0) ≠ 0) :
    P (originalRosenField B ψ) x ξ =
      blockQuadratic 1 0 (x 1)
        (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0))) ξ := by
  unfold P blockQuadratic
  rw [inverseMetric_originalRosenField B ψ x hB]


theorem blockQuadratic_momentum_hasFDerivAt_du (b d v s t : ℝ) :
    HasFDerivAt (blockQuadratic b d v s t)
      (-(b⁻¹) • (ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ)) du := by
  have hc (i : Fin 4) : HasFDerivAt (fun ξ : Coordinate => ξ i)
      (ContinuousLinearMap.proj i : Coordinate →L[ℝ] ℝ) du :=
    (ContinuousLinearMap.proj i : Coordinate →L[ℝ] ℝ).hasFDerivAt
  have h01 : HasFDerivAt (fun ξ : Coordinate => ξ 0 * ξ 1)
      (ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 0).mul (hc 1)
  have h1 : HasFDerivAt (fun ξ : Coordinate => (ξ 1)^2) (0 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 1).pow 2
  have h2 : HasFDerivAt (fun ξ : Coordinate => (ξ 2)^2) (0 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 2).pow 2
  have h3 : HasFDerivAt (fun ξ : Coordinate => (ξ 3)^2) (0 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 3).pow 2
  have h := ((h01.const_mul (-(b⁻¹))).add (h1.const_mul (d * v / b^2))).add
    (((h2.const_mul s⁻¹).add (h3.const_mul t⁻¹)).const_mul ((2 : ℝ)⁻¹))
  rw [show blockQuadratic b d v s t =
      (fun ξ : Coordinate => -(b⁻¹) * ξ 0 * ξ 1 + (d * v / b^2) * (ξ 1)^2 +
        (s⁻¹ * (ξ 2)^2 + t⁻¹ * (ξ 3)^2) / 2) from
      funext (blockQuadratic_eq_coordinates b d v s t)]
  have hneg : (-(b⁻¹) • (ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ)) =
      -(b⁻¹ • (ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ)) := by
    ext w
    change -(b⁻¹) * w 1 = -(b⁻¹ * w 1)
    ring
  rw [hneg]
  simp only [hneg] at h
  simpa only [Pi.add_def, smul_zero, add_zero, zero_add,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem P_pulledRosen_momentum_hasFDerivAt_du (B ψ : ℝ → ℝ) (x : Coordinate)
    (hB : B (x 0) ≠ 0) :
    HasFDerivAt (P (pulledRosenField B ψ) x)
      (-((B (x 0))⁻¹) • (ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ)) du := by
  have h := blockQuadratic_momentum_hasFDerivAt_du
    (B (x 0)) (deriv B (x 0)) (x 1)
    (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0)))
  convert h using 1
  funext ξ
  exact P_pulledRosen_eq_blockQuadratic B ψ x ξ hB

theorem P_originalRosen_momentum_hasFDerivAt_du (B ψ : ℝ → ℝ) (x : Coordinate)
    (hB : B (x 0) ≠ 0) :
    HasFDerivAt (P (originalRosenField B ψ) x)
      (-(ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ)) du := by
  have h := blockQuadratic_momentum_hasFDerivAt_du 1 0 (x 1)
    (screenX (B (x 0)) (ψ (x 0))) (screenZ (B (x 0)) (ψ (x 0)))
  have he : P (originalRosenField B ψ) x =
      blockQuadratic 1 0 (x 1) (screenX (B (x 0)) (ψ (x 0)))
        (screenZ (B (x 0)) (ψ (x 0))) := by
    funext ξ
    exact P_originalRosen_eq_blockQuadratic B ψ x ξ hB
  rw [he]
  convert h using 1
  ext w
  simp

theorem basePartial_P_pulledRosen_du (B ψ : ℝ → ℝ) (x : Coordinate) (i : Fin 4) :
    basePartial i (P (pulledRosenField B ψ)) x du = 0 := by
  simp [basePartial, P_pulledRosen_du]

theorem basePartial_P_originalRosen_du (B ψ : ℝ → ℝ) (x : Coordinate) (i : Fin 4) :
    basePartial i (P (originalRosenField B ψ)) x du = 0 := by
  simp [basePartial, P_originalRosen_du]

theorem momentumPartial_P_pulledRosen_du (B ψ : ℝ → ℝ) (x : Coordinate)
    (hB : B (x 0) ≠ 0) (i : Fin 4) :
    momentumPartial i (P (pulledRosenField B ψ)) x du =
      if i = 1 then -((B (x 0))⁻¹) else 0 := by
  unfold momentumPartial
  rw [(P_pulledRosen_momentum_hasFDerivAt_du B ψ x hB).fderiv]
  fin_cases i <;> simp [coordinateBasis]

theorem momentumPartial_P_originalRosen_du (B ψ : ℝ → ℝ) (x : Coordinate)
    (hB : B (x 0) ≠ 0) (i : Fin 4) :
    momentumPartial i (P (originalRosenField B ψ)) x du =
      if i = 1 then -1 else 0 := by
  unfold momentumPartial
  rw [(P_originalRosen_momentum_hasFDerivAt_du B ψ x hB).fderiv]
  fin_cases i <;> simp [coordinateBasis]

theorem canonicalHamilton_pulledRosen_du (B ψ : ℝ → ℝ)
    (a : Coordinate → Coordinate → ℝ) (x : Coordinate) (hB : B (x 0) ≠ 0) :
    canonicalHamilton (pulledRosenField B ψ) a x du =
      -((B (x 0))⁻¹) * basePartial 1 a x du := by
  unfold canonicalHamilton
  simp_rw [momentumPartial_P_pulledRosen_du B ψ x hB, basePartial_P_pulledRosen_du]
  simp

theorem canonicalHamilton_originalRosen_du (B ψ : ℝ → ℝ)
    (a : Coordinate → Coordinate → ℝ) (x : Coordinate) (hB : B (x 0) ≠ 0) :
    canonicalHamilton (originalRosenField B ψ) a x du = -basePartial 1 a x du := by
  unfold canonicalHamilton
  simp_rw [momentumPartial_P_originalRosen_du B ψ x hB, basePartial_P_originalRosen_du]
  simp

theorem du_ne_zero : du ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [du, coordinateBasis] at h0

theorem cos_pos_on_original_interval (u : ℝ)
    (hu : u ∈ Set.Ioo (-(1 / 4) : ℝ) (1 / 4)) : 0 < Real.cos u := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.one_le_pi_div_two, hu.1, hu.2]

theorem canonicalHamilton_pulled_cos_du (a : Coordinate → Coordinate → ℝ)
    (x : Coordinate) (hx : x 0 ∈ Set.Ioo (-(1 / 4) : ℝ) (1 / 4)) :
    canonicalHamilton (pulledRosenField Real.cos (fun _ => 0)) a x du =
      -((Real.cos (x 0))⁻¹) * basePartial 1 a x du :=
  canonicalHamilton_pulledRosen_du _ _ a x (cos_pos_on_original_interval _ hx).ne'

theorem canonicalHamilton_original_cos_du (a : Coordinate → Coordinate → ℝ)
    (x : Coordinate) (hx : x 0 ∈ Set.Ioo (-(1 / 4) : ℝ) (1 / 4)) :
    canonicalHamilton (originalRosenField Real.cos (fun _ => 0)) a x du =
      -basePartial 1 a x du :=
  canonicalHamilton_originalRosen_du _ _ a x (cos_pos_on_original_interval _ hx).ne'



theorem P_pulled_cos_eq_coordinates (x ξ : Coordinate) (hB : Real.cos (x 0) ≠ 0) :
    P (pulledRosenField Real.cos (fun _ => 0)) x ξ =
      -((Real.cos (x 0))⁻¹) * ξ 0 * ξ 1 +
        (-Real.sin (x 0)) * x 1 * ((Real.cos (x 0))^2)⁻¹ * (ξ 1)^2 +
        (((Real.cos (x 0))^2)⁻¹ * (ξ 2)^2 +
          ((Real.cos (x 0))^2)⁻¹ * (ξ 3)^2) / 2 := by
  rw [P_pulledRosen_eq_blockQuadratic _ _ x ξ hB, blockQuadratic_eq_coordinates]
  simp only [screenX, screenZ, Real.deriv_cos, mul_zero, Real.exp_zero, mul_one,
    div_eq_mul_inv]

theorem P_original_cos_eq_coordinates (x ξ : Coordinate) (hB : Real.cos (x 0) ≠ 0) :
    P (originalRosenField Real.cos (fun _ => 0)) x ξ =
      -(ξ 0 * ξ 1) +
        (((Real.cos (x 0))^2)⁻¹ * (ξ 2)^2 +
          ((Real.cos (x 0))^2)⁻¹ * (ξ 3)^2) / 2 := by
  rw [P_originalRosen_eq_blockQuadratic _ _ x ξ hB, blockQuadratic_eq_coordinates]
  simp [screenX, screenZ]

theorem P_pulled_cos_joint_contDiffAt (z : Coordinate × Coordinate)
    (hB : Real.cos (z.1 0) ≠ 0) :
    ContDiffAt ℝ ∞
      (fun y : Coordinate × Coordinate =>
        P (pulledRosenField Real.cos (fun _ => 0)) y.1 y.2) z := by
  have hx (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : Coordinate × Coordinate => y.1 i) z :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffAt
  have hξ (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : Coordinate × Coordinate => y.2 i) z :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffAt
  have hc := (hx 0).cos
  have hs := (hx 0).sin
  have hci := hc.inv hB
  have hc2i := (hc.pow 2).inv (pow_ne_zero 2 hB)
  have hp := (((hci.neg.mul (hξ 0)).mul (hξ 1)).add
      (((hs.neg.mul (hx 1)).mul hc2i).mul ((hξ 1).pow 2))).add
    (((hc2i.mul ((hξ 2).pow 2)).add (hc2i.mul ((hξ 3).pow 2))).div_const 2)
  apply hp.congr_of_eventuallyEq
  filter_upwards [hc.continuousAt.eventually_ne hB] with y hy
  rw [P_pulled_cos_eq_coordinates y.1 y.2 hy]

theorem P_original_cos_joint_contDiffAt (z : Coordinate × Coordinate)
    (hB : Real.cos (z.1 0) ≠ 0) :
    ContDiffAt ℝ ∞
      (fun y : Coordinate × Coordinate =>
        P (originalRosenField Real.cos (fun _ => 0)) y.1 y.2) z := by
  have hx : ContDiffAt ℝ ∞ (fun y : Coordinate × Coordinate => y.1 0) z :=
    ((contDiff_apply ℝ ℝ (0 : Fin 4)).comp contDiff_fst).contDiffAt
  have hξ (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : Coordinate × Coordinate => y.2 i) z :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffAt
  have hc := hx.cos
  have hc2i := (hc.pow 2).inv (pow_ne_zero 2 hB)
  have hp := ((hξ 0).mul (hξ 1)).neg.add
    (((hc2i.mul ((hξ 2).pow 2)).add (hc2i.mul ((hξ 3).pow 2))).div_const 2)
  apply hp.congr_of_eventuallyEq
  filter_upwards [hc.continuousAt.eventually_ne hB] with y hy
  rw [P_original_cos_eq_coordinates y.1 y.2 hy]

theorem basePartial_eq_joint_fderiv (a : Coordinate → Coordinate → ℝ)
    (x ξ : Coordinate)
    (ha : DifferentiableAt ℝ (fun y : Coordinate × Coordinate => a y.1 y.2) (x, ξ))
    (i : Fin 4) :
    basePartial i a x ξ =
      fderiv ℝ (fun y : Coordinate × Coordinate => a y.1 y.2)
        (x, ξ) (coordinateBasis i, 0) := by
  have hid : HasFDerivAt (fun y : Coordinate => y)
      (ContinuousLinearMap.id ℝ Coordinate) x := hasFDerivAt_id x
  have hconst : HasFDerivAt (fun _ : Coordinate => ξ)
      (0 : Coordinate →L[ℝ] Coordinate) x := hasFDerivAt_const ξ x
  have h := ha.hasFDerivAt.comp x (hid.prodMk hconst)
  simp only [Function.comp_def] at h
  unfold basePartial
  rw [h.fderiv]
  rfl

theorem canonicalHamilton_pulled_cos_du_joint_fderiv
    (a : Coordinate → Coordinate → ℝ) (x : Coordinate)
    (hx : x 0 ∈ Set.Ioo (-(1 / 4) : ℝ) (1 / 4))
    (ha : DifferentiableAt ℝ (fun y : Coordinate × Coordinate => a y.1 y.2) (x, du)) :
    canonicalHamilton (pulledRosenField Real.cos (fun _ => 0)) a x du =
      fderiv ℝ (fun y : Coordinate × Coordinate => a y.1 y.2)
        (x, du) (-((Real.cos (x 0))⁻¹) • coordinateBasis 1, 0) := by
  rw [canonicalHamilton_pulled_cos_du a x hx, basePartial_eq_joint_fderiv a x du ha]
  rw [show (-((Real.cos (x 0))⁻¹) • coordinateBasis 1, (0 : Coordinate)) =
      -((Real.cos (x 0))⁻¹) • (coordinateBasis 1, (0 : Coordinate)) by simp]
  rw [map_smul]
  rfl

theorem canonicalHamilton_original_cos_du_joint_fderiv
    (a : Coordinate → Coordinate → ℝ) (x : Coordinate)
    (hx : x 0 ∈ Set.Ioo (-(1 / 4) : ℝ) (1 / 4))
    (ha : DifferentiableAt ℝ (fun y : Coordinate × Coordinate => a y.1 y.2) (x, du)) :
    canonicalHamilton (originalRosenField Real.cos (fun _ => 0)) a x du =
      fderiv ℝ (fun y : Coordinate × Coordinate => a y.1 y.2)
        (x, du) (-coordinateBasis 1, 0) := by
  rw [canonicalHamilton_original_cos_du a x hx, basePartial_eq_joint_fderiv a x du ha]
  rw [show (-coordinateBasis 1, (0 : Coordinate)) =
      -(coordinateBasis 1, (0 : Coordinate)) by simp]
  rw [map_neg]

end Burnett.RosenMultiscale.Transport

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open Filter MeasureTheory Set
open scoped ENNReal NNReal

def rosenInterval : Set ℝ := Ioo (-(1 / 4) : ℝ) (1 / 4)

def coordinateLebesgue : Measure Coordinate := volume.restrict {x | x 0 ∈ rosenInterval}

def pulledLimitDensity (x : Coordinate) : ℝ := 2 * (Real.cos (x 0))^3

def originalLimitDensity (x : Coordinate) : ℝ := 2 * (Real.cos (x 0))^2

def rosenKineticWeight (pulled : Bool) (x : Coordinate) : ℝ≥0 :=
  (if pulled then pulledLimitDensity x else originalLimitDensity x).toNNReal

def rosenKineticMeasure (pulled : Bool) : Measure (Coordinate × Coordinate) :=
  (coordinateLebesgue.withDensity fun x => (rosenKineticWeight pulled x : ℝ≥0∞)).map (fun x => (x, du))

theorem rosenInterval_cos_pos (u : ℝ) (hu : u ∈ rosenInterval) : 0 < Real.cos u := by
  have h := show u ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) from hu
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.two_le_pi], by linarith [h.2, Real.two_le_pi]⟩

theorem coordinateLebesgue_ae_mem : ∀ᵐ x ∂coordinateLebesgue, x 0 ∈ rosenInterval := by
  have hset : MeasurableSet (rosenInterval : Set ℝ) := isOpen_Ioo.measurableSet
  exact ae_restrict_mem (hset.preimage (measurable_pi_apply 0))

theorem rosenKineticWeight_coe (pulled : Bool) (x : Coordinate) (hx : x 0 ∈ rosenInterval) :
    (rosenKineticWeight pulled x : ℝ) = if pulled then pulledLimitDensity x else originalLimitDensity x := by
  have hp := rosenInterval_cos_pos (x 0) hx
  cases pulled <;> simp [rosenKineticWeight, pulledLimitDensity, originalLimitDensity, hp.le]

theorem rosenKineticWeight_measurable (pulled : Bool) : Measurable (rosenKineticWeight pulled) := by
  cases pulled
  · change Measurable (fun x : Coordinate => (2 * (Real.cos (x 0))^2).toNNReal)
    fun_prop
  · change Measurable (fun x : Coordinate => (2 * (Real.cos (x 0))^3).toNNReal)
    fun_prop

theorem rosenKineticMeasure_ae_graph (pulled : Bool) :
    ∀ᵐ p ∂(rosenKineticMeasure pulled), p.1 0 ∈ rosenInterval ∧ p.2 = du := by
  have hgraph : Measurable (fun x : Coordinate => (x, du)) := measurable_id.prodMk measurable_const
  have hrect : MeasurableSet {p : Coordinate × Coordinate | p.1 0 ∈ rosenInterval ∧ p.2 = du} :=
    (isOpen_Ioo.measurableSet.preimage ((measurable_pi_apply 0).comp measurable_fst)).inter
      ((measurableSet_singleton du).preimage measurable_snd)
  unfold rosenKineticMeasure
  rw [ae_map_iff hgraph.aemeasurable hrect]
  have hbase : ∀ᵐ x ∂(coordinateLebesgue.withDensity fun x => (rosenKineticWeight pulled x : ℝ≥0∞)),
      x 0 ∈ rosenInterval := (withDensity_absolutelyContinuous coordinateLebesgue
        (fun x => (rosenKineticWeight pulled x : ℝ≥0∞))).ae_le coordinateLebesgue_ae_mem
  exact hbase.mono fun _ hx => ⟨hx, rfl⟩

theorem rosenKineticMeasure_integral (pulled : Bool) (b : Coordinate × Coordinate → ℝ) (hb : Measurable b) :
    ∫ p, b p ∂rosenKineticMeasure pulled =
      ∫ x, (if pulled then pulledLimitDensity x else originalLimitDensity x) * b (x, du) ∂coordinateLebesgue := by
  have hgraph : Measurable (fun x : Coordinate => (x, du)) := measurable_id.prodMk measurable_const
  unfold rosenKineticMeasure
  rw [integral_map hgraph.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (rosenKineticWeight_measurable pulled)]
  apply integral_congr_ae
  filter_upwards [coordinateLebesgue_ae_mem] with x hx
  change (rosenKineticWeight pulled x : ℝ) * b (x, du) = _
  rw [rosenKineticWeight_coe pulled x hx]

theorem rosenKineticMeasure_coordinate_moment (pulled : Bool) (a : Coordinate → ℝ) (ha : Measurable a)
    (i j : Fin 4) :
    ∫ p, a p.1 * p.2 i * p.2 j ∂rosenKineticMeasure pulled =
      ∫ x, if i = 0 ∧ j = 0 then
        (if pulled then pulledLimitDensity x else originalLimitDensity x) * a x else 0 ∂coordinateLebesgue := by
  have hmeas : Measurable (fun p : Coordinate × Coordinate => a p.1 * p.2 i * p.2 j) := by fun_prop
  rw [rosenKineticMeasure_integral pulled _ hmeas]
  congr 1
  funext x
  have hdu (k : Fin 4) : du k = if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · subst k
      simp [du, coordinateBasis]
    · simp [du, coordinateBasis, hk]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [hdu, hi, hj]

theorem rosen_du_norm : ‖du‖ = 1 := by
  rw [du, coordinateBasis, Pi.norm_single, norm_one]

theorem rosenKineticMeasure_compact_base (pulled : Bool) {K : Set Coordinate} (hK : IsCompact K) :
    rosenKineticMeasure pulled (Prod.fst ⁻¹' K) < ∞ := by
  have hbound (x : Coordinate) : (rosenKineticWeight pulled x : ℝ≥0∞) ≤ 2 := by
    have hpow (k : ℕ) : (Real.cos (x 0))^k ≤ 1 := by
      apply (le_abs_self _).trans
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
    change ENNReal.ofReal (if pulled then pulledLimitDensity x else originalLimitDensity x) ≤ 2
    calc
      _ ≤ ENNReal.ofReal 2 := by
        apply ENNReal.ofReal_le_ofReal
        cases pulled
        · change 2 * (Real.cos (x 0))^2 ≤ 2
          linarith only [hpow 2]
        · change 2 * (Real.cos (x 0))^3 ≤ 2
          linarith only [hpow 3]
      _ = _ := by norm_num
  have hdom := withDensity_mono (μ := coordinateLebesgue) (Filter.Eventually.of_forall hbound)
  have hgraph : Measurable (fun x : Coordinate => (x, du)) := measurable_id.prodMk measurable_const
  rw [rosenKineticMeasure, Measure.map_apply hgraph (hK.isClosed.measurableSet.preimage measurable_fst)]
  change (coordinateLebesgue.withDensity fun x => (rosenKineticWeight pulled x : ℝ≥0∞)) K < ∞
  apply (hdom K).trans_lt
  rw [withDensity_const, Measure.smul_apply, smul_eq_mul]
  have hvol : coordinateLebesgue K < ∞ :=
    (Measure.restrict_apply_le _ _).trans_lt (hK.measure_lt_top (μ := volume))
  exact ENNReal.mul_lt_top (by norm_num) hvol

theorem rosenKineticMeasure_compact_second_moment (pulled : Bool) {K : Set Coordinate} (hK : IsCompact K) :
    ∫⁻ p in Prod.fst ⁻¹' K, ENNReal.ofReal (‖p.2‖^2) ∂rosenKineticMeasure pulled < ∞ := by
  have heq : (fun p : Coordinate × Coordinate => ENNReal.ofReal (‖p.2‖^2))
      =ᵐ[(rosenKineticMeasure pulled).restrict (Prod.fst ⁻¹' K)] (fun _ => 1) := by
    filter_upwards [ae_restrict_of_ae (rosenKineticMeasure_ae_graph pulled)] with p hp
    simp [hp.2, rosen_du_norm]
  rw [lintegral_congr_ae heq, lintegral_one, Measure.restrict_apply_univ]
  exact rosenKineticMeasure_compact_base pulled hK

end Burnett.RosenMultiscale.Transport

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open Matrix

theorem rosenLimitDensity_is_twice_metric_volume (pulled : Bool) (p : Coordinate)
    (hp : p 0 ∈ rosenInterval) :
    (if pulled then pulledLimitDensity p else originalLimitDensity p) =
      2 * Real.sqrt |((if pulled then pulledRosenField else originalRosenField)
        Real.cos (fun _ => 0) p).det| := by
  cases pulled
  · change originalLimitDensity p = 2 * Real.sqrt |(originalRosenField Real.cos (fun _ => 0) p).det|
    have hm : originalRosenField Real.cos (fun _ => 0) p =
        pulledMetricAt 1 0 0 (screenX (Real.cos (p 0)) 0) (screenZ (Real.cos (p 0)) 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [originalRosenField, pulledMetricAt]
    rw [hm, pulledMetricAt_det]
    unfold originalLimitDensity
    rw [one_pow, one_mul, screen_product, abs_neg]
    have hpow : Real.cos (p 0)^4 = (Real.cos (p 0)^2)^2 := by ring
    rw [hpow, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  · change pulledLimitDensity p = 2 * Real.sqrt |(pulledRosenField Real.cos (fun _ => 0) p).det|
    unfold pulledLimitDensity pulledRosenField
    rw [pulledRosen_volume _ _ _ _ (rosenInterval_cos_pos (p 0) hp)]

end Burnett.RosenMultiscale.Transport

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open MeasureTheory Set
open scoped ENNReal

theorem rosenKineticMeasure_integrable_coordinate_moment (pulled : Bool) (a : Coordinate → ℝ)
    (ha : Continuous a) (hcompact : HasCompactSupport a) (i j : Fin 4) :
    Integrable (fun p : Coordinate × Coordinate => a p.1 * p.2 i * p.2 j) (rosenKineticMeasure pulled) := by
  let μ := coordinateLebesgue.withDensity fun x => (rosenKineticWeight pulled x : ℝ≥0∞)
  let F := fun x : Coordinate => (x, du)
  have hF : Measurable F := measurable_id.prodMk measurable_const
  letI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    have hh := rosenKineticMeasure_compact_base pulled hK
    change μ.map F (Prod.fst ⁻¹' K) < ∞ at hh
    rw [Measure.map_apply hF (hK.isClosed.measurableSet.preimage measurable_fst)] at hh
    exact hh⟩
  have hs : Integrable (fun x => a x * du i * du j) μ :=
    ((ha.integrable_of_hasCompactSupport hcompact).mul_const (du i)).mul_const (du j)
  have hm : Measurable (fun p : Coordinate × Coordinate => a p.1 * p.2 i * p.2 j) := by fun_prop
  exact (integrable_map_measure hm.aestronglyMeasurable hF.aemeasurable).2 hs

end Burnett.RosenMultiscale.Transport

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open MeasureTheory Set
open scoped ENNReal

theorem rosenKineticMeasure_ne_zero (pulled : Bool) : rosenKineticMeasure pulled ≠ 0 := by
  let slab : Set Coordinate := {x | x 0 ∈ rosenInterval}
  let w := fun x => (rosenKineticWeight pulled x : ℝ≥0∞)
  let F := fun x : Coordinate => (x, du)
  have hF : Measurable F := measurable_id.prodMk measurable_const
  have hw : Measurable w := (rosenKineticWeight_measurable pulled).coe_nnreal_ennreal
  have hopen : IsOpen slab := isOpen_Ioo.preimage (continuous_apply 0)
  have hpos (x : Coordinate) (hx : x ∈ slab) : w x ≠ 0 := by
    have hc := rosenInterval_cos_pos (x 0) hx
    have hreal : 0 < (rosenKineticWeight pulled x : ℝ) := by
      rw [rosenKineticWeight_coe pulled x hx]
      cases pulled
      · exact mul_pos (by norm_num) (pow_pos hc 2)
      · exact mul_pos (by norm_num) (pow_pos hc 3)
    intro hz
    have hzero : rosenKineticWeight pulled x = 0 := ENNReal.coe_eq_zero.mp hz
    simp [hzero] at hreal
  intro hzero
  have hbase : coordinateLebesgue.withDensity w univ = 0 := by
    have h := congrArg (fun μ : Measure (Coordinate × Coordinate) => μ univ) hzero
    change (coordinateLebesgue.withDensity w).map F univ = _ at h
    rw [Measure.map_apply hF MeasurableSet.univ] at h
    simpa using h
  have hnull := (withDensity_apply_eq_zero hw).mp hbase
  have hsub : slab ⊆ {x | w x ≠ 0} ∩ (univ : Set Coordinate) := fun x hx => ⟨hpos x hx, mem_univ x⟩
  have hslab : coordinateLebesgue slab = 0 := measure_mono_null hsub hnull
  change volume.restrict slab slab = 0 at hslab
  rw [Measure.restrict_apply hopen.measurableSet, inter_self] at hslab
  have hnonempty : slab.Nonempty := ⟨fun _ => 0, by norm_num [slab, rosenInterval]⟩
  exact hopen.measure_ne_zero (volume : Measure Coordinate) hnonempty hslab

end Burnett.RosenMultiscale.Transport

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference

theorem rosenKineticMeasure_moment_eq_limit_ricci (pulled : Bool) (a : Coordinate → ℝ)
    (ha : Continuous a) (hcompact : HasCompactSupport a) (i j : Index) :
    let g := if pulled then pulledScreenBilinear Real.cos
      (fun u => screenX (Real.cos u) 0) (fun u => screenZ (Real.cos u) 0)
      else originalRosenBilinear Real.cos (fun _ => 0)
    let G := (if pulled then pulledRosenField else originalRosenField) Real.cos (fun _ => 0)
    Integrable (fun p : Coordinate × Coordinate => a p.1 * p.2 i * p.2 j) (rosenKineticMeasure pulled) ∧
    (∫ p, a p.1 * p.2 i * p.2 j ∂rosenKineticMeasure pulled) =
      ∫ x, a x * coordinateRicci (computedConnection g) (WithLp.toLp 2 x) i j *
        Real.sqrt |(G x).det| ∂coordinateLebesgue := by
  dsimp only
  refine ⟨rosenKineticMeasure_integrable_coordinate_moment pulled a ha hcompact i j, ?_⟩
  rw [rosenKineticMeasure_coordinate_moment pulled a ha.measurable i j]
  apply integral_congr_ae
  filter_upwards [coordinateLebesgue_ae_mem] with x hx
  rw [rosenLimitDensity_is_twice_metric_volume pulled x hx]
  have hr : coordinateRicci (computedConnection (if pulled then pulledScreenBilinear Real.cos
      (fun u => screenX (Real.cos u) 0) (fun u => screenZ (Real.cos u) 0)
      else originalRosenBilinear Real.cos (fun _ => 0))) (WithLp.toLp 2 x) i j =
      if i = 0 ∧ j = 0 then 2 else 0 := by
    cases pulled
    · exact coordinateRicci_originalRosen_cos rosenInterval isOpen_Ioo
        (fun u hu => (rosenInterval_cos_pos u hu).ne') (WithLp.toLp 2 x) hx i j
    · exact coordinateRicci_pulledRosen_cos (WithLp.toLp 2 x) hx i j
  rw [hr]
  split_ifs <;> ring

end Burnett.RosenMultiscale.Transport

noncomputable section

namespace Burnett.RosenMultiscale.Transport

open Filter MeasureTheory
open scoped ENNReal

def rosenLimitMetric (pulled : Bool) : Coordinate → CoordinateMetric :=
  (if pulled then pulledRosenField else originalRosenField) Real.cos (fun _ => 0)

theorem rosenKineticMeasure_ae_nonzero_null (pulled : Bool) :
    ∀ᵐ p ∂(rosenKineticMeasure pulled),
      p.1 0 ∈ rosenInterval ∧ p.2 ≠ 0 ∧ P (rosenLimitMetric pulled) p.1 p.2 = 0 := by
  filter_upwards [rosenKineticMeasure_ae_graph pulled] with p hp
  refine ⟨hp.1, hp.2.symm ▸ du_ne_zero, ?_⟩
  rw [hp.2]
  cases pulled
  · exact P_originalRosen_du Real.cos (fun _ => 0) p.1
  · exact P_pulledRosen_du Real.cos (fun _ => 0) p.1

theorem rosenKineticMeasure_transport_pairing (pulled : Bool) (a : Coordinate → Coordinate → ℝ) :
    let H := canonicalHamilton (rosenLimitMetric pulled) a
    let d := fun x => if pulled then pulledLimitDensity x else originalLimitDensity x
    (Integrable (fun p : Coordinate × Coordinate => H p.1 p.2) (rosenKineticMeasure pulled) ↔
      Integrable (fun x => d x * H x du) coordinateLebesgue) ∧
    (∫ p, H p.1 p.2 ∂rosenKineticMeasure pulled) = ∫ x, d x * H x du ∂coordinateLebesgue := by
  dsimp only
  let H := canonicalHamilton (rosenLimitMetric pulled) a
  let d := fun x => if pulled then pulledLimitDensity x else originalLimitDensity x
  let f := fun x : Coordinate => if pulled then -((Real.cos (x 0))⁻¹) * basePartial 1 a x du
    else -basePartial 1 a x du
  let F := fun x : Coordinate => (x, du)
  let μ := coordinateLebesgue.withDensity fun x => (rosenKineticWeight pulled x : ℝ≥0∞)
  have hF : Measurable F := measurable_id.prodMk measurable_const
  have hb : Measurable (fun x : Coordinate => basePartial 1 a x du) :=
    measurable_fderiv_apply_const ℝ (fun x : Coordinate => a x du) (coordinateBasis 1)
  have hf : Measurable f := by
    cases pulled
    · exact hb.neg
    · have hc : Measurable (fun x : Coordinate => Real.cos (x 0)) :=
        Real.continuous_cos.measurable.comp (measurable_pi_apply 0)
      exact hc.inv.neg.mul hb
  have hEq (x : Coordinate) (hx : x 0 ∈ rosenInterval) : H x du = f x := by
    cases pulled
    · exact canonicalHamilton_original_cos_du a x hx
    · exact canonicalHamilton_pulled_cos_du a x hx
  have hPhase : (fun p : Coordinate × Coordinate => H p.1 p.2) =ᵐ[rosenKineticMeasure pulled]
      (fun p => f p.1) := by
    filter_upwards [rosenKineticMeasure_ae_graph pulled] with p hp
    rw [hp.2, hEq p.1 hp.1]
  have hWeighted : (fun x => (rosenKineticWeight pulled x : ℝ) * f x) =ᵐ[coordinateLebesgue]
      (fun x => d x * H x du) := by
    filter_upwards [coordinateLebesgue_ae_mem] with x hx
    rw [rosenKineticWeight_coe pulled x hx, hEq x hx]
  have hDensity : (fun x => d x * f x) =ᵐ[coordinateLebesgue] (fun x => d x * H x du) := by
    filter_upwards [coordinateLebesgue_ae_mem] with x hx
    rw [hEq x hx]
  constructor
  · calc
      _ ↔ Integrable (fun p : Coordinate × Coordinate => f p.1) (rosenKineticMeasure pulled) :=
        integrable_congr hPhase
      _ ↔ Integrable f μ := (integrable_map_measure (hf.comp measurable_fst).aestronglyMeasurable
        hF.aemeasurable)
      _ ↔ Integrable (fun x => (rosenKineticWeight pulled x : ℝ) * f x) coordinateLebesgue :=
        integrable_withDensity_iff_integrable_smul (rosenKineticWeight_measurable pulled)
      _ ↔ _ := integrable_congr hWeighted
  · calc
      _ = ∫ p : Coordinate × Coordinate, f p.1 ∂rosenKineticMeasure pulled := integral_congr_ae hPhase
      _ = ∫ x, d x * f x ∂coordinateLebesgue :=
        rosenKineticMeasure_integral pulled _ (hf.comp measurable_fst)
      _ = _ := integral_congr_ae hDensity

end Burnett.RosenMultiscale.Transport
