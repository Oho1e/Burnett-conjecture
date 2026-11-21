import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearPolarization

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- The paper's constant linear coefficient map, represented by its real entries
in a basis of the finite field space. -/
def linearEnergyCoefficient {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (H : J → SchwartzMap E ℂ) (k : EnergyIndex J) : SchwartzMap E ℂ :=
  ∑ j, c k j • H j

private def schwartzEvaluation {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    SchwartzMap E F →+ (E → F) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem linearEnergyCoefficient_symmetry {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (H : J → SchwartzMap E ℂ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (hH : ∀ j x, conj (H j x) = H j x) :
    ∀ a d i j x, conj (linearEnergyCoefficient c H ((a,d),(i,j)) x) =
      linearEnergyCoefficient c H ((d,a),(j,i)) x := by
  intro a d i j x
  unfold linearEnergyCoefficient
  change conj ((schwartzEvaluation (∑ l, c ((a,d),(i,j)) l • H l)) x) =
    (schwartzEvaluation (∑ l, c ((d,a),(j,i)) l • H l)) x
  simp only [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  change conj ((c ((a,d),(i,j)) l : ℂ) * H l x) =
    (c ((d,a),(j,i)) l : ℂ) * H l x
  rw [map_mul, Complex.conj_ofReal, hH, hc]

theorem energyGradientNorm_lt_top (f : SchwartzMap E ℂ) : energyGradientNorm f < ⊤ := by
  exact ((SchwartzMap.fderivCLM ℝ f).memLp (ENNReal.ofReal 3) volume).eLpNorm_lt_top

private theorem energyGradientNorm_smul (r : ℝ) (f : SchwartzMap E ℂ) :
    energyGradientNorm (r • f) = ‖r‖ₑ * energyGradientNorm f := by
  change eLpNorm (SchwartzMap.fderivCLM ℝ (r • f) : E → E →L[ℝ] ℂ) (ENNReal.ofReal 3) volume = _
  rw [map_smul]
  exact eLpNorm_const_smul r (SchwartzMap.fderivCLM ℝ f : E → E →L[ℝ] ℂ) _ _

set_option maxHeartbeats 800000 in
private theorem energyGradientNorm_sum_le {J : Type} [Fintype J] (f : J → SchwartzMap E ℂ) :
    energyGradientNorm (∑ j, f j) ≤ ∑ j, energyGradientNorm (f j) := by
  change eLpNorm (schwartzEvaluation (SchwartzMap.fderivCLM ℝ (∑ j, f j)))
    (ENNReal.ofReal 3) volume ≤ _
  rw [map_sum, map_sum]
  let D (j : J) : E → E →L[ℝ] ℂ := SchwartzMap.fderivCLM ℝ (f j)
  change eLpNorm (∑ j, D j) (ENNReal.ofReal 3) volume ≤ ∑ j, eLpNorm (D j) (ENNReal.ofReal 3) volume
  exact eLpNorm_sum_le (f := D) (fun j _ => (SchwartzMap.fderivCLM ℝ (f j)).continuous.aestronglyMeasurable)
    (by norm_num)

private theorem field_component_le_sum {J : Type} [Fintype J]
    (f : J → SchwartzMap E ℂ) (i : J) :
    energyGradientNorm (f i) ≤ fieldEnergyGradientNorm f := by
  classical
  exact Finset.single_le_sum (fun j _ => zero_le (energyGradientNorm (f j))) (Finset.mem_univ i)

private theorem linearEnergyCoefficient_norm {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (H : J → SchwartzMap E ℂ) :
    (∑ k, energyGradientNorm (linearEnergyCoefficient c H k)) ≤
      (∑ k, ∑ j, ‖c k j‖ₑ) * fieldEnergyGradientNorm H := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  unfold linearEnergyCoefficient
  apply (energyGradientNorm_sum_le _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [energyGradientNorm_smul]
  exact mul_le_mul_left' (field_component_le_sum H j) _

/-- With the actual constant real coefficient map substituted, the polarized
quasilinear pairing has one full gradient norm in each of its three slots. -/
theorem quasilinear_linear_coefficient_estimate (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ H u v : J → SchwartzMap E ℂ,
      (∀ j x, conj (H j x) = H j x) →
      ENNReal.ofReal |quasilinearSymmetricEnergy b (linearEnergyCoefficient c H) u v| ≤
        C * (fieldEnergyGradientNorm H * (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) := by
  obtain ⟨K, hK, est⟩ := quasilinear_polarized_estimate b hb hom
  let M := ∑ k, ∑ j, ‖c k j‖ₑ
  have hM : M < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ =>
    ENNReal.sum_lt_top.mpr fun _ _ => enorm_lt_top
  refine ⟨K * M, ENNReal.mul_lt_top hK hM, fun H u v hH => ?_⟩
  have hbA := est (linearEnergyCoefficient c H) u v (linearEnergyCoefficient_symmetry c H hc hH)
  calc
    _ ≤ _ := hbA
    _ ≤ K * ((M * fieldEnergyGradientNorm H) * (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) :=
      mul_le_mul_left' (mul_le_mul_right' (linearEnergyCoefficient_norm c H) _) K
    _ = _ := by ring

end Burnett.A02.FrequencySplit
