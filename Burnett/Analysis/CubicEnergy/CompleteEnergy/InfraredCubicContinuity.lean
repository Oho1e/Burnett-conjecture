import Burnett.Analysis.CubicEnergy.CompleteEnergy.CubicSymmetrization
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedLowerOrderCompleteCubic
import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformCompleteCubic
import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformWeightedEuclidean

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ContDiff ENNReal

/-- The full Euclidean value and first-derivative norms of a field. -/
def euclideanFieldSobolevNorm {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ≥0∞ :=
  eLpNorm (fieldValueArray u) (ENNReal.ofReal 3) volume + euclideanFieldGradientNorm u

theorem euclideanFieldSobolevNorm_lt_top {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) :
    euclideanFieldSobolevNorm u < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨(fieldValueArray_memLp u _).eLpNorm_lt_top, euclideanFieldGradientNorm_lt_top u⟩

/-- The real W¹³ norm is the sum of the Euclidean value and gradient norms. -/
def euclideanFieldW13 {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ :=
  (euclideanFieldSobolevNorm u).toReal

theorem euclideanFieldW13_eq {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) :
    euclideanFieldW13 u = euclideanFieldValueL3 u + euclideanFieldGradientL3 u :=
  ENNReal.toReal_add (fieldValueArray_memLp u _).eLpNorm_lt_top.ne (euclideanFieldGradientNorm_lt_top u).ne

private theorem component_grad_le_inhomogeneous {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) :
    fieldEnergyGradientNorm u ≤ fieldInhomogeneousNorm u := by
  unfold fieldInhomogeneousNorm inhomogeneousComponentNorm
  rw [Finset.sum_add_distrib]
  exact le_add_of_nonneg_left (zero_le _)

theorem fieldInhomogeneousNorm_le_euclidean {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) :
    fieldInhomogeneousNorm u ≤ ((Fintype.card J : ℝ≥0∞) * Fintype.card Index) *
      euclideanFieldSobolevNorm u := by
  let N : ℝ≥0∞ := Fintype.card J
  let M : ℝ≥0∞ := N * Fintype.card Index
  have hi : (1 : ℝ≥0∞) ≤ (Fintype.card Index : ℝ≥0∞) := by
    change (1 : ℝ≥0∞) ≤ (Fintype.card (Fin 4) : ℝ≥0∞)
    simp
  have hNM : N ≤ M := by simpa only [M, mul_one] using mul_le_mul_left' hi N
  have values : (∑ j, eLpNorm (u j : E → ℂ) (ENNReal.ofReal 3) volume) ≤
      M * eLpNorm (fieldValueArray u) (ENNReal.ofReal 3) volume :=
    (component_values_L3_le_euclidean u).trans (mul_le_mul_right' hNM _)
  unfold fieldInhomogeneousNorm inhomogeneousComponentNorm euclideanFieldSobolevNorm
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add values (fieldEnergyGradientNorm_le_euclidean u)

/-- The same complete regularized physical energy is the diagonal of a real
symmetric cubic form, with a common Euclidean W¹³ bound in its three slots. -/
theorem fixed_infrared_complete_symmetric_euclidean_bound {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∃ T : MultilinearMap ℝ (fun _ : Fin 3 => RealEnergyField J) ℝ,
        (∀ (v : Fin 3 → RealEnergyField J) (σ : Equiv.Perm (Fin 3)), T (v ∘ σ) = T v) ∧
        (∀ u : RealEnergyField J, T (fun _ => u) =
          completeCubicEnergy c q (fixedInfraredSymbol cut add b) u) ∧
        (∀ v : Fin 3 → RealEnergyField J, ‖T v‖ₑ ≤ C * (ENNReal.ofReal D + 1) *
          ∏ i, euclideanFieldSobolevNorm (v i : J → SchwartzMap E ℂ)) := by
  obtain ⟨A,hA,homBound⟩ := complete_cubic_map_L3_sphere_bound c hc q
  obtain ⟨B,hB,cutBound⟩ := fixed_cut_complete_cubic_W13_sphere_bound cut hcut c q
  obtain ⟨R,hR,Tadd,addDiag,addBound⟩ := fixed_profile_complete_cubic_W13_bound add hadd c q
  let M : ℝ≥0∞ := (Fintype.card J : ℝ≥0∞) * Fintype.card Index
  let C : ℝ≥0∞ := (A+B+R)*M^3
  have hM : M < ⊤ := ENNReal.mul_lt_top (by simp) (by simp)
  have hM3 : M^3 < ⊤ := by
    rw [pow_succ, pow_two]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hM hM) hM
  refine ⟨C, ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hA,hB⟩,hR⟩) hM3, ?_⟩
  intro b hb hom D hD jet
  obtain ⟨Tcut,cutDiag,cutEst⟩ := cutBound b hb hom D hD (fun n hn => jet n (le_trans hn (by norm_num)))
  let H := completeSymmetricCubicMap c q b hb hom
  let Treg := H - Tcut + Tadd
  let d := ENNReal.ofReal D
  refine ⟨symmetricAverageCubic Treg, symmetricAverageCubic_permute Treg, ?_, ?_⟩
  · intro u
    rw [symmetricAverageCubic_diag]
    change H (fun _ => u) - Tcut (fun _ => u) + Tadd (fun _ => u) = _
    rw [complete_cubic_map_diag c q b hb hom u, cutDiag u, addDiag u]
    exact (complete_cubic_energy_fixed_infrared_split c q cut add hcut hadd b hb hom u).symm
  · let G (w : RealEnergyField J) := euclideanFieldSobolevNorm (w : J → SchwartzMap E ℂ)
    refine symmetricAverageCubic_bound Treg G (C * (d+1)) ?_
    intro v
    let P := ∏ i, fieldInhomogeneousNorm (v i : J → SchwartzMap E ℂ)
    let mass := ∏ i, G (v i)
    have grad : (∏ i, fieldEnergyGradientNorm (v i : J → SchwartzMap E ℂ)) ≤ P :=
      Finset.prod_le_prod' (fun i _ => component_grad_le_inhomogeneous (v i : J → SchwartzMap E ℂ))
    have sobolev : P ≤ M^3 * mass := calc
      _ ≤ ∏ i, M * G (v i) :=
        Finset.prod_le_prod' (fun i _ => fieldInhomogeneousNorm_le_euclidean (v i : J → SchwartzMap E ℂ))
      _ = _ := by dsimp only [mass]; simp only [Fin.prod_univ_three]; ring
    have coefficient : (A+B)*d + R ≤ (A+B+R)*(d+1) := calc
      _ ≤ ((A+B)*d + R) + ((A+B) + R*d) := le_add_of_nonneg_right (zero_le _)
      _ = _ := by ring
    have h : ‖H v‖ₑ ≤ A * d * P :=
      (homBound b hb hom D hD jet v).trans (mul_le_mul_left' grad _)
    have hs : ‖H v - Tcut v‖ₑ ≤ ‖H v‖ₑ + ‖Tcut v‖ₑ := by
      simpa only [sub_eq_add_neg, enorm_neg] using (enorm_add_le (H v) (-Tcut v))
    change ‖H v - Tcut v + Tadd v‖ₑ ≤ C * (d+1) * mass
    calc
      _ ≤ (A*d*P + B*d*P) + R*P :=
        (enorm_add_le _ _).trans (add_le_add (hs.trans (add_le_add h (cutEst v))) (addBound v))
      _ = ((A+B)*d+R)*P := by ring
      _ ≤ ((A+B+R)*(d+1))*(M^3*mass) := mul_le_mul' coefficient sobolev
      _ = _ := by dsimp only [C]; ring

/-- The fixed inhomogeneous continuity statement on the actual regularized
diagonal, with the paper's W¹³ norm and the uniform symbol coefficient. -/
theorem fixed_infrared_complete_continuity_euclidean {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ u v : RealEnergyField J,
        |completeCubicEnergy c q (fixedInfraredSymbol cut add b) u -
          completeCubicEnergy c q (fixedInfraredSymbol cut add b) v| ≤
        (C*(D+1)) * euclideanFieldW13 (↑(u-v) : J → SchwartzMap E ℂ) *
          (euclideanFieldW13 (u : J → SchwartzMap E ℂ) + euclideanFieldW13 (v : J → SchwartzMap E ℂ))^2 := by
  obtain ⟨K,hK,estimate⟩ := fixed_infrared_complete_symmetric_euclidean_bound c hc q cut add hcut hadd
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro b hb hom D hD jet u v
  obtain ⟨T,_,diag,products⟩ := estimate b hb hom D hD jet
  let G (w : RealEnergyField J) := euclideanFieldSobolevNorm (w : J → SchwartzMap E ℂ)
  let d := ENNReal.ofReal D
  let C := K*(d+1)
  have h := trilinear_diagonal_enorm_bound T G C products u v
  rw [diag u, diag v] at h
  have gfinite (w : RealEnergyField J) : G w < ⊤ := euclideanFieldSobolevNorm_lt_top _
  have gpair : G u + G v < ⊤ := ENNReal.add_lt_top.mpr ⟨gfinite u,gfinite v⟩
  have hd : d < ⊤ := ENNReal.ofReal_lt_top
  have hC : C < ⊤ := ENNReal.mul_lt_top hK (ENNReal.add_lt_top.mpr ⟨hd,by simp⟩)
  have finite : C * G (u-v) * (G u + G v)^2 < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hC (gfinite (u-v))) (by rw [pow_two]; exact ENNReal.mul_lt_top gpair gpair)
  rw [Real.enorm_eq_ofReal_abs] at h
  have real := ENNReal.toReal_mono finite.ne h
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_pow,
    C, ENNReal.toReal_add hd.ne (by simp : (1 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_one,
    ENNReal.toReal_add (gfinite u).ne (gfinite v).ne, d, ENNReal.toReal_ofReal hD,
    euclideanFieldW13, G] using real

end Burnett.A02.FrequencySplit
