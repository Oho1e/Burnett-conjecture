import Burnett.Analysis.AllScaleTransfer.EightDimensionalModeSummation
import Burnett.Analysis.AngularCaps.ParabolicProfileJets
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.A05

open Metric Set Burnett.A02.FrequencySplit
open Burnett.A03 (spatialLatticeVector spatialLatticeWeight spatialModePhase)
open Burnett.Analysis.ProjectiveNullCaps (exists_uniform_right_slice_iteratedFDeriv)
open scoped ContDiff RealInnerProductSpace BigOperators

/-- The signed angular direction used in the fixed-box expansion. -/
def endpointDirection (ξ : E) : E := ‖ξ‖⁻¹ • ξ

theorem endpointDirection_pos_smul (t : ℝ) (ht : 0 < t) (ξ : E) :
    endpointDirection (t • ξ) = endpointDirection ξ := by
  simp only [endpointDirection, norm_smul, Real.norm_of_nonneg ht.le, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

theorem endpointDirection_mem_sphere {ξ : E} (hξ : ξ ≠ 0) :
    endpointDirection ξ ∈ sphere (0 : E) 1 := by
  rw [mem_sphere, dist_zero_right, endpointDirection, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)

theorem endpointDirection_contDiffOn : ContDiffOn ℝ ∞ endpointDirection {ξ : E | ξ ≠ 0} := by
  have hnorm : ContDiffOn ℝ ∞ (fun ξ : E => ‖ξ‖) {ξ : E | ξ ≠ 0} :=
    contDiffOn_id.norm ℝ (fun _ h => h)
  exact (hnorm.inv (fun _ h => norm_ne_zero_iff.mpr h)).smul contDiffOn_id

/-- Exactly the one-slot phase of the normalized box, evaluated on signed unit directions. -/
def endpointModePhase (P : ℝ) (a : FourierMode) (ξ : E) : ℝ :=
  spatialModePhase P a (endpointDirection ξ)

def endpointModeSymbol (P : ℝ) (a : FourierMode) (ξ : E) : ℂ :=
  Complex.exp ((endpointModePhase P a ξ : ℂ) * Complex.I)

theorem endpointModeSymbol_pos_smul (P : ℝ) (a : FourierMode) (t : ℝ) (ht : 0 < t) (ξ : E) :
    endpointModeSymbol P a (t • ξ) = endpointModeSymbol P a ξ := by
  simp only [endpointModeSymbol, endpointModePhase, endpointDirection_pos_smul t ht ξ]

theorem endpointModeSymbol_norm (P : ℝ) (a : FourierMode) (ξ : E) : ‖endpointModeSymbol P a ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private def directionPhase (P : ℝ) (z : E × E) : ℝ :=
  tau * inner ℝ (endpointDirection z.2) ((2 * P)⁻¹ • z.1)

private theorem directionPhase_joint_contDiffOn (P : ℝ) :
    ContDiffOn ℝ ∞ (directionPhase P) {z : E × E | z.2 ≠ 0} := by
  have hd : ContDiffOn ℝ ∞ (fun z : E × E => endpointDirection z.2) {z | z.2 ≠ 0} :=
    endpointDirection_contDiffOn.comp contDiff_snd.contDiffOn (fun _ h => h)
  have hv : ContDiffOn ℝ ∞ (fun z : E × E => (2 * P)⁻¹ • z.1) {z | z.2 ≠ 0} :=
    (contDiff_fst.const_smul _).contDiffOn
  exact (hd.inner ℝ hv).const_smul tau

private theorem directionPhase_contDiffOn (P : ℝ) (k : E) :
    ContDiffOn ℝ ∞ (fun ξ => directionPhase P (k,ξ)) {ξ : E | ξ ≠ 0} :=
  (directionPhase_joint_contDiffOn P).comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (fun _ h => h)

theorem endpointModePhase_contDiffOn (P : ℝ) (a : FourierMode) :
    ContDiffOn ℝ ∞ (endpointModePhase P a) {ξ : E | ξ ≠ 0} :=
  directionPhase_contDiffOn P (spatialLatticeVector a)

theorem endpointModePhase_pos_smul (P : ℝ) (a : FourierMode) (t : ℝ) (ht : 0 < t) (ξ : E) :
    endpointModePhase P a (t • ξ) = endpointModePhase P a ξ := by
  rw [endpointModePhase, endpointDirection_pos_smul t ht ξ]
  rfl

private theorem exists_phase_sphere_jets (P : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a : FourierMode) (j : ℕ), j ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ j (endpointModePhase P a) ξ‖ ≤ C * spatialLatticeWeight a := by
  let U : Set (E × E) := {z | z.2 ≠ 0}
  let K := closedBall (0 : E) 1 ×ˢ sphere (0 : E) 1
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKU : K ⊆ U := fun _ h => ne_of_mem_sphere h.2 (by norm_num)
  choose D hD jet using fun j : Fin 7 =>
    exists_uniform_right_slice_iteratedFDeriv hU (directionPhase_joint_contDiffOn P) hK hKU j.val
  let C := 1 + ∑ j : Fin 7, D j
  have hsum : (0 : ℝ) ≤ ∑ j : Fin 7, D j := Finset.sum_nonneg fun j _ => (hD j).le
  have hC : 1 ≤ C := le_add_of_nonneg_right hsum
  refine ⟨C,hC,?_⟩
  intro a j hj ξ hξ
  let l : Fin 7 := ⟨j,Nat.lt_succ_of_le hj⟩
  have hDj : D l ≤ C := (Finset.single_le_sum (fun k _ => (hD k).le) (Finset.mem_univ l)).trans
    (le_add_of_nonneg_left zero_le_one)
  let w := spatialLatticeWeight a
  let k := spatialLatticeVector a
  let u := w⁻¹ • k
  have hw : 0 < w := by dsimp only [w, spatialLatticeWeight]; positivity
  have hu : u ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, show u = w⁻¹ • k from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hw.le), inv_mul_eq_div, div_le_one hw]
    exact le_add_of_nonneg_left zero_le_one
  have hvec : w • u = k := by rw [show u = w⁻¹ • k from rfl, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
  have hphase : endpointModePhase P a = fun x => w • directionPhase P (u,x) := by
    funext x
    change tau * inner ℝ (endpointDirection x) ((2 * P)⁻¹ • k) =
      w * (tau * inner ℝ (endpointDirection x) ((2 * P)⁻¹ • u))
    calc
      _ = tau * inner ℝ (endpointDirection x) ((2 * P)⁻¹ • (w • u)) := by rw [hvec]
      _ = w * (tau * inner ℝ (endpointDirection x) ((2 * P)⁻¹ • u)) := by
        rw [smul_comm ((2 * P)⁻¹) w u, real_inner_smul_right]
        ring
  have hx0 : ξ ≠ 0 := ne_of_mem_sphere hξ (by norm_num)
  have hOpen : IsOpen {ξ : E | ξ ≠ 0} := isOpen_ne
  have hs : ContDiffAt ℝ j (fun x => directionPhase P (u,x)) ξ :=
    ((directionPhase_contDiffOn P u).contDiffAt (hOpen.mem_nhds hx0)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [hphase, iteratedFDeriv_const_smul_apply' hs, norm_smul, Real.norm_of_nonneg hw.le]
  exact (mul_le_mul_of_nonneg_left ((jet l (u,ξ) ⟨hu,hξ⟩).trans hDj) hw.le).trans_eq (mul_comm _ _)

/-- The actual sine and cosine symbols have the same sixth-order Mikhlin budget. -/
theorem exists_endpoint_trig_sphere_jets (P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : FourierMode) (j : ℕ), j ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ j (Real.cos ∘ endpointModePhase P a) ξ‖ ≤ C * spatialLatticeWeight a ^ 6 ∧
      ‖iteratedFDeriv ℝ j (Real.sin ∘ endpointModePhase P a) ξ‖ ≤ C * spatialLatticeWeight a ^ 6 := by
  obtain ⟨D,hD,phaseBound⟩ := exists_phase_sphere_jets P
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨((Nat.factorial 6 : ℕ) : ℝ) * D^6, ?_, ?_⟩
  · positivity
  intro a j hj ξ hξ
  let U : Set E := {ξ | ξ ≠ 0}
  let w := spatialLatticeWeight a
  let phase := endpointModePhase P a
  have hU : IsOpen U := isOpen_ne
  have hx : ξ ∈ U := ne_of_mem_sphere hξ (by norm_num)
  have hw : 1 ≤ w := le_add_of_nonneg_right (norm_nonneg _)
  have hbase : 1 ≤ D*w := one_le_mul_of_one_le_of_one_le hD hw
  have hphase (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i phase U ξ‖ ≤ (D*w)^i := by
    rw [iteratedFDerivWithin_of_isOpen i hU hx]
    exact (phaseBound a i (hij.trans hj) ξ hξ).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hbase hi)
  have main (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
      (hJet : ∀ i x, ‖iteratedFDeriv ℝ i F x‖ ≤ 1) :
      ‖iteratedFDeriv ℝ j (F ∘ phase) ξ‖ ≤ ((Nat.factorial 6 : ℕ) : ℝ) * D ^ 6 * w ^ 6 := by
    rw [← iteratedFDerivWithin_of_isOpen j hU hx]
    have h := norm_iteratedFDerivWithin_comp_le hF.contDiffOn
      (endpointModePhase_contDiffOn P a) (WithTop.coe_le_coe.mpr le_top)
      uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hx
      (fun i _ => by simpa only [iteratedFDerivWithin_univ] using hJet i (phase ξ)) hphase
    calc
      _ ≤ ((Nat.factorial j : ℕ) : ℝ) * 1 * (D*w)^j := h
      _ ≤ ((Nat.factorial 6 : ℕ) : ℝ) * 1 * (D*w)^6 := by
        have hFact : ((Nat.factorial j : ℕ) : ℝ) ≤ ((Nat.factorial 6 : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le hj
        exact mul_le_mul (mul_le_mul_of_nonneg_right hFact zero_le_one)
          (pow_le_pow_right₀ hbase hj) (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, mul_one, ← mul_assoc]
  exact ⟨main Real.cos Real.contDiff_cos (fun i x => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one i x),
    main Real.sin Real.contDiff_sin (fun i x => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_sin_le_one i x)⟩

end Burnett.A05
