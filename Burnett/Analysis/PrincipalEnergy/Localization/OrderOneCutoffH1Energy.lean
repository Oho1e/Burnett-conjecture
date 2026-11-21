import Burnett.Analysis.PrincipalEnergy.Localization.OrderOneCutoffOverlap

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Set Function Metric Burnett.Fourier Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.SymmetricEnergy
open scoped BigOperators ContDiff

/-- The cutoff derivative obeys the actual pointwise product rule. -/
theorem scalarSchwartzProduct_pderiv (e : Space) (χ f : SchwartzMap Space ℂ) :
    SchwartzMap.pderivCLM ℂ e (scalarSchwartzProduct χ f) =
      scalarSchwartzProduct χ (SchwartzMap.pderivCLM ℂ e f) +
        scalarSchwartzProduct (SchwartzMap.pderivCLM ℂ e χ) f := by
  ext x
  change fderiv ℝ (fun y => χ y * f y) x e =
    χ x * fderiv ℝ (f : Space → ℂ) x e + fderiv ℝ (χ : Space → ℂ) x e * f x
  rw [fderiv_fun_mul χ.differentiableAt f.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem translateSchwartz_tsupport_subset_closedBall (χ : SchwartzMap Space ℂ) (c : Space) (R : ℝ)
    (hχ : tsupport (χ : Space → ℂ) ⊆ closedBall (0 : Space) R) :
    tsupport (translateSchwartz (-c) χ : Space → ℂ) ⊆ closedBall c R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have h : x-c ∈ closedBall (0 : Space) R :=
    hχ (subset_closure (show χ (x-c) ≠ 0 by simpa only [translateSchwartz_apply, sub_eq_add_neg] using hx))
  simpa only [mem_closedBall, dist_eq_norm, dist_zero_right, sub_zero] using h

private theorem radialDerivative_support_subset (χ : SchwartzMap Space ℂ) (e : Space) :
    tsupport (SchwartzMap.pderivCLM ℂ e χ : Space → ℂ) ⊆ tsupport (χ : Space → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply support_fderiv_subset ℝ
  intro hz
  apply hx
  change fderiv ℝ (χ : Space → ℂ) x e = 0
  rw [hz, ContinuousLinearMap.zero_apply]

private theorem schwartzNormToLp_sq_add_le (u v : SchwartzMap Space ℂ) :
    ‖(u+v : SchwartzMap Space ℂ).toLp 2 volume‖^2 ≤
      2*(‖u.toLp 2 volume‖^2+‖v.toLp 2 volume‖^2) := by
  have h : ‖(u+v : SchwartzMap Space ℂ).toLp 2 volume‖ ≤ ‖u.toLp 2 volume‖+‖v.toLp 2 volume‖ := by
    change ‖SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space) (u+v)‖ ≤ _
    rw [map_add]
    exact norm_add_le _ _
  calc
    _ ≤ (‖u.toLp 2 volume‖+‖v.toLp 2 volume‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := by nlinarith only [sq_nonneg (‖u.toLp 2 volume‖-‖v.toLp 2 volume‖)]

/-- Localizing the input at radius five costs one H¹ constant on any finite
subset of the lattice. This constant uses the cutoff shape alone. -/
theorem exists_latticeCutoff_coordinateH1_square_sum_bound {χ : SchwartzMap Space ℂ}
    (hSupp : tsupport (χ : Space → ℂ) ⊆ closedBall (0 : Space) 5)
    (hSup : ∀ x, ‖χ x‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset LatticeIndex) (f : SchwartzMap Space ℂ),
      (∑ i : ↥s, coordinateH1 (scalarSchwartzProduct
        (translateSchwartz (-latticeCenter i.val) χ) f)^2) ≤ C^2 * coordinateH1 f^2 := by
  let D : ℝ := ((17^4 : ℕ) : ℝ)
  let T := SchwartzMap.seminorm ℝ 0 1 χ
  let M := D+8*D*(1+T^2)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun s f => ?_⟩
  let Q (i : ↥s) := translateSchwartz (-latticeCenter i.val) χ
  let F (i : ↥s) := scalarSchwartzProduct (Q i) f
  let Dv (b : Fin 4) : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
    SchwartzMap.pderivCLM ℂ (coordinateDirection b)
  let H := coordinateH1 f
  have hSupp' (i : ↥s) : tsupport (Q i : Space → ℂ) ⊆ closedBall (latticeCenter i.val) 5 :=
    translateSchwartz_tsupport_subset_closedBall χ _ _ hSupp
  have hQ (i : ↥s) (x : Space) : ‖Q i x‖ ≤ 1 := hSup _
  have hTd (b : Fin 4) (i : ↥s) (x : Space) : ‖Dv b (Q i) x‖ ≤ T := by
    simp only [Dv, Q, SchwartzMap.pderivCLM_apply, translateSchwartz_fderiv]
    let y := x + -latticeCenter i.val
    have hDir : ‖coordinateDirection b‖ = 1 := by simp [coordinateDirection]
    have hNorm : ‖fderiv ℝ (χ : Space → ℂ) y‖ ≤ T := by
      calc
        _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (χ : Space → ℂ)) y‖ := by rw [norm_iteratedFDeriv_zero]
        _ = ‖iteratedFDeriv ℝ 1 (χ : Space → ℂ) y‖ := norm_iteratedFDeriv_fderiv
        _ ≤ _ := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ 1 y
    calc
      _ ≤ ‖fderiv ℝ (χ : Space → ℂ) y‖ * ‖coordinateDirection b‖ :=
        (fderiv ℝ (χ : Space → ℂ) y).le_opNorm _
      _ ≤ _ := by rw [hDir, mul_one]; exact hNorm
  have hVal (x : Space) : (∑ i, ‖Q i x‖^2) ≤ D := by
    simpa only [D, one_pow, mul_one] using sum_latticeCutoff_values_sq_le s Q 1 hSupp' hQ x
  have hDerivative (b : Fin 4) (x : Space) : (∑ i, ‖Dv b (Q i) x‖^2) ≤ D*T^2 :=
    sum_latticeCutoff_values_sq_le s (fun i => Dv b (Q i)) T
      (fun i => (radialDerivative_support_subset (Q i) (coordinateDirection b)).trans (hSupp' i))
      (hTd b) x
  have hF₂ : ‖f.toLp 2 volume‖ ≤ H := by
    change ‖f.toLp 2 volume‖ ≤ coordinateH1 f
    rw [← schwartzCoordinateJet_norm, ← schwartzCoordinateJet_zero_component]
    exact PiLp.norm_apply_le _ _
  have hDf₂ (b : Fin 4) : ‖(Dv b f).toLp 2 volume‖ ≤ H := by
    change ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection b) f).toLp 2 volume‖ ≤ coordinateH1 f
    rw [← schwartzCoordinateJet_norm, ← schwartzCoordinateJet_succ_component]
    exact PiLp.norm_apply_le _ _
  have hBase : (∑ i, ‖(F i).toLp 2 volume‖^2) ≤ D*H^2 :=
    (scalarCutoff_sum_L2_sq_le_of_square_bound Q f D hVal).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hF₂ 2) hD)
  have hDer (b : Fin 4) : (∑ i, ‖(Dv b (F i)).toLp 2 volume‖^2) ≤ 2*D*(1+T^2)*H^2 := by
    calc
      _ ≤ ∑ i, 2*(‖(scalarSchwartzProduct (Q i) (Dv b f)).toLp 2 volume‖^2+
          ‖(scalarSchwartzProduct (Dv b (Q i)) f).toLp 2 volume‖^2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [show Dv b (F i) = scalarSchwartzProduct (Q i) (Dv b f)+
            scalarSchwartzProduct (Dv b (Q i)) f from scalarSchwartzProduct_pderiv _ _ _]
        exact schwartzNormToLp_sq_add_le _ _
      _ ≤ 2*(D*‖(Dv b f).toLp 2 volume‖^2+(D*T^2)*‖f.toLp 2 volume‖^2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (add_le_add
          (scalarCutoff_sum_L2_sq_le_of_square_bound Q (Dv b f) D hVal)
          (scalarCutoff_sum_L2_sq_le_of_square_bound (fun i => Dv b (Q i)) f (D*T^2) (hDerivative b)))
          (by positivity)
      _ ≤ 2*(D*H^2+(D*T^2)*H^2) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hDf₂ b) 2) hD)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hF₂ 2) (mul_nonneg hD (sq_nonneg _))))
          (by positivity)
      _ = _ := by ring
  have hEnergy (g : SchwartzMap Space ℂ) : coordinateH1 g^2 =
      ‖g.toLp 2 volume‖^2+∑ b : Fin 4, ‖(Dv b g).toLp 2 volume‖^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  change (∑ i, coordinateH1 (F i)^2) ≤ Real.sqrt M ^ 2 * H^2
  simp_rw [hEnergy (F _)]
  rw [Finset.sum_add_distrib, Finset.sum_comm, Real.sq_sqrt hM]
  calc
    _ ≤ D*H^2+∑ _b : Fin 4, 2*D*(1+T^2)*H^2 := add_le_add hBase (Finset.sum_le_sum fun b _ => hDer b)
    _ = _ := by simp only [M, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring

end Burnett.Analysis.CarlesonEmbedding
