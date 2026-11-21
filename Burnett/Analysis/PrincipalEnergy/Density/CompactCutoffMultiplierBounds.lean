import Burnett.Analysis.PrincipalEnergy.Density.FixedChartDensitySandwich
import Burnett.Analysis.PrincipalEnergy.Energy.CompactFourierNorms

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection Op firstOrderEnergy norm_derivative_le_firstOrderEnergy)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

def compactSchwartzMultiplier {ι : Type*} [Fintype ι] (χ : SchwartzMap Space ℂ) : Op (CompactMatrixTest ι) :=
  compactTransportOp (compactScalarMultiplier χ (χ.smooth ⊤))

theorem compactSchwartzMultiplier_comm_coordinate {ι : Type*} [Fintype ι]
    (b : Fin 4) (χ : SchwartzMap Space ℂ) :
    SymmetricEnergy.comm (compactMatrixCoordinatePartial b) (compactSchwartzMultiplier (ι := ι) χ) =
      compactSchwartzMultiplier (SchwartzMap.pderivCLM ℂ (coordinateDirection b) χ) := by
  have h := compactScalarMultiplier_leibniz (ι := ι) (χ : Space → ℂ) (χ.smooth ⊤) b
  change compactMatrixCoordinatePartial b * compactSchwartzMultiplier χ =
    compactSchwartzMultiplier χ * compactMatrixCoordinatePartial b +
      compactSchwartzMultiplier (SchwartzMap.pderivCLM ℂ (coordinateDirection b) χ) at h
  rw [SymmetricEnergy.comm, h, add_sub_cancel_left]

private theorem norm_le_matrixFirstOrderEnergy {ι : Type*} [Fintype ι] (u : CompactMatrixTest ι) :
    ‖u‖ ≤ firstOrderEnergy compactMatrixCoordinatePartial u := by
  unfold firstOrderEnergy
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem exists_compactSchwartzMultiplier_energy_bounds {ι : Type*} [Fintype ι] (χ : SchwartzMap Space ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : CompactMatrixTest ι,
      ‖compactSchwartzMultiplier χ u‖ ≤ C*‖u‖ ∧
      firstOrderEnergy compactMatrixCoordinatePartial (compactSchwartzMultiplier χ u) ≤
        C * firstOrderEnergy compactMatrixCoordinatePartial u := by
  let D : Fin 4 → Op (CompactMatrixTest ι) := compactMatrixCoordinatePartial
  let M := compactSchwartzMultiplier (ι := ι) χ
  let dχ (b : Fin 4) := SchwartzMap.pderivCLM ℂ (coordinateDirection b) χ
  let S := SchwartzMap.seminorm ℝ 0 0 χ
  let T (b : Fin 4) := SchwartzMap.seminorm ℝ 0 0 (dχ b)
  let A := S + ∑ b, T b
  have hS : 0 ≤ S := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ χ (0 : Space))
  have hT (b : Fin 4) : 0 ≤ T b := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ (dχ b) (0 : Space))
  have hA : 0 ≤ A := add_nonneg hS (Finset.sum_nonneg (fun b _ => hT b))
  have hSA : S ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (fun b _ => hT b))
  have hM (u : CompactMatrixTest ι) : ‖M u‖ ≤ S*‖u‖ :=
    compactScalarMultiplier_norm_le χ (χ.smooth ⊤) S hS (SchwartzMap.norm_le_seminorm ℝ χ) u
  have hMd (b : Fin 4) (u : CompactMatrixTest ι) : ‖compactSchwartzMultiplier (dχ b) u‖ ≤ T b*‖u‖ :=
    compactScalarMultiplier_norm_le (dχ b) ((dχ b).smooth ⊤) (T b) (hT b)
      (SchwartzMap.norm_le_seminorm ℝ (dχ b)) u
  have hA3 : 0 ≤ (3:ℝ)*A := mul_nonneg (by norm_num) hA
  refine ⟨3*A, hA3, fun u => ⟨(hM u).trans ?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (hSA.trans
      (le_mul_of_one_le_left hA (by norm_num))) (norm_nonneg _)
  let E := firstOrderEnergy D u
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hU := norm_le_matrixFirstOrderEnergy u
  have hMu : ‖M u‖ ≤ A*E := (hM u).trans (mul_le_mul hSA hU (norm_nonneg _) hA)
  have hDM (b : Fin 4) : ‖D b (M u)‖ ≤ A*E := by
    have hLeibniz := compactScalarMultiplier_leibniz (ι := ι) (χ : Space → ℂ) (χ.smooth ⊤) b
    change D b * M = M * D b + compactSchwartzMultiplier (dχ b) at hLeibniz
    have hEq : D b (M u) = M (D b u) + compactSchwartzMultiplier (dχ b) u := by
      rw [← Module.End.mul_apply (D b) M, hLeibniz]
      rfl
    have hSum : S + T b ≤ A :=
      add_le_add_left (Finset.single_le_sum (fun j _ => hT j) (Finset.mem_univ b)) S
    rw [hEq]
    calc
      _ ≤ ‖M (D b u)‖ + ‖compactSchwartzMultiplier (dχ b) u‖ := norm_add_le _ _
      _ ≤ S*E + T b*E := add_le_add
        ((hM (D b u)).trans (mul_le_mul_of_nonneg_left (norm_derivative_le_firstOrderEnergy D u b) hS))
        ((hMd b u).trans (mul_le_mul_of_nonneg_left hU (hT b)))
      _ = (S + T b)*E := by ring
      _ ≤ A*E := mul_le_mul_of_nonneg_right hSum hE
  change firstOrderEnergy D (M u) ≤ 3*A*E
  unfold firstOrderEnergy
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hA3 hE)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  have hBnd : ‖M u‖^2 + ∑ b, ‖D b (M u)‖^2 ≤ (A*E)^2 + ∑ _b : Fin 4, (A*E)^2 :=
    add_le_add (pow_le_pow_left₀ (norm_nonneg _) hMu 2)
      (Finset.sum_le_sum (fun b _ => pow_le_pow_left₀ (norm_nonneg _) (hDM b) 2))
  apply hBnd.trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  nlinarith only [sq_nonneg (A*E)]

end Burnett.Analysis.CarlesonEmbedding
