import Burnett.Analysis.PrincipalEnergy.Localization.GlobalSmoothCoefficientL2
import Burnett.Analysis.PrincipalEnergy.Commutator.SchwartzCoordinateJet

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped NNReal ComplexConjugate ContDiff BigOperators InnerProductSpace

/-- The actual commutator pairing for a compact input and a general smooth
coefficient. -/
def smoothMatrixCoefficientPair {ι : Type*} [Fintype ι] (a : ι → ι → Space → Space → ℂ)
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (f : ι → SchwartzMap Space ℂ)
    (hf : ∀ i, HasCompactSupport (f i : Space → ℂ)) (g : ι → SchwartzMap Space ℂ) : ℂ :=
  ∑ i, ∫ x, conj (g i x) * smoothMatrixCoefficientCommutator a r hr f hf i x

theorem coordinateSchwartzDerivative_support_subset (f : SchwartzMap Space ℂ) (b : Fin 4) :
    tsupport (SchwartzMap.pderivCLM ℂ (coordinateDirection b) f : Space → ℂ) ⊆
      tsupport (f : Space → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply support_fderiv_subset ℝ
  intro hz
  apply hx
  change fderiv ℝ (f : Space → ℂ) x (coordinateDirection b) = 0
  rw [hz, ContinuousLinearMap.zero_apply]

theorem matrixCoordinateL2_le_coordinateJet {ι : Type*} [Fintype ι]
    (u : ι → SchwartzMap Space ℂ) (b : Fin 4) :
    matrixSchwartzL2Norm (fun i => SchwartzMap.pderivCLM ℂ (coordinateDirection b) (u i)) ≤
      ‖WithLp.toLp 2 (fun i => schwartzCoordinateJet (u i))‖ := by
  unfold matrixSchwartzL2Norm
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  change ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection b) (u i)).toLp 2 volume‖ ≤
    ‖schwartzCoordinateJet (u i)‖
  rw [← schwartzCoordinateJet_succ_component]
  exact PiLp.norm_apply_le (schwartzCoordinateJet (u i)) b.succ

/-- All actual middle commutator pairings from the coordinate decomposition
use one support-independent constant and the full coordinate H¹ jet. -/
theorem exists_matrix_coordinate_middleTerm_global_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a)
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : Fin 4 → Fin 4 → Space → ℂ) (hr : ∀ b d, ContDiff ℝ ∞ (r b d))
        (U : Fin 4 → Fin 4 → ℝ) (L : Fin 4 → Fin 4 → NNReal),
        (∀ b d x, conj (r b d x) = r b d x) →
        (∀ b d, ∀ᵐ x ∂(volume : Measure Space), ‖r b d x‖ ≤ U b d) →
        (∀ b d, ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r b d) x‖ ≤ (L b d : ℝ)) →
        ∀ (u : ι → SchwartzMap Space ℂ) (hu : ∀ i, HasCompactSupport (u i : Space → ℂ)),
          let DU (b : Fin 4) (i : ι) := SchwartzMap.pderivCLM ℂ (coordinateDirection b) (u i)
          let hDU (b : Fin 4) (i : ι) : HasCompactSupport (DU b i : Space → ℂ) :=
            (hu i).of_isClosed_subset isClosed_closure (coordinateSchwartzDerivative_support_subset (u i) b)
          ‖∑ b, ∑ d, smoothMatrixCoefficientPair a (r b d) (hr b d) (DU d) (hDU d) (DU b)‖ ≤
            C * (∑ b, ∑ d, (U b d + (L b d : ℝ))) *
              ‖WithLp.toLp 2 (fun i => schwartzCoordinateJet (u i))‖^2 := by
  obtain ⟨C, hC, bound⟩ := exists_smoothMatrixCoefficientCommutator_global_L2_bound ha hs hb hSym hProper
  refine ⟨C, hC, ?_⟩
  intro r hr U L hReal hU hL u hu DU hDU
  let H := ‖WithLp.toLp 2 (fun i => schwartzCoordinateJet (u i))‖
  have hH : 0 ≤ H := norm_nonneg _
  let P (b d : Fin 4) := smoothMatrixCoefficientPair a (r b d) (hr b d) (DU d) (hDU d) (DU b)
  have hP (b d : Fin 4) : ‖P b d‖ ≤ C * (U b d + (L b d : ℝ)) * H^2 := by
    obtain ⟨hT, hTbound⟩ := bound (r b d) (hr b d) (L b d) (U b d)
      (hReal b d) (hU b d) (hL b d) (DU d) (hDU d)
    let T : PiLp 2 (fun _ : ι => ComplexL2 Space) :=
      WithLp.toLp 2 (fun i => (hT i).toLp (smoothMatrixCoefficientCommutator a (r b d) (hr b d) (DU d) (hDU d) i))
    let G : PiLp 2 (fun _ : ι => ComplexL2 Space) := WithLp.toLp 2 (fun i => (DU b i).toLp 2 volume)
    have hp : ⟪G, T⟫_ℂ = P b d := by
      unfold P smoothMatrixCoefficientPair
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(DU b i).coeFn_toLp 2 volume, MemLp.coeFn_toLp (hT i)] with x hg hx
      change inner ℂ (((DU b i).toLp 2 volume) x) (((hT i).toLp _) x) = _
      rw [hg, hx, RCLike.inner_apply']
    have hDUb : ‖G‖ ≤ H := matrixCoordinateL2_le_coordinateJet u b
    have hDUd : matrixSchwartzL2Norm (DU d) ≤ H := matrixCoordinateL2_le_coordinateJet u d
    obtain ⟨hU₀, _, _⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative (r b d) ((hr b d).of_le (by simp))
      (U b d) (L b d) (hU b d) (hL b d)
    have hCoef : 0 ≤ C * (U b d + (L b d : ℝ)) := mul_nonneg hC (add_nonneg hU₀ (L b d).coe_nonneg)
    calc
      _ = ‖⟪G,T⟫_ℂ‖ := by rw [hp]
      _ ≤ ‖G‖ * ‖T‖ := norm_inner_le_norm _ _
      _ ≤ H * (C * (U b d + (L b d : ℝ)) * matrixSchwartzL2Norm (DU d)) :=
        mul_le_mul hDUb hTbound (norm_nonneg _) hH
      _ ≤ H * (C * (U b d + (L b d : ℝ)) * H) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDUd hCoef) hH
      _ = _ := by ring
  change ‖∑ b, ∑ d, P b d‖ ≤ _
  calc
    _ ≤ ∑ b, ‖∑ d, P b d‖ := norm_sum_le _ _
    _ ≤ ∑ b, ∑ d, ‖P b d‖ := Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ b, ∑ d, C * (U b d + (L b d : ℝ)) * H^2 :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun d _ => hP b d))
    _ = _ := by simp only [← Finset.sum_mul, ← Finset.mul_sum, H]

end Burnett.Analysis.CarlesonEmbedding
