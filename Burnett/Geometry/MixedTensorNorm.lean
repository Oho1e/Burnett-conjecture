import Burnett.Geometry.CovariantTensorNorm
import Burnett.Geometry.ConnectionError
import Burnett.Geometry.InverseField

/-!
# The physical norm of a tensor with one upper and two lower indices

The index order is upper a, lower b,c. The Gram is (R tensor R-inverse)
tensor R-inverse for a positive covariant metric R. Existing array norms
are the coordinate Pi sup norms, never operator or physical Hilbert norms.
-/

noncomputable section

namespace Burnett.Geometry.MixedTensorNorm

open Matrix
open scoped BigOperators Kronecker Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.GramCoordinateBound
open Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.ConnectionError

/-- The upper slot uses R; the two lower slots use its actual matrix inverse. -/
def mixedGram (R : Matrix Index Index ℝ) :
    Matrix ((Index × Index) × Index) ((Index × Index) × Index) ℝ :=
  (R ⊗ₖ (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R)) ⊗ₖ
    (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R)

/-- Full ordered contraction of a genuine (1,2) array E^a_bc. -/
def mixedEnergy (R : Matrix Index Index ℝ) (T : Connection) : ℝ :=
  let S := @Inv.inv (Matrix Index Index ℝ) Matrix.inv R
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    R a d * S b e * S c f * T a b c * T d e f

def mixedNorm (R : Matrix Index Index ℝ) (T : Connection) : ℝ :=
  Real.sqrt (mixedEnergy R T)

theorem mixedGram_posDef (R : Matrix Index Index ℝ) (hR : R.PosDef) :
    (mixedGram R).PosDef :=
  posDef_kronecker _ _ (posDef_kronecker _ _ hR hR.inv) hR.inv

theorem mixedGram_inverse (R : Matrix Index Index ℝ) (hR : R.PosDef) :
    (mixedGram R)⁻¹ =
      ((@Inv.inv (Matrix Index Index ℝ) Matrix.inv R) ⊗ₖ R) ⊗ₖ R := by
  have hi := Matrix.nonsing_inv_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  unfold mixedGram
  rw [Matrix.inv_kronecker, Matrix.inv_kronecker, hi]

theorem mixedEnergy_eq_gramEnergy (R : Matrix Index Index ℝ) (T : Connection) :
    mixedEnergy R T = gramEnergy (mixedGram R) (flatten3 T) := by
  simp only [mixedEnergy, gramEnergy, mixedGram, flatten3, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine Finset.sum_congr rfl (fun e _ => ?_)
  refine Finset.sum_congr rfl (fun f _ => ?_)
  ring

theorem mixedEnergy_nonneg (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : Connection) :
    0 ≤ mixedEnergy R T := by
  rw [mixedEnergy_eq_gramEnergy]
  exact gramEnergy_nonneg _ (mixedGram_posDef R hR).posSemidef _

theorem mixedNorm_nonneg (R : Matrix Index Index ℝ) (T : Connection) :
    0 ≤ mixedNorm R T := Real.sqrt_nonneg _

theorem mixedNorm_sq (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : Connection) :
    mixedNorm R T ^ 2 = mixedEnergy R T := Real.sq_sqrt (mixedEnergy_nonneg R hR T)

theorem mixedNorm_eq_gramNorm (R : Matrix Index Index ℝ) (T : Connection) :
    mixedNorm R T = gramNorm (mixedGram R) (flatten3 T) := by
  simp only [mixedNorm, gramNorm, mixedEnergy_eq_gramEnergy]

theorem mixedNorm_eq_ofMatrix_norm (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : Connection) :
    mixedNorm R T = @Norm.norm (((Index × Index) × Index) → ℝ)
      (Matrix.NormedAddCommGroup.ofMatrix (mixedGram_posDef R hR)).toNorm (flatten3 T) := by
  rw [mixedNorm_eq_gramNorm]
  exact gramNorm_eq_ofMatrix_norm _ (mixedGram_posDef R hR) _

theorem abs_entry_le_mixedNorm (R : Matrix Index Index ℝ) (hR : R.PosDef)
    (T : Connection) (a b c : Index) :
    |T a b c| ≤ Real.sqrt ((@Inv.inv (Matrix Index Index ℝ) Matrix.inv R) a a *
      R b b * R c c) * mixedNorm R T := by
  have h := abs_apply_le_sqrt_inverse_diagonal_mul_gramNorm
    (mixedGram R) (mixedGram_posDef R hR) (flatten3 T) ((a, b), c)
  rw [mixedGram_inverse R hR] at h
  simpa only [Matrix.kronecker_apply, flatten3, ← mixedNorm_eq_gramNorm] using h

theorem coordinate_sup_le_mixedNorm_of_diagonal_bounds
    (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : Connection)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hS : ∀ i, (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R) i i ≤ A)
    (hRdiag : ∀ i, R i i ≤ B) :
    ‖T‖ ≤ Real.sqrt (A * B ^ 2) * mixedNorm R T := by
  apply norm_connection_le_of_entries _ (mul_nonneg (Real.sqrt_nonneg _) (mixedNorm_nonneg _ _))
  intro a b c
  have hp := mul_le_mul (hS a) (hRdiag b) (diagonal_nonneg R hR b) hA
  have hp' := mul_le_mul hp (hRdiag c) (diagonal_nonneg R hR c) (mul_nonneg hA hB)
  have hprod : (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R) a a * R b b * R c c ≤ A * B^2 := by
    nlinarith
  exact (abs_entry_le_mixedNorm R hR T a b c).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hprod) (mixedNorm_nonneg _ _))

/-- Explicit finite coefficient sum; this is not an operator norm or an assumed equivalence. -/
def coefficientSum (R : Matrix Index Index ℝ) : ℝ :=
  let S := @Inv.inv (Matrix Index Index ℝ) Matrix.inv R
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, |R a d * S b e * S c f|

def comparisonCoefficient (R : Matrix Index Index ℝ) : ℝ := Real.sqrt (coefficientSum R)

theorem coefficientSum_nonneg (R : Matrix Index Index ℝ) : 0 ≤ coefficientSum R := by
  unfold coefficientSum
  positivity

theorem mixedEnergy_le_coefficientSum_mul_norm_sq (R : Matrix Index Index ℝ) (T : Connection) :
    mixedEnergy R T ≤ coefficientSum R * ‖T‖ ^ 2 := by
  let S := @Inv.inv (Matrix Index Index ℝ) Matrix.inv R
  calc
    mixedEnergy R T ≤ ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
        |R a d * S b e * S c f| * ‖T‖^2 := by
      unfold mixedEnergy
      apply Finset.sum_le_sum; intro a ha
      apply Finset.sum_le_sum; intro b hb
      apply Finset.sum_le_sum; intro c hc
      apply Finset.sum_le_sum; intro d hd
      apply Finset.sum_le_sum; intro e he
      apply Finset.sum_le_sum; intro f hf
      have hT : |T a b c * T d e f| ≤ ‖T‖^2 := by
        rw [abs_mul, pow_two]
        exact mul_le_mul (abs_firstJet_entry_le_norm T a b c)
          (abs_firstJet_entry_le_norm T d e f) (abs_nonneg _) (norm_nonneg _)
      calc
        _ ≤ |R a d * S b e * S c f * T a b c * T d e f| := le_abs_self _
        _ = |R a d * S b e * S c f| * |T a b c * T d e f| := by
          simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hT (abs_nonneg _)
    _ = coefficientSum R * ‖T‖^2 := by simp only [coefficientSum, S, Finset.sum_mul]

theorem mixedNorm_le_comparisonCoefficient_mul_norm (R : Matrix Index Index ℝ) (T : Connection) :
    mixedNorm R T ≤ comparisonCoefficient R * ‖T‖ := by
  calc
    mixedNorm R T ≤ Real.sqrt (coefficientSum R * ‖T‖^2) :=
      Real.sqrt_le_sqrt (mixedEnergy_le_coefficientSum_mul_norm_sq R T)
    _ = comparisonCoefficient R * ‖T‖ := by
      rw [Real.sqrt_mul (coefficientSum_nonneg R), Real.sqrt_sq (norm_nonneg T)]
      rfl


section Continuous
variable {X : Type*} [TopologicalSpace X]

theorem continuousOn_inverse (R : X → Matrix Index Index ℝ) (K : Set X)
    (hc : ContinuousOn R K) (hR : ∀ x ∈ K, (R x).PosDef) :
    ContinuousOn (fun x => @Inv.inv (Matrix Index Index ℝ) Matrix.inv (R x)) K := by
  simpa only [Burnett.Geometry.InverseField.matrixInverse] using
    Burnett.Geometry.InverseField.continuousOn_matrixInverse R K hc
      (fun x hx => ne_of_gt (hR x hx).det_pos)

theorem continuousOn_comparisonCoefficient (R : X → Matrix Index Index ℝ) (K : Set X)
    (hc : ContinuousOn R K) (hR : ∀ x ∈ K, (R x).PosDef) :
    ContinuousOn (fun x => comparisonCoefficient (R x)) K := by
  have hi := continuousOn_inverse R K hc hR
  have hRc (a d : Index) := continuousOn_pi.mp (continuousOn_pi.mp hc a) d
  have hSc (b e : Index) := continuousOn_pi.mp (continuousOn_pi.mp hi b) e
  have hs : ContinuousOn (fun x => coefficientSum (R x)) K := by
    unfold coefficientSum
    refine continuousOn_finset_sum Finset.univ (fun a _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun b _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun c _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun d _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun e _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun f _ => ?_)
    exact (((hRc a d).mul (hSc b e)).mul (hSc c f)).abs
  exact hs.sqrt

/-- Continuity of the actual variable-metric scalar norm. The inverse
continuity is derived from R, not supplied as a separate premise. -/
theorem continuousOn_mixedNorm (R : X → Matrix Index Index ℝ) (T : X → Connection)
    (K : Set X) (hc : ContinuousOn R K) (hT : ContinuousOn T K)
    (hR : ∀ x ∈ K, (R x).PosDef) :
    ContinuousOn (fun x => mixedNorm (R x) (T x)) K := by
  have hi := continuousOn_inverse R K hc hR
  have hRc (a d : Index) := continuousOn_pi.mp (continuousOn_pi.mp hc a) d
  have hSc (b e : Index) := continuousOn_pi.mp (continuousOn_pi.mp hi b) e
  have hTc (a b c : Index) :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hT a) b) c
  have hs : ContinuousOn (fun x => mixedEnergy (R x) (T x)) K := by
    unfold mixedEnergy
    refine continuousOn_finset_sum Finset.univ (fun a _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun b _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun c _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun d _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun e _ => ?_)
    refine continuousOn_finset_sum Finset.univ (fun f _ => ?_)
    exact (((((hRc a d).mul (hSc b e)).mul (hSc c f)).mul (hTc a b c)).mul (hTc d e f))
  exact hs.sqrt

/-- One actual comparison constant works for every point and every mixed
array on K. No norm-equivalence constant or inverse bound is an input. -/
theorem exists_uniform_mixedNorm_control
    (R : X → Matrix Index Index ℝ) (K : Set X) (hK : IsCompact K)
    (hc : ContinuousOn R K) (hR : ∀ x ∈ K, (R x).PosDef) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : Connection, mixedNorm (R x) T ≤ C * ‖T‖ := by
  obtain ⟨C, hC, hb⟩ := (hK.image_of_continuousOn
    (continuousOn_comparisonCoefficient R K hc hR)).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x hx T => ?_⟩
  have hcoeff : comparisonCoefficient (R x) ≤ C :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb _ (Set.mem_image_of_mem _ hx))
  exact (mixedNorm_le_comparisonCoefficient_mul_norm (R x) T).trans
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))

/-- The reverse compact comparison uses the inverse Gram diagonal, whose
upper-index factor is R-inverse and whose lower-index factors are R. -/
theorem exists_uniform_coordinate_control
    (R : X → Matrix Index Index ℝ) (K : Set X) (hK : IsCompact K)
    (hc : ContinuousOn R K) (hR : ∀ x ∈ K, (R x).PosDef) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : Connection, ‖T‖ ≤ C * mixedNorm (R x) T := by
  have hi := continuousOn_inverse R K hc hR
  have hdR : ContinuousOn (fun x i => R x i i) K :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mp (continuousOn_pi.mp hc i) i)
  have hdS : ContinuousOn
      (fun x i => (@Inv.inv (Matrix Index Index ℝ) Matrix.inv (R x)) i i) K :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mp (continuousOn_pi.mp hi i) i)
  obtain ⟨A, hA, hbA⟩ := (hK.image_of_continuousOn hdS).isBounded.exists_pos_norm_le
  obtain ⟨B, hB, hbB⟩ := (hK.image_of_continuousOn hdR).isBounded.exists_pos_norm_le
  refine ⟨Real.sqrt (A * B^2), Real.sqrt_pos.mpr (mul_pos hA (pow_pos hB _)), ?_⟩
  intro x hx T
  apply coordinate_sup_le_mixedNorm_of_diagonal_bounds (R x) (hR x hx) T hA.le hB.le
  · intro i
    have h := (norm_le_pi_norm (fun i => (@Inv.inv (Matrix Index Index ℝ) Matrix.inv (R x)) i i) i).trans
      (hbA _ (Set.mem_image_of_mem _ hx))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)
  · intro i
    have h := (norm_le_pi_norm (fun i => R x i i) i).trans (hbB _ (Set.mem_image_of_mem _ hx))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)

end Continuous

end Burnett.Geometry.MixedTensorNorm
