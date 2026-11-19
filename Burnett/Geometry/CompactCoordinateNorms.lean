import Burnett.Geometry.IntrinsicDhMeasure
import Burnett.Geometry.ManifoldMetricSequence

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Burnett.Geometry.AuxiliaryAdmissibility

open Set Matrix Filter MeasureTheory
open Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open Burnett.Geometry.CovariantTensorNorm Burnett.Geometry.GramCoordinateBound
open scoped ContDiff Manifold Kronecker Topology ENNReal

private theorem gramNorm_le_of_entry_bound {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (v : ι → ℝ) {A : ℝ} (hA : 0 ≤ A) (hG : ∀ i j, |G i j| ≤ A) :
    gramNorm G v ≤ (Fintype.card ι * Real.sqrt A) * ‖v‖ := by
  have hC : (0 : ℝ) ≤ Fintype.card ι * Real.sqrt A := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hentry (i : ι) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hm (i j : ι) : v i * (G i j * v j) ≤ ‖v‖ * (A * ‖v‖) := by
    calc
      _ ≤ |v i * (G i j * v j)| := le_abs_self _
      _ = |v i| * (|G i j| * |v j|) := by simp only [abs_mul]
      _ ≤ _ := mul_le_mul (hentry i) (mul_le_mul (hG i j) (hentry j) (abs_nonneg _) hA)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have hsum : gramEnergy G v ≤ (Fintype.card ι : ℝ)^2 * A * ‖v‖^2 := by
    unfold gramEnergy
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    calc
      _ ≤ ∑ _i : ι, ∑ _j : ι, ‖v‖ * (A * ‖v‖) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hm i j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hsq : (Fintype.card ι : ℝ)^2 * A * ‖v‖^2 =
      ((Fintype.card ι * Real.sqrt A) * ‖v‖)^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA]
  unfold gramNorm
  rw [hsq] at hsum
  exact (Real.sqrt_le_sqrt hsum).trans_eq (Real.sqrt_sq (mul_nonneg hC (norm_nonneg _)))

private theorem exists_uniform_gramNorm_upper {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (G : X → Matrix ι ι ℝ) (K : Set X) (hK : IsCompact K) (hG : ContinuousOn G K) :
    ∃ C > 0, ∀ x ∈ K, ∀ v : ι → ℝ, gramNorm (G x) v ≤ C * ‖v‖ := by
  let P : X → ι → ι → ℝ := fun x i j => G x i j
  have hP : ContinuousOn P K := hG
  obtain ⟨A, hA, hb⟩ := (hK.image_of_continuousOn hP).isBounded.exists_pos_norm_le
  let C := (Fintype.card ι : ℝ) * Real.sqrt A
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨C + 1, by linarith, ?_⟩
  intro x hx v
  have hEntries (i j : ι) : |G x i j| ≤ A := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (P x i) j).trans
      ((norm_le_pi_norm (P x) i).trans (hb _ (mem_image_of_mem _ hx)))
  exact (gramNorm_le_of_entry_bound (G x) v hA.le hEntries).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))

private theorem norm_flatten2_le (T : Tensor2) : ‖flatten2 T‖ ≤ ‖T‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).mpr
  intro ij
  exact (norm_le_pi_norm (T ij.1) ij.2).trans (norm_le_pi_norm T ij.1)

private theorem norm_flatten3_le (T : FirstJet) : ‖flatten3 T‖ ≤ ‖T‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).mpr
  intro ijk
  exact (norm_le_pi_norm (T ijk.1.1 ijk.1.2) ijk.2).trans
    ((norm_le_pi_norm (T ijk.1.1) ijk.1.2).trans (norm_le_pi_norm T ijk.1.1))

private theorem continuousOn_gram2 {X : Type*} [TopologicalSpace X]
    (R : X → Tensor2) (K : Set X) (hR : ContinuousOn (fun x => InverseField.matrixInverse (R x)) K) :
    ContinuousOn (fun x => gram2 (R x)) K := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have h (a b : Index) := continuousOn_pi.mp (continuousOn_pi.mp hR a) b
  simpa only [gram2, Matrix.kronecker_apply, InverseField.matrixInverse] using
    (h i.1 j.1).mul (h i.2 j.2)

private theorem continuousOn_gram3 {X : Type*} [TopologicalSpace X]
    (R : X → Tensor2) (K : Set X) (hR : ContinuousOn (fun x => InverseField.matrixInverse (R x)) K) :
    ContinuousOn (fun x => gram3 (R x)) K := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have h (a b : Index) := continuousOn_pi.mp (continuousOn_pi.mp hR a) b
  have h2 := continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_gram2 R K hR) i.1) j.1
  simpa only [gram3, Matrix.kronecker_apply, InverseField.matrixInverse] using h2.mul (h i.2 j.2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem coordinateMetric_inverse_continuousOn (r : Metric (M := M)) (c : M) :
    ContinuousOn (fun x => InverseField.matrixInverse (metricComponents (coordinateMetric r c) x))
      (chartAt CoordinateSpace c).target := by
  apply InverseField.continuousOn_matrixInverse
  · exact ManifoldBilinear.continuousOn_components r.inner (ManifoldBilinear.isSmooth_inner r) c
  · intro y hy
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero r.inner
      (GlobalLeviCivita.inner_nondegenerate r) c hy

theorem exists_chart_norm2_upper (r : Metric (M := M)) (c : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : Tensor2, norm2 (metricComponents (coordinateMetric r c) x) T ≤ C * ‖T‖ := by
  let R := metricComponents (coordinateMetric r c)
  obtain ⟨C, hC, hb⟩ := exists_uniform_gramNorm_upper (fun x => gram2 (R x)) K hK
    (continuousOn_gram2 R K ((coordinateMetric_inverse_continuousOn r c).mono hKt))
  refine ⟨C, hC, ?_⟩
  intro x hx T
  rw [norm2_eq_gramNorm]
  exact (hb x hx (flatten2 T)).trans (mul_le_mul_of_nonneg_left (norm_flatten2_le T) hC.le)

theorem exists_chart_norm3_upper (r : Metric (M := M)) (c : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : FirstJet, norm3 (metricComponents (coordinateMetric r c) x) T ≤ C * ‖T‖ := by
  let R := metricComponents (coordinateMetric r c)
  obtain ⟨C, hC, hb⟩ := exists_uniform_gramNorm_upper (fun x => gram3 (R x)) K hK
    (continuousOn_gram3 R K ((coordinateMetric_inverse_continuousOn r c).mono hKt))
  refine ⟨C, hC, ?_⟩
  intro x hx T
  rw [norm3_eq_gramNorm]
  exact (hb x hx (flatten3 T)).trans (mul_le_mul_of_nonneg_left (norm_flatten3_le T) hC.le)

end Burnett.Geometry.AuxiliaryAdmissibility
