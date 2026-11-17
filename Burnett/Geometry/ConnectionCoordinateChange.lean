import Burnett.Geometry.LeviCivitaUniqueness
import Mathlib.Tactic.NoncommRing

/-!
# Affine second-jet transformation of connection coefficients

A maps new coordinate vectors to old ones. H has one old upper and two new
lower indices and supplies the nonlinear second-derivative contribution.
The transformed jet is the three-term metric differentiation formula.
Metric compatibility, zero torsion and the Christoffel identity are proved
for these explicit arrays. Their identification with derivatives of actual
chart maps, and the global Levi-Civita construction, are separate tasks.
Every inverse inside a Christoffel argument is explicitly a MATRIX inverse;
no entrywise inverse of the definitionally equal Tensor2 function is used.
-/

noncomputable section
namespace Burnett.Geometry.ConnectionCoordinateChange
open Matrix
open scoped BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

def transformedConnectionMatrix (A K H : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  A⁻¹ * (K * A + H)

def transformedMetricDerivative (A G J H : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  Hᵀ * G * A + Aᵀ * J * A + Aᵀ * G * H

theorem transformed_metric_compatible (A G J K H : Matrix Index Index ℝ)
    (hA : IsUnit A) (hc : Kᵀ * G + G * K = J) :
    (transformedConnectionMatrix A K H)ᵀ * (Aᵀ * G * A) +
      (Aᵀ * G * A) * transformedConnectionMatrix A K H =
        transformedMetricDerivative A G J H := by
  have ha : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hr : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ha
  have ht : (A⁻¹)ᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hr]; simp
  unfold transformedConnectionMatrix transformedMetricDerivative
  calc
    _ = ((K * A + H)ᵀ * ((A⁻¹)ᵀ * Aᵀ)) * G * A +
        (Aᵀ * G) * (A * A⁻¹) * (K * A + H) := by
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = (K * A + H)ᵀ * G * A + Aᵀ * G * (K * A + H) := by rw [ht, hr]; simp
    _ = Hᵀ * G * A + Aᵀ * (Kᵀ * G + G * K) * A + Aᵀ * G * H := by
      simp only [Matrix.transpose_add, Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [hc]

def connectionMatrix (Γ : Connection) (b : Index) : Matrix Index Index ℝ :=
  fun a c => Γ a b c

theorem matrix_metric_compatible_iff (G : Matrix Index Index ℝ) (J : FirstJet) (Γ : Connection) :
    (∀ b c d, covariantJet Γ G J b c d = 0) ↔
      ∀ b, (connectionMatrix Γ b)ᵀ * G + G * connectionMatrix Γ b = J b := by
  constructor
  · intro h b
    ext c d
    have hh := h b c d
    simp only [covariantJet] at hh
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix]
    have heq : (∑ e, G c e * Γ e b d) = ∑ e, Γ e b d * G c e := by
      apply Finset.sum_congr rfl
      intro e he
      ring
    rw [heq]
    nlinarith [hh]
  · intro h b c d
    have hh := congrArg (fun A : Matrix Index Index ℝ => A c d) (h b)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix] at hh
    have heq : (∑ e, G c e * Γ e b d) = ∑ e, Γ e b d * G c e := by
      apply Finset.sum_congr rfl
      intro e he
      ring
    rw [heq] at hh
    simp only [covariantJet]
    nlinarith [hh]

def directionalConnection (A : Matrix Index Index ℝ) (Γ : Connection) (b : Index) :
    Matrix Index Index ℝ := ∑ p, A p b • connectionMatrix Γ p

def transformedConnection (A : Matrix Index Index ℝ) (Γ H : Connection) : Connection :=
  fun a b c => transformedConnectionMatrix A (directionalConnection A Γ b)
    (connectionMatrix H b) a c

def transformedJet (A G : Matrix Index Index ℝ) (J : FirstJet) (H : Connection) : FirstJet :=
  fun b => transformedMetricDerivative A G (∑ p, A p b • (J p : Matrix Index Index ℝ))
    (connectionMatrix H b)

theorem directional_metric_compatible (A G : Matrix Index Index ℝ) (J : FirstJet)
    (Γ : Connection) (hc : ∀ b c d, covariantJet Γ G J b c d = 0) (b : Index) :
    (directionalConnection A Γ b)ᵀ * G + G * directionalConnection A Γ b =
      ∑ p, A p b • (J p : Matrix Index Index ℝ) := by
  have hm := (matrix_metric_compatible_iff G J Γ).mp hc
  unfold directionalConnection
  calc
    _ = ∑ p, A p b • ((connectionMatrix Γ p)ᵀ * G + G * connectionMatrix Γ p) := by
      simp only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul,
        Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_add, Finset.sum_add_distrib]
    _ = _ := by simp only [hm]

theorem transformed_connection_metric_compatible (A G : Matrix Index Index ℝ)
    (J : FirstJet) (Γ H : Connection) (hA : IsUnit A)
    (hc : ∀ b c d, covariantJet Γ G J b c d = 0) :
    ∀ b c d, covariantJet (transformedConnection A Γ H) (Aᵀ * G * A)
      (transformedJet A G J H) b c d = 0 := by
  apply (matrix_metric_compatible_iff _ _ _).mpr
  intro b
  exact transformed_metric_compatible A G _ _ _ hA (directional_metric_compatible A G J Γ hc b)

theorem directional_torsion_free (A : Matrix Index Index ℝ) (Γ : Connection)
    (ht : ∀ a b c, Γ a b c = Γ a c b) (d b c : Index) :
    (directionalConnection A Γ b * A) d c = (directionalConnection A Γ c * A) d b := by
  simp only [directionalConnection, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, connectionMatrix, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [ht d j i]
  ring

theorem transformed_connection_torsion_free (A : Matrix Index Index ℝ) (Γ H : Connection)
    (ht : ∀ a b c, Γ a b c = Γ a c b) (hH : ∀ a b c, H a b c = H a c b) :
    ∀ a b c, transformedConnection A Γ H a b c = transformedConnection A Γ H a c b := by
  intro a b c
  change (∑ d, A⁻¹ a d * ((directionalConnection A Γ b * A) d c + H d b c)) =
    ∑ d, A⁻¹ a d * ((directionalConnection A Γ c * A) d b + H d c b)
  apply Finset.sum_congr rfl
  intro d hd
  rw [directional_torsion_free A Γ ht d b c]
  rw [hH d b c]

theorem transformed_connection_unique (A G GNewInv : Matrix Index Index ℝ)
    (J : FirstJet) (Γ H : Connection) (hA : IsUnit A) (hg : IsSymmetricTensor G)
    (hi : ∀ a e, (∑ d, GNewInv a d * (Aᵀ * G * A) d e) = if a = e then 1 else 0)
    (ht : ∀ a b c, Γ a b c = Γ a c b) (hH : ∀ a b c, H a b c = H a c b)
    (hc : ∀ b c d, covariantJet Γ G J b c d = 0) :
    transformedConnection A Γ H = christoffel GNewInv (transformedJet A G J H) := by
  have hgt : Gᵀ = G := by ext i j; exact hg j i
  have hnew : (Aᵀ * G * A)ᵀ = Aᵀ * G * A := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hgt, Matrix.mul_assoc]
  exact LeviCivitaUniqueness.eq_christoffel_of_torsion_free_metric_compatible
    _ GNewInv _ _ (fun i j => congrArg (fun Q : Matrix Index Index ℝ => Q j i) hnew) hi
    (transformed_connection_torsion_free A Γ H ht hH)
    (transformed_connection_metric_compatible A G J Γ H hA hc)

theorem transformed_connection_unique_inverse (A G : Matrix Index Index ℝ)
    (J : FirstJet) (Γ H : Connection) (hA : IsUnit A) (hG : IsUnit G)
    (hg : IsSymmetricTensor G) (ht : ∀ a b c, Γ a b c = Γ a c b)
    (hH : ∀ a b c, H a b c = H a c b)
    (hc : ∀ b c d, covariantJet Γ G J b c d = 0) :
    transformedConnection A Γ H =
      christoffel ((Aᵀ * G * A)⁻¹ : Matrix Index Index ℝ) (transformedJet A G J H) := by
  have ha := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hgd := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hdet : IsUnit (Aᵀ * G * A).det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using (ha.mul hgd).mul ha
  apply transformed_connection_unique A G _ J Γ H hA hg _ ht hH hc
  intro a e
  have hh := congrArg (fun Q : Matrix Index Index ℝ => Q a e)
    (Matrix.nonsing_inv_mul (Aᵀ * G * A) hdet)
  simpa only [Matrix.mul_apply, Matrix.one_apply] using hh

theorem transformed_christoffel (A G : Matrix Index Index ℝ) (J : FirstJet)
    (H : Connection) (hA : IsUnit A) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (hJ : ∀ d, IsSymmetricTensor (J d)) (hH : ∀ a b c, H a b c = H a c b) :
    transformedConnection A (christoffel (G⁻¹ : Matrix Index Index ℝ) J) H =
      christoffel ((Aᵀ * G * A)⁻¹ : Matrix Index Index ℝ) (transformedJet A G J H) := by
  have hgd := (Matrix.isUnit_iff_isUnit_det G).mp hG
  apply transformed_connection_unique_inverse A G J _ H hA hG hg
    (christoffel_torsion_free _ _ hJ) hH
  apply christoffel_metric_compatible _ _ _ hg hJ
  intro a e
  have hh := congrArg (fun Q : Matrix Index Index ℝ => Q a e)
    (Matrix.mul_nonsing_inv G hgd)
  simpa only [Matrix.mul_apply, Matrix.one_apply] using hh

end Burnett.Geometry.ConnectionCoordinateChange
