import Mathlib.Analysis.CStarAlgebra.Basic

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace Burnett.Analysis.CotlarStein

variable {ι A : Type*} [NormedRing A] [NormOneClass A] [StarRing A] [NormedStarGroup A]

def letter (T : ι → A) (parity : Bool) (i : ι) : A :=
  if parity then star (T i) else T i

def alternatingProduct (T : ι → A) : Bool → List ι → A
  | _, [] => 1
  | b, i :: t => letter T b i * alternatingProduct T (!b) t

def pairedWeight (w : ι → ι → ℝ) : List ι → ℝ
  | i :: j :: t => w i j * pairedWeight w t
  | _ => 1

def pathWeight (w : ι → ι → ℝ) : List ι → ℝ
  | i :: j :: t => w i j * pathWeight w (j :: t)
  | _ => 1

def endpointWeight (M : ℝ) : List ι → ℝ
  | [] => 1
  | [_] => M
  | _ :: _ :: t => endpointWeight M t

private theorem pairedWeight_nonneg (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    ∀ t, 0 ≤ pairedWeight w t
  | [] => zero_le_one
  | [_] => zero_le_one
  | i :: j :: t => mul_nonneg (hw i j) (pairedWeight_nonneg w hw t)

private theorem endpointWeight_nonneg (M : ℝ) (hM : 0 ≤ M) :
    ∀ t : List ι, 0 ≤ endpointWeight M t
  | [] => zero_le_one
  | [_] => hM
  | _ :: _ :: t => endpointWeight_nonneg M hM t

private theorem endpointWeight_cons_mul (M : ℝ) :
    ∀ (i : ι) (t : List ι), endpointWeight M (i :: t) * endpointWeight M t = M
  | _, [] => by simp [endpointWeight]
  | i, j :: t => by
      change endpointWeight M t * endpointWeight M (j :: t) = M
      rw [mul_comm, endpointWeight_cons_mul M j t]

theorem pathWeight_eq_pair_split (w : ι → ι → ℝ) :
    ∀ (i : ι) (t : List ι), pathWeight w (i :: t) = pairedWeight w (i :: t) * pairedWeight w t
  | _, [] => by simp [pathWeight,pairedWeight]
  | i, j :: t => by
      change w i j * pathWeight w (j :: t) =
        (w i j * pairedWeight w t) * pairedWeight w (j :: t)
      rw [pathWeight_eq_pair_split w j t]
      ring

private theorem pair_norm_bound (T : ι → A) (w : ι → ι → ℝ)
    (h₁ : ∀ i j, ‖star (T i) * T j‖ ≤ (w i j)^2)
    (h₂ : ∀ i j, ‖T i * star (T j)‖ ≤ (w i j)^2) (b : Bool) (i j : ι) :
    ‖letter T b i * letter T (!b) j‖ ≤ (w i j)^2 := by
  cases b
  · exact h₂ i j
  · exact h₁ i j

private theorem single_norm_bound (T : ι → A) (M : ℝ) (hT : ∀ i, ‖T i‖ ≤ M)
    (b : Bool) (i : ι) : ‖letter T b i‖ ≤ M := by
  cases b <;> simpa only [letter,Bool.false_eq_true,if_false,if_true,norm_star] using hT i

private theorem alternatingProduct_paired_bound (T : ι → A) (w : ι → ι → ℝ)
    (h₁ : ∀ i j, ‖star (T i) * T j‖ ≤ (w i j)^2)
    (h₂ : ∀ i j, ‖T i * star (T j)‖ ≤ (w i j)^2)
    (M : ℝ) (hT : ∀ i, ‖T i‖ ≤ M) :
    ∀ (b : Bool) (t : List ι), ‖alternatingProduct T b t‖ ≤ endpointWeight M t*(pairedWeight w t)^2
  | _, [] => by simp [alternatingProduct,endpointWeight,pairedWeight]
  | b, [i] => by
      simpa only [alternatingProduct,endpointWeight,pairedWeight,mul_one,one_pow] using single_norm_bound T M hT b i
  | b, i :: j :: t => by
      simp only [alternatingProduct, Bool.not_not, ← mul_assoc, endpointWeight, pairedWeight]
      exact (norm_mul_le _ _).trans ((mul_le_mul
        (pair_norm_bound T w h₁ h₂ b i j) (alternatingProduct_paired_bound T w h₁ h₂ M hT b t)
        (norm_nonneg _) (sq_nonneg _)).trans_eq (by ring))

/-- Cotlar's two pairings of a single nonempty alternating word. -/
theorem alternatingProduct_path_bound (T : ι → A) (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (h₁ : ∀ i j, ‖star (T i) * T j‖ ≤ (w i j)^2)
    (h₂ : ∀ i j, ‖T i * star (T j)‖ ≤ (w i j)^2)
    (M : ℝ) (hM : 0 ≤ M) (hT : ∀ i, ‖T i‖ ≤ M) (b : Bool) (i : ι) (t : List ι) :
    ‖alternatingProduct T b (i :: t)‖ ≤ M * pathWeight w (i :: t) := by
  have hA := alternatingProduct_paired_bound T w h₁ h₂ M hT b (i :: t)
  have hB : ‖alternatingProduct T b (i :: t)‖ ≤ M*(endpointWeight M t*(pairedWeight w t)^2) := by
    change ‖letter T b i * alternatingProduct T (!b) t‖ ≤ _
    exact (norm_mul_le _ _).trans (mul_le_mul (single_norm_bound T M hT b i)
      (alternatingProduct_paired_bound T w h₁ h₂ M hT (!b) t) (norm_nonneg _) hM)
  rw [pathWeight_eq_pair_split]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM
    (mul_nonneg (pairedWeight_nonneg w hw (i :: t)) (pairedWeight_nonneg w hw t)))).mp
  rw [pow_two]
  refine (mul_le_mul hA hB (norm_nonneg _) (mul_nonneg (endpointWeight_nonneg M hM _) (sq_nonneg _))).trans_eq ?_
  calc
    _ = (M * (endpointWeight M (i :: t)*endpointWeight M t)) *
        ((pairedWeight w (i :: t))^2*(pairedWeight w t)^2) := by ring
    _ = _ := by rw [endpointWeight_cons_mul]; ring

end Burnett.Analysis.CotlarStein
