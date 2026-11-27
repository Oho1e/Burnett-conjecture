import Burnett.Analysis.CubicEnergy.AngularCorrection.PaperAnalyticCorrectionBounds

set_option autoImplicit false

noncomputable section

namespace Burnett.A08

open MeasureTheory Metric Set Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ComplexConjugate ContDiff ENNReal NNReal BigOperators

local instance finiteMatrixCorrectionOneLeTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance finiteMatrixCorrectionOneLeFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev lp4 (u : Test) : ℝ := ‖u.toLp 4 volume‖
private abbrev grad4 (u : Test) : ℝ := schwartzGradientNorm 4 u

variable {L I J : Type*} [Fintype L] [Fintype I] [Fintype J]

/-- A finite tensor contraction of scalar symbols. The high adjoint exchanges the
input and output component indices. The component sums specify the field norms. -/
structure FiniteMatrixAnalyticCorrectionBounds (b : L → I → J → Joint → ℂ) (C : ℝ) where
  forward : (L → Test) → (J → Test) → I → LP2
  adjoint : (L → Test) → (I → Test) → J → LP2
  forward_pair (H : L → Test) (u : J → Test) (i : I) (w : Test) :
    inner ℂ (w.toLp 2 volume) (forward H u i) = ∑ a, ∑ j, radianHighPair (b a i j) (H a) (u j) w
  adjoint_pair (H : L → Test) (u : I → Test) (j : J) (w : Test) :
    inner ℂ (w.toLp 2 volume) (adjoint H u j) =
      ∑ a, ∑ i, radianHighPair (highAdjointSymbol (b a i j)) (fun x => conj (H a x)) (u i) w
  adjoint_duality (H : L → Test) (u : J → Test) (w : I → Test) :
    ∑ i, inner ℂ ((w i).toLp 2 volume) (forward H u i) =
      ∑ j, inner ℂ (adjoint H w j) ((u j).toLp 2 volume)
  first_order (H : L → Test) (u : J → Test) (w : I → Test) :
    (∀ i, ‖forward H u i‖ ≤ C * (∑ a, lp4 (H a)) * (∑ j, grad4 (u j))) ∧
    (∀ j, ‖adjoint H w j‖ ≤ C * (∑ a, lp4 (H a)) * (∑ i, grad4 (w i)))
  coordinate_commutator (k : Fin 4) (H : L → Test) (u : J → Test) (w : I → Test) (v : Test) :
    (∀ i, -inner ℂ ((coordinateDerivative k v).toLp 2 volume) (forward H u i) -
          inner ℂ (v.toLp 2 volume) (forward H (fun j => coordinateDerivative k (u j)) i) =
        inner ℂ (v.toLp 2 volume) (forward (fun a => coordinateDerivative k (H a)) u i)) ∧
    (∀ j, -inner ℂ ((coordinateDerivative k v).toLp 2 volume) (adjoint H w j) -
          inner ℂ (v.toLp 2 volume) (adjoint H (fun i => coordinateDerivative k (w i)) j) =
        inner ℂ (v.toLp 2 volume) (adjoint (fun a => coordinateDerivative k (H a)) w j))
  derivative_first_order (k : Fin 4) (H : L → Test) (u : J → Test) (w : I → Test) :
    (∀ i, ‖forward (fun a => coordinateDerivative k (H a)) u i‖ ≤
      C * (∑ a, lp4 (coordinateDerivative k (H a))) * (∑ j, grad4 (u j))) ∧
    (∀ j, ‖adjoint (fun a => coordinateDerivative k (H a)) w j‖ ≤
      C * (∑ a, lp4 (coordinateDerivative k (H a))) * (∑ i, grad4 (w i)))
  rough_gradient (d : E → ℝ) {D : ℝ≥0} (_ : LipschitzWith D d)
      (H : L → Test) (u : J → Test) (w : I → Test) :
    ∃ U : I → LP2, ∃ V : J → LP2,
      (∀ i, ‖U i‖ ≤ C * lipschitzGradientLInfty d * (∑ a, lp4 (H a)) * (∑ j, lp4 (u j))) ∧
      (∀ j, ‖V j‖ ≤ C * lipschitzGradientLInfty d * (∑ a, lp4 (H a)) * (∑ i, lp4 (w i))) ∧
      (∀ i (v : Test), inner ℂ (v.toLp 2 volume) (U i) =
        ∑ a, ∑ j, -radianHighCommutatorPair (b a i j) d (H a) (u j) v) ∧
      (∀ j (v : Test), inner ℂ (v.toLp 2 volume) (V j) =
        ∑ a, ∑ i, -radianHighCommutatorPair (highAdjointSymbol (b a i j)) d (fun x => conj (H a x)) (w i) v)

private theorem norm_finite_contraction (terms : L → J → LP2) (C : ℝ) (f : L → ℝ) (g : J → ℝ)
    (h : ∀ a j, ‖terms a j‖ ≤ C * f a * g j) :
    ‖∑ a, ∑ j, terms a j‖ ≤ C * (∑ a, f a) * (∑ j, g j) := by
  calc
    ‖∑ a, ∑ j, terms a j‖ ≤ ∑ a, ‖∑ j, terms a j‖ := norm_sum_le _ _
    _ ≤ ∑ a, ∑ j, (C * f a * g j) :=
      Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => h a j)
    _ = C * (∑ a, f a) * (∑ j, g j) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem finiteMatrixAnalyticCorrectionBounds
    {b : L → I → J → Joint → ℂ} {C : ℝ}
    (P : ∀ a i j, PaperAnalyticCorrectionBounds (b a i j) C) :
    Nonempty (FiniteMatrixAnalyticCorrectionBounds b C) := by
  classical
  let F (H : L → Test) (u : J → Test) (i : I) : LP2 := ∑ a, ∑ j, (P a i j).forward (H a) (u j)
  let A (H : L → Test) (w : I → Test) (j : J) : LP2 := ∑ a, ∑ i, (P a i j).adjoint (H a) (w i)
  have horder (H : L → Test) (u : J → Test) (w : I → Test) :
      (∀ i, ‖F H u i‖ ≤ C * (∑ a, lp4 (H a)) * (∑ j, grad4 (u j))) ∧
      (∀ j, ‖A H w j‖ ≤ C * (∑ a, lp4 (H a)) * (∑ i, grad4 (w i))) := by
    constructor
    · intro i
      exact norm_finite_contraction _ _ _ _ (fun a j => ((P a i j).first_order (H a) (u j)).1)
    · intro j
      exact norm_finite_contraction _ _ _ _ (fun a i => ((P a i j).first_order (H a) (w i)).2)
  refine ⟨{
    forward := F
    adjoint := A
    forward_pair := ?_
    adjoint_pair := ?_
    adjoint_duality := ?_
    first_order := horder
    coordinate_commutator := ?_
    derivative_first_order := fun k H u w => horder (fun a => coordinateDerivative k (H a)) u w
    rough_gradient := ?_ }⟩
  · intro H u i w
    simp only [F, inner_sum, (P _ _ _).forward_pair]
  · intro H w j v
    simp only [A, inner_sum, (P _ _ _).adjoint_pair]
  · intro H u w
    simp only [F, A, inner_sum, sum_inner]
    calc
      _ = ∑ a, ∑ i, ∑ j, inner ℂ ((w i).toLp 2 volume) ((P a i j).forward (H a) (u j)) := Finset.sum_comm
      _ = ∑ a, ∑ j, ∑ i, inner ℂ ((P a i j).adjoint (H a) (w i)) ((u j).toLp 2 volume) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [(P _ _ _).adjoint_duality]
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  · intro k H u w v
    constructor
    · intro i
      simp only [F, inner_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun j _ => ((P a i j).coordinate_commutator k (H a) (u j) v).1
    · intro j
      simp only [A, inner_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun i _ => ((P a i j).coordinate_commutator k (H a) (w i) v).2
  · intro d D hd H u w
    have hF (a : L) (i : I) (j : J) :
        ∃ X : LP2, ‖X‖ ≤ C * lipschitzGradientLInfty d * lp4 (H a) * lp4 (u j) ∧
          ∀ v : Test, inner ℂ (v.toLp 2 volume) X = -radianHighCommutatorPair (b a i j) d (H a) (u j) v := by
      obtain ⟨X, _, hX, _, hPair⟩ := (P a i j).rough_gradient d (L := D) hd (H a) (u j)
      exact ⟨X, hX, fun v => (hPair v).1⟩
    have hA (a : L) (i : I) (j : J) :
        ∃ X : LP2, ‖X‖ ≤ C * lipschitzGradientLInfty d * lp4 (H a) * lp4 (w i) ∧
          ∀ v : Test, inner ℂ (v.toLp 2 volume) X =
            -radianHighCommutatorPair (highAdjointSymbol (b a i j)) d (fun x => conj (H a x)) (w i) v := by
      obtain ⟨_, X, _, hX, hPair⟩ := (P a i j).rough_gradient d (L := D) hd (H a) (w i)
      exact ⟨X, hX, fun v => (hPair v).2⟩
    choose U hU pU using hF
    choose V hV pV using hA
    refine ⟨fun i => ∑ a, ∑ j, U a i j, fun j => ∑ a, ∑ i, V a i j, ?_, ?_, ?_, ?_⟩
    · exact fun i => norm_finite_contraction _ _ _ _ (fun a j => hU a i j)
    · exact fun j => norm_finite_contraction _ _ _ _ (fun a i => hV a i j)
    · intro i v
      simp only [inner_sum, pU]
    · intro j v
      simp only [inner_sum, pV]

theorem exists_paperFiniteMatrixAnalyticCorrectionBounds
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 27 ≤ K ∧ 0 ≤ C ∧
      ∀ {F : L → I → J → Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → (∀ a i j, ContDiffOn ℝ ∞ (F a i j) W) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ a i j, ∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n (F a i j) (p, (x : RotationSpace))‖ ≤ M) →
      Nonempty (FiniteMatrixAnalyticCorrectionBounds (fun a i j => originalRegularizedAngularSymbol η χ (F a i j)) (C * M)) := by
  intro Q
  obtain ⟨K, C, hK, hC, bound⟩ :=
    exists_paperAnalyticCorrectionBounds η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨K, C, hK, hC, ?_⟩
  intro F W hW hQ hF M hM hjet
  exact finiteMatrixAnalyticCorrectionBounds fun a i j =>
    Classical.choice (bound hW hQ (hF a i j) M hM (hjet a i j))

end Burnett.A08
