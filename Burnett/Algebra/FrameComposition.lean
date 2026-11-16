import Burnett.Algebra.TensorFrame
import Burnett.Algebra.NullScreen

noncomputable section

namespace Burnett.RicciSymbol.FrameComposition

open scoped BigOperators

/-- Actual matrix composition of the two coordinate frames. -/
def compose (e r : Tensor2) : Tensor2 := fun i a => ∑ b, e i b * r b a

private theorem fc_sum_swap (f : Index → Index → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  have h (s : Finset Index) :
      (∑ a ∈ s, ∑ b, f a b) = ∑ b, ∑ a ∈ s, f a b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, Finset.sum_add_distrib]
  simpa using h Finset.univ

private theorem fc_sum_one_two (f : Index → Index → Index → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
  rw [fc_sum_swap]
  apply Finset.sum_congr rfl
  intro a ha
  rw [fc_sum_swap]

private theorem fc_sum_two_two (f : Index → Index → Index → Index → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f i j a b := by
      apply Finset.sum_congr rfl
      intro i hi
      exact fc_sum_one_two _
    _ = _ := fc_sum_one_two _

/-- Covectors transform by the genuine composite, in the contravariant order
of the coordinate maps. -/
theorem covector_compose (e r : Tensor2) (ξ : Covector) :
    TensorFrame.covector (compose e r) ξ = TensorFrame.covector r (TensorFrame.covector e ξ) := by
  funext a
  simp only [TensorFrame.covector, compose, Finset.sum_mul, Finset.mul_sum]
  rw [fc_sum_swap]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Both covariant tensor slots transform under the same actual composition. -/
theorem tensor_compose (e r k : Tensor2) :
    TensorFrame.tensor (compose e r) k = TensorFrame.tensor r (TensorFrame.tensor e k) := by
  funext a b
  simp only [TensorFrame.tensor, compose, Finset.sum_mul, Finset.mul_sum]
  rw [fc_sum_two_two, fc_sum_swap]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- General metric contraction for a composite frame, before imposing the
Lorentz property on the second frame. -/
theorem inverseMetric_compose (e r : Tensor2) (i j : Index) :
    TensorFrame.inverseMetric (compose e r) i j =
      ∑ b, ∑ c, e i b * e j c * TensorFrame.inverseMetric r b c := by
  simp only [TensorFrame.inverseMetric, compose, Finset.sum_mul, Finset.mul_sum]
  rw [fc_sum_one_two, fc_sum_swap]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- An actual Lorentz change of frame preserves the inverse metric reconstructed
by the first frame. This is a proved contraction identity, not a field of data. -/
theorem inverseMetric_compose_of_lorentz (e r : Tensor2)
    (hr : TensorFrame.inverseMetric r = TensorFrame.standardInverse) :
    TensorFrame.inverseMetric (compose e r) = TensorFrame.inverseMetric e := by
  funext i j
  rw [inverseMetric_compose, hr]
  simp [TensorFrame.standardInverse, TensorFrame.inverseMetric, mul_ite]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Compose two genuine frame certificates. The second is a Lorentz frame of
the standard metric; no null normalization or positivity is assumed. -/
def composeFrames (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (rotation : TensorFrame.LorentzFrame NullScreen.minkowskiInverse) : TensorFrame.LorentzFrame gInv where
  components := compose frame.components rotation.components
  isBasis := by
    have hc : TensorFrame.covector (compose frame.components rotation.components) =
        (TensorFrame.covector rotation.components) ∘ (TensorFrame.covector frame.components) := by
      funext ξ
      exact covector_compose frame.components rotation.components ξ
    rw [hc]
    exact rotation.isBasis.comp frame.isBasis
  inverseMetric_eq := by
    have hr : TensorFrame.inverseMetric rotation.components = TensorFrame.standardInverse :=
      rotation.inverseMetric_eq
    rw [inverseMetric_compose_of_lorentz frame.components rotation.components hr]
    exact frame.inverseMetric_eq

@[simp] theorem composeFrames_components (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (rotation : TensorFrame.LorentzFrame NullScreen.minkowskiInverse) :
    (composeFrames gInv frame rotation).components = compose frame.components rotation.components := rfl

theorem covector_composeFrames (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (rotation : TensorFrame.LorentzFrame NullScreen.minkowskiInverse) (ξ : Covector) :
    TensorFrame.covector (composeFrames gInv frame rotation).components ξ =
      TensorFrame.covector rotation.components (TensorFrame.covector frame.components ξ) :=
  covector_compose frame.components rotation.components ξ

theorem tensor_composeFrames (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (rotation : TensorFrame.LorentzFrame NullScreen.minkowskiInverse) (k : Tensor2) :
    TensorFrame.tensor (composeFrames gInv frame rotation).components k =
      TensorFrame.tensor rotation.components (TensorFrame.tensor frame.components k) :=
  tensor_compose frame.components rotation.components k

end Burnett.RicciSymbol.FrameComposition
