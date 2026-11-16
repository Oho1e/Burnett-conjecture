import Burnett.Algebra.RealPolarization

/-!
# Real tensor contractions under a Lorentz-frame change

For the component matrix E, covectors transform by Eᵀ and covariant
symmetric tensors by Eᵀ k E; the inverse metric is E η Eᵀ.
The frame certificate records an invertible change and that normal form,
without assuming a physical-positivity or a Ricci-kernel conclusion.
-/

noncomputable section
namespace Burnett.RicciSymbol.TensorFrame
open scoped BigOperators

def signature (a : Index) : ℝ := if a = 0 then -1 else 1

def standardInverse : Tensor2 := fun a b => if a = b then signature a else 0

def inverseMetric (e : Tensor2) : Tensor2 := fun i j =>
  ∑ a, signature a * e i a * e j a

def tensor (e k : Tensor2) : Tensor2 := fun a b =>
  ∑ i, ∑ j, e i a * e j b * k i j

def covector (e : Tensor2) (ξ : Covector) : Covector := fun a =>
  ∑ i, e i a * ξ i

private theorem sum_swap (f : Index → Index → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  have h (s : Finset Index) :
      (∑ a ∈ s, ∑ b, f a b) = ∑ b, ∑ a ∈ s, f a b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, Finset.sum_add_distrib]
  simpa using h Finset.univ

private theorem sum_one_two (f : Index → Index → Index → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
  rw [sum_swap]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_swap]

private theorem sum_four_two (f : Index → Index → Index → Index → Index → Index → ℝ) :
    (∑ i, ∑ j, ∑ c, ∑ d, ∑ a, ∑ b, f i j c d a b) =
      ∑ a, ∑ b, ∑ i, ∑ j, ∑ c, ∑ d, f i j c d a b := by
  calc
    _ = ∑ i, ∑ j, ∑ c, ∑ a, ∑ b, ∑ d, f i j c d a b := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_one_two _
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, f i j c d a b := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_one_two _
    _ = ∑ i, ∑ a, ∑ b, ∑ j, ∑ c, ∑ d, f i j c d a b := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_one_two _
    _ = _ := sum_one_two _

private theorem sum_two_two (f : Index → Index → Index → Index → ℝ) :
    (∑ i, ∑ j, ∑ c, ∑ d, f i j c d) = ∑ c, ∑ d, ∑ i, ∑ j, f i j c d := by
  calc
    _ = ∑ i, ∑ c, ∑ d, ∑ j, f i j c d := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_one_two _
    _ = _ := sum_one_two _

theorem metricTrace_transform (e k : Tensor2) :
    metricTrace (inverseMetric e) k = ∑ a, signature a * tensor e k a a := by
  unfold metricTrace inverseMetric tensor
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ a, ∑ j, signature a * e i a * e j a * k i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sum_swap]
    _ = ∑ a, ∑ i, ∑ j, signature a * e i a * e j a * k i j := sum_swap _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem tensorPairing_transform (e k l : Tensor2) :
    tensorPairing (inverseMetric e) k l =
      ∑ a, ∑ b, signature a * signature b * tensor e k a b * tensor e l a b := by
  unfold tensorPairing inverseMetric tensor
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_two]
  rw [sum_swap]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [sum_two_two]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem metricTrace_standard (k : Tensor2) :
    metricTrace standardInverse k = ∑ a, signature a * k a a := by
  simp [metricTrace, standardInverse, ite_mul]

theorem tensorPairing_standard (k l : Tensor2) :
    tensorPairing standardInverse k l = ∑ a, ∑ b, signature a * signature b * k a b * l a b := by
  simp [tensorPairing, standardInverse, ite_mul, mul_ite]

theorem physicalPairing_transform (e k l : Tensor2) :
    physicalPairing (inverseMetric e) k l = physicalPairing standardInverse (tensor e k) (tensor e l) := by
  simp only [physicalPairing, metricTrace_standard, tensorPairing_standard,
    metricTrace_transform, tensorPairing_transform]

theorem tensor_symmetric (e k : Tensor2) (hk : IsSymmetricTensor k) :
    IsSymmetricTensor (tensor e k) := by
  intro a b
  unfold tensor
  rw [sum_swap]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hk j i]
  ring

theorem inverseMetric_symmetric (e : Tensor2) : IsSymmetricTensor (inverseMetric e) := by
  intro i j
  unfold inverseMetric
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem raiseCovector_transform (e : Tensor2) (ξ : Covector) (i : Index) :
    raiseCovector (inverseMetric e) ξ i = ∑ a, signature a * e i a * covector e ξ a := by
  unfold raiseCovector inverseMetric covector
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem contracted_standard (ξ : Covector) (k : Tensor2) (a : Index) :
    contracted standardInverse ξ k a = ∑ b, signature b * ξ b * k b a := by
  simp [contracted, raiseCovector, standardInverse, ite_mul]

theorem contracted_transform (e k : Tensor2) (ξ : Covector) (a : Index) :
    contracted standardInverse (covector e ξ) (tensor e k) a =
      ∑ j, e j a * contracted (inverseMetric e) ξ k j := by
  rw [contracted_standard]
  simp only [tensor, covector, contracted, raiseCovector_transform,
    Finset.mul_sum, Finset.sum_mul]
  rw [sum_one_two, sum_swap]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro h hh
  ring

theorem tensor_product (e : Tensor2) (ξ v : Covector) (a b : Index) :
    tensor e (fun i j => ξ i * v j) a b = covector e ξ a * covector e v b := by
  unfold tensor covector
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem symbolNorm_eq_metricTrace (gInv : Tensor2) (ξ : Covector) :
    symbolNorm gInv ξ = metricTrace gInv (fun i j => ξ i * ξ j) := by
  unfold symbolNorm metricTrace
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem symbolNorm_transform (e : Tensor2) (ξ : Covector) :
    symbolNorm (inverseMetric e) ξ = symbolNorm standardInverse (covector e ξ) := by
  rw [symbolNorm_eq_metricTrace, metricTrace_transform, symbolNorm_eq_metricTrace,
    metricTrace_standard]
  apply Finset.sum_congr rfl
  intro a ha
  rw [tensor_product]

theorem null_kernel_transform (e k : Tensor2) (ξ : Covector)
    (hξ : ξ ≠ 0) (hs : symbolNorm (inverseMetric e) ξ = 0)
    (hk : ∀ i j, ricciSymbol (inverseMetric e) ξ k i j = 0) :
    ∀ a b, ricciSymbol standardInverse (covector e ξ) (tensor e k) a b = 0 := by
  have hq := (null_kernel_iff_contracted (inverseMetric e) ξ k hξ hs).mp hk
  have hs' : symbolNorm standardInverse (covector e ξ) = 0 := by
    rw [← symbolNorm_transform, hs]
  have ht : metricTrace standardInverse (tensor e k) = metricTrace (inverseMetric e) k := by
    rw [metricTrace_transform, metricTrace_standard]
  have hq' (a : Index) : contracted standardInverse (covector e ξ) (tensor e k) a =
      metricTrace standardInverse (tensor e k) * covector e ξ a / 2 := by
    rw [contracted_transform, ht]
    simp_rw [hq]
    simp only [covector, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  intro a b
  rw [ricciSymbol, hs', hq' a, hq' b]
  ring

theorem covector_zero (e : Tensor2) : covector e 0 = 0 := by
  funext a
  simp [covector]

theorem tensor_as_covector (e k : Tensor2) (a b : Index) :
    tensor e k a b = covector e (fun i => covector e (k i) b) a := by
  simp only [tensor, covector, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tensor_injective (e : Tensor2) (he : Function.Injective (covector e)) :
    Function.Injective (tensor e) := by
  intro k l h
  have hcol (b : Index) : (fun i => covector e (k i) b) = (fun i => covector e (l i) b) := by
    apply he
    funext a
    rw [← tensor_as_covector, ← tensor_as_covector]
    exact congrFun (congrFun h a) b
  funext i
  apply he
  funext b
  exact congrFun (hcol b) i

theorem covector_ne_zero (e : Tensor2) (he : Function.Injective (covector e))
    (ξ : Covector) (hξ : ξ ≠ 0) : covector e ξ ≠ 0 := by
  intro h
  apply hξ
  apply he
  simpa only [covector_zero] using h

theorem tensor_add (e k l : Tensor2) : tensor e (k + l) = tensor e k + tensor e l := by
  funext a b
  simp only [tensor, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem tensor_pureGauge (e : Tensor2) (ξ v : Covector) :
    tensor e (pureGauge ξ v) = pureGauge (covector e ξ) (covector e v) := by
  have hd : pureGauge ξ v = (fun i j => ξ i * v j) + (fun i j => v i * ξ j) := rfl
  rw [hd, tensor_add]
  funext a b
  simp only [Pi.add_apply, tensor_product, pureGauge]

/-- A Lorentz frame certificate records only an invertible coordinate change
and the inverse metric's normal form; it contains no positivity conclusion. -/
structure LorentzFrame (gInv : Tensor2) where
  components : Tensor2
  isBasis : Function.Bijective (covector components)
  inverseMetric_eq : inverseMetric components = gInv

end Burnett.RicciSymbol.TensorFrame
