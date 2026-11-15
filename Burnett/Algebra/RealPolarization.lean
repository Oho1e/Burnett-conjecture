import Burnett.Algebra.NullQuadratic

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators

/-- The ordered connection cross product, before symmetrizing the amplitudes.
The two factors are the original connection symbols from the paper. -/
def connectionCrossSymbol (gInv : Tensor2) (ξ : Covector) (k l : Tensor2)
    (b c : Index) : ℝ :=
  ∑ a, ∑ e,
    (connectionSymbol gInv ξ k a c e * connectionSymbol gInv ξ l e b a -
      connectionSymbol gInv ξ k a a e * connectionSymbol gInv ξ l e b c)

/-- The real symmetric mixed form associated with the paper's `B(k,k)`.
This definition uses the actual ordered connection products. -/
def mixedQuadraticSymbol (gInv : Tensor2) (ξ : Covector) (k l : Tensor2)
    (b c : Index) : ℝ :=
  (connectionCrossSymbol gInv ξ k l b c +
    connectionCrossSymbol gInv ξ l k b c) / 2

theorem metricTrace_add (gInv k l : Tensor2) :
    metricTrace gInv (k + l) = metricTrace gInv k + metricTrace gInv l := by
  simp only [metricTrace, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem metricTrace_smul (gInv : Tensor2) (r : ℝ) (k : Tensor2) :
    metricTrace gInv (r • k) = r * metricTrace gInv k := by
  simp only [metricTrace, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem contracted_add (gInv : Tensor2) (ξ : Covector) (k l : Tensor2) (b : Index) :
    contracted gInv ξ (k + l) b = contracted gInv ξ k b + contracted gInv ξ l b := by
  simp only [contracted, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem contracted_smul (gInv : Tensor2) (ξ : Covector) (r : ℝ)
    (k : Tensor2) (b : Index) :
    contracted gInv ξ (r • k) b = r * contracted gInv ξ k b := by
  simp only [contracted, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem connectionSymbol_add (gInv : Tensor2) (ξ : Covector) (k l : Tensor2)
    (a b c : Index) :
    connectionSymbol gInv ξ (k + l) a b c =
      connectionSymbol gInv ξ k a b c + connectionSymbol gInv ξ l a b c := by
  have hr (i j : Index) : raiseSecond gInv (k + l) i j =
      raiseSecond gInv k i j + raiseSecond gInv l i j := by
    simp only [raiseSecond, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [connectionSymbol, hr, Pi.add_apply]
  ring

theorem connectionSymbol_smul (gInv : Tensor2) (ξ : Covector) (r : ℝ) (k : Tensor2)
    (a b c : Index) :
    connectionSymbol gInv ξ (r • k) a b c = r * connectionSymbol gInv ξ k a b c := by
  have hr (i j : Index) : raiseSecond gInv (r • k) i j =
      r * raiseSecond gInv k i j := by
    simp only [raiseSecond, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp only [connectionSymbol, hr, Pi.smul_apply, smul_eq_mul]
  ring

theorem connectionCrossSymbol_add_left (gInv : Tensor2) (ξ : Covector)
    (k l m : Tensor2) (b c : Index) :
    connectionCrossSymbol gInv ξ (k + l) m b c =
      connectionCrossSymbol gInv ξ k m b c + connectionCrossSymbol gInv ξ l m b c := by
  simp only [connectionCrossSymbol, connectionSymbol_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem connectionCrossSymbol_add_right (gInv : Tensor2) (ξ : Covector)
    (k l m : Tensor2) (b c : Index) :
    connectionCrossSymbol gInv ξ k (l + m) b c =
      connectionCrossSymbol gInv ξ k l b c + connectionCrossSymbol gInv ξ k m b c := by
  simp only [connectionCrossSymbol, connectionSymbol_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem connectionCrossSymbol_smul_left (gInv : Tensor2) (ξ : Covector)
    (r : ℝ) (k l : Tensor2) (b c : Index) :
    connectionCrossSymbol gInv ξ (r • k) l b c =
      r * connectionCrossSymbol gInv ξ k l b c := by
  simp only [connectionCrossSymbol, connectionSymbol_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem connectionCrossSymbol_smul_right (gInv : Tensor2) (ξ : Covector)
    (r : ℝ) (k l : Tensor2) (b c : Index) :
    connectionCrossSymbol gInv ξ k (r • l) b c =
      r * connectionCrossSymbol gInv ξ k l b c := by
  simp only [connectionCrossSymbol, connectionSymbol_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- Symmetry here exchanges the two amplitudes, with `b,c` fixed. -/
theorem mixedQuadraticSymbol_comm (gInv : Tensor2) (ξ : Covector)
    (k l : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k l b c = mixedQuadraticSymbol gInv ξ l k b c := by
  unfold mixedQuadraticSymbol
  ring

theorem mixedQuadraticSymbol_add_left (gInv : Tensor2) (ξ : Covector)
    (k l m : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ (k + l) m b c =
      mixedQuadraticSymbol gInv ξ k m b c + mixedQuadraticSymbol gInv ξ l m b c := by
  simp only [mixedQuadraticSymbol, connectionCrossSymbol_add_left,
    connectionCrossSymbol_add_right]
  ring

theorem mixedQuadraticSymbol_add_right (gInv : Tensor2) (ξ : Covector)
    (k l m : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k (l + m) b c =
      mixedQuadraticSymbol gInv ξ k l b c + mixedQuadraticSymbol gInv ξ k m b c := by
  simp only [mixedQuadraticSymbol, connectionCrossSymbol_add_left,
    connectionCrossSymbol_add_right]
  ring

theorem mixedQuadraticSymbol_smul_left (gInv : Tensor2) (ξ : Covector)
    (r : ℝ) (k l : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ (r • k) l b c =
      r * mixedQuadraticSymbol gInv ξ k l b c := by
  simp only [mixedQuadraticSymbol, connectionCrossSymbol_smul_left,
    connectionCrossSymbol_smul_right]
  ring

theorem mixedQuadraticSymbol_smul_right (gInv : Tensor2) (ξ : Covector)
    (r : ℝ) (k l : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k (r • l) b c =
      r * mixedQuadraticSymbol gInv ξ k l b c := by
  simp only [mixedQuadraticSymbol, connectionCrossSymbol_smul_left,
    connectionCrossSymbol_smul_right]
  ring

/-- The diagonal is exactly the original ordered-sum quadratic symbol. -/
theorem mixedQuadraticSymbol_diag (gInv : Tensor2) (ξ : Covector)
    (k : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k k b c = quadraticSymbol gInv ξ k b c := by
  change (quadraticSymbol gInv ξ k b c + quadraticSymbol gInv ξ k b c) / 2 = _
  ring

/-- The connection-product definition agrees with real polarization of the
original quadratic symbol; this is a proved bridge, not a second definition. -/
theorem mixedQuadraticSymbol_polarization (gInv : Tensor2) (ξ : Covector)
    (k l : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k l b c =
      (quadraticSymbol gInv ξ (k + l) b c - quadraticSymbol gInv ξ k b c -
        quadraticSymbol gInv ξ l b c) / 2 := by
  change _ = (connectionCrossSymbol gInv ξ (k + l) (k + l) b c -
    connectionCrossSymbol gInv ξ k k b c - connectionCrossSymbol gInv ξ l l b c) / 2
  simp only [connectionCrossSymbol_add_left, connectionCrossSymbol_add_right,
    mixedQuadraticSymbol]
  ring

/-- The Ricci symbol is additive in its amplitude, so its kernel is a real
linear subspace. The scalar part is supplied below. -/
theorem ricciSymbol_add (gInv : Tensor2) (ξ : Covector) (k l : Tensor2)
    (a b : Index) :
    ricciSymbol gInv ξ (k + l) a b =
      ricciSymbol gInv ξ k a b + ricciSymbol gInv ξ l a b := by
  simp only [ricciSymbol, Pi.add_apply, metricTrace_add, contracted_add]
  ring

theorem ricciSymbol_smul (gInv : Tensor2) (ξ : Covector) (r : ℝ) (k : Tensor2)
    (a b : Index) :
    ricciSymbol gInv ξ (r • k) a b = r * ricciSymbol gInv ξ k a b := by
  simp only [ricciSymbol, Pi.smul_apply, smul_eq_mul, metricTrace_smul, contracted_smul]
  ring

/-- All real mixed terms vanish on the noncharacteristic Ricci kernel.
No symmetry or signature assumptions are needed for this stronger statement. -/
theorem mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel
    (gInv : Tensor2) (ξ : Covector) (k l : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, ricciSymbol gInv ξ l a b = 0) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k l b c = 0 := by
  have hkl : ∀ a b, ricciSymbol gInv ξ (k + l) a b = 0 := by
    intro a b
    rw [ricciSymbol_add, hk a b, hl a b, add_zero]
  rw [mixedQuadraticSymbol_polarization,
    quadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ (k + l) hs hkl,
    quadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ k hs hk,
    quadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ l hs hl]
  ring

private theorem rp_sum_comm (f : Index → Index → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  have h (s : Finset Index) :
      (∑ a ∈ s, ∑ b, f a b) = ∑ b, ∑ a ∈ s, f a b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, Finset.sum_add_distrib]
  simpa using h Finset.univ

/-- Symmetry of the original ordered contraction follows from symmetry of the
inverse metric; neither amplitude is required to be symmetric here. -/
theorem tensorPairing_comm (gInv k l : Tensor2) (hg : IsSymmetricTensor gInv) :
    tensorPairing gInv k l = tensorPairing gInv l k := by
  unfold tensorPairing
  calc
    _ = ∑ a, ∑ c, ∑ d, ∑ b, gInv a c * gInv b d * k a b * l c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [rp_sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [rp_sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, gInv a c * gInv b d * k a b * l c d := by
      rw [rp_sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [rp_sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hg a c, hg b d]
      ring

theorem physicalPairing_comm (gInv k l : Tensor2) (hg : IsSymmetricTensor gInv) :
    physicalPairing gInv k l = physicalPairing gInv l k := by
  unfold physicalPairing
  rw [tensorPairing_comm gInv k l hg]
  ring

theorem physicalPairing_add_left (gInv k l m : Tensor2) :
    physicalPairing gInv (k + l) m =
      physicalPairing gInv k m + physicalPairing gInv l m := by
  simp only [physicalPairing, tensorPairing, metricTrace_add, Pi.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem physicalPairing_add_right (gInv k l m : Tensor2) :
    physicalPairing gInv k (l + m) =
      physicalPairing gInv k l + physicalPairing gInv k m := by
  simp only [physicalPairing, tensorPairing, metricTrace_add, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]
  ring

theorem physicalPairing_smul_left (gInv : Tensor2) (r : ℝ) (k l : Tensor2) :
    physicalPairing gInv (r • k) l = r * physicalPairing gInv k l := by
  have ht : tensorPairing gInv (r • k) l = r * tensorPairing gInv k l := by
    simp only [tensorPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp only [physicalPairing, ht, metricTrace_smul]
  ring

theorem physicalPairing_smul_right (gInv : Tensor2) (r : ℝ) (k l : Tensor2) :
    physicalPairing gInv k (r • l) = r * physicalPairing gInv k l := by
  have ht : tensorPairing gInv k (r • l) = r * tensorPairing gInv k l := by
    simp only [tensorPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp only [physicalPairing, ht, metricTrace_smul]
  ring

/-- The real mixed null formula, with both independently quantified symmetric
Ricci-kernel amplitudes. It uses the original full ordered physical contraction. -/
theorem mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel
    (gInv : Tensor2) (ξ : Covector) (k l : Tensor2)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricTensor k)
    (hlSymm : IsSymmetricTensor l) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, ricciSymbol gInv ξ l a b = 0) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k l b c =
      ξ b * ξ c * physicalPairing gInv k l / 4 := by
  have hklSymm : IsSymmetricTensor (k + l) := by
    intro a b
    change k a b + l a b = k b a + l b a
    rw [hkSymm a b, hlSymm a b]
  have hkl : ∀ a b, ricciSymbol gInv ξ (k + l) a b = 0 := by
    intro a b
    rw [ricciSymbol_add, hk a b, hl a b, add_zero]
  rw [mixedQuadraticSymbol_polarization,
    quadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ (k + l) hg hklSymm
      hξ hs hkl,
    quadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ k hg hkSymm hξ hs hk,
    quadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ l hg hlSymm hξ hs hl,
    physicalPairing_add_left, physicalPairing_add_right, physicalPairing_add_right,
    physicalPairing_comm gInv l k hg]
  ring

end Burnett.RicciSymbol
