import Burnett.Algebra.ComplexFrame

noncomputable section

namespace Burnett.RicciSymbol.NullNormalForm

open scoped BigOperators ComplexConjugate
open ComplexFrame

private theorem nf_sum_swap (f : Index → Index → ℂ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  have h (s : Finset Index) :
      (∑ a ∈ s, ∑ b, f a b) = ∑ b, ∑ a ∈ s, f a b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, Finset.sum_add_distrib]
  simpa using h Finset.univ

theorem complexTensor_as_covector (e : Tensor2) (k : ComplexTensor2) (a b : Index) :
    complexTensor e k a b = complexCovector e (fun i => complexCovector e (k i) b) a := by
  simp only [complexTensor, complexCovector, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Actual surjectivity of the two-tensor transformation, reconstructed through
the two covector slots rather than assumed as frame data. -/
theorem complexTensor_surjective (e : Tensor2) (he : Function.Surjective (TensorFrame.covector e)) :
    Function.Surjective (complexTensor e) := by
  classical
  have hsurj := complexCovector_surjective e he
  intro l
  let u (b : Index) : ComplexCovector := Classical.choose (hsurj (fun a => l a b))
  have hu (b : Index) : complexCovector e (u b) = fun a => l a b :=
    Classical.choose_spec (hsurj (fun a => l a b))
  let k (i : Index) : ComplexCovector := Classical.choose (hsurj (fun b => u b i))
  have hk (i : Index) : complexCovector e (k i) = fun b => u b i :=
    Classical.choose_spec (hsurj (fun b => u b i))
  refine ⟨k, ?_⟩
  funext a b
  rw [complexTensor_as_covector]
  have hrow : (fun i => complexCovector e (k i) b) = u b := by
    funext i
    exact congrFun (hk i) b
  rw [hrow]
  exact congrFun (hu b) a

theorem complexTensor_transpose (e : Tensor2) (k : ComplexTensor2) (a b : Index) :
    complexTensor e (fun i j => k j i) a b = complexTensor e k b a := by
  simp only [complexTensor]
  rw [nf_sum_swap]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem complexTensor_symmetric_reflect (e : Tensor2)
    (he : Function.Injective (TensorFrame.covector e)) (k : ComplexTensor2)
    (hk : IsSymmetricComplexTensor (complexTensor e k)) : IsSymmetricComplexTensor k := by
  have htrans : complexTensor e (fun i j => k j i) = complexTensor e k := by
    funext a b
    rw [complexTensor_transpose]
    exact hk b a
  have h := complexTensor_injective e he htrans
  intro a b
  exact (congrFun (congrFun h a) b).symm

/-- Null-kernel covariance is an equivalence when the coordinate frame is
invertible; the reverse direction pulls the contracted constraint back. -/
theorem real_null_kernel_iff (e : Tensor2) (he : Function.Injective (TensorFrame.covector e))
    (ξ : Covector) (k : Tensor2) (hξ : ξ ≠ 0)
    (hs : symbolNorm (TensorFrame.inverseMetric e) ξ = 0) :
    (∀ i j, ricciSymbol (TensorFrame.inverseMetric e) ξ k i j = 0) ↔
      ∀ a b, ricciSymbol TensorFrame.standardInverse (TensorFrame.covector e ξ)
        (TensorFrame.tensor e k) a b = 0 := by
  constructor
  · exact TensorFrame.null_kernel_transform e k ξ hξ hs
  · intro hk
    have hξ' := TensorFrame.covector_ne_zero e he ξ hξ
    have hs' : symbolNorm TensorFrame.standardInverse (TensorFrame.covector e ξ) = 0 := by
      rw [← TensorFrame.symbolNorm_transform, hs]
    have hq := (null_kernel_iff_contracted TensorFrame.standardInverse
      (TensorFrame.covector e ξ) (TensorFrame.tensor e k) hξ' hs').mp hk
    have ht : metricTrace TensorFrame.standardInverse (TensorFrame.tensor e k) =
        metricTrace (TensorFrame.inverseMetric e) k := by
      rw [TensorFrame.metricTrace_standard, TensorFrame.metricTrace_transform]
    have hqE : TensorFrame.covector e (fun j => contracted (TensorFrame.inverseMetric e) ξ k j) =
        TensorFrame.covector e (fun j => metricTrace (TensorFrame.inverseMetric e) k * ξ j / 2) := by
      funext a
      change (∑ j, e j a * contracted (TensorFrame.inverseMetric e) ξ k j) = _
      rw [← TensorFrame.contracted_transform, hq a, ht]
      simp only [TensorFrame.covector, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hbase := he hqE
    apply (null_kernel_iff_contracted (TensorFrame.inverseMetric e) ξ k hξ hs).mpr
    intro j
    exact congrFun hbase j

theorem complex_null_kernel_iff (e : Tensor2)
    (he : Function.Injective (TensorFrame.covector e))
    (ξ : Covector) (k : ComplexTensor2) (hξ : ξ ≠ 0)
    (hs : symbolNorm (TensorFrame.inverseMetric e) ξ = 0) :
    (∀ i j, complexRicciSymbol (TensorFrame.inverseMetric e) ξ k i j = 0) ↔
      ∀ a b, complexRicciSymbol TensorFrame.standardInverse (TensorFrame.covector e ξ)
        (complexTensor e k) a b = 0 := by
  constructor
  · exact complex_null_kernel_transform e ξ k hξ hs
  · intro hk
    obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff TensorFrame.standardInverse
      (TensorFrame.covector e ξ) (complexTensor e k)).mp hk
    apply (complexRicci_kernel_iff (TensorFrame.inverseMetric e) ξ k).mpr
    constructor
    · apply (real_null_kernel_iff e he ξ (tensorRe k) hξ hs).mpr
      simpa only [complexTensor_re] using hkr
    · apply (real_null_kernel_iff e he ξ (tensorIm k) hξ hs).mpr
      simpa only [complexTensor_im] using hki

theorem complexTensor_add (e : Tensor2) (k l : ComplexTensor2) :
    complexTensor e (k + l) = complexTensor e k + complexTensor e l := by
  funext a b
  simp [complexTensor, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem complexTensor_smul (e : Tensor2) (z : ℂ) (k : ComplexTensor2) :
    complexTensor e (z • k) = z • complexTensor e k := by
  funext a b
  simp only [complexTensor, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Coordinates are extracted from the actual transformed amplitude. -/
def screenCoordinates (e : Tensor2) (k : ComplexTensor2) : ℂ × ℂ :=
  (complexTensor e k 2 2, complexTensor e k 2 3)

theorem screenCoordinates_add (e : Tensor2) (k l : ComplexTensor2) :
    screenCoordinates e (k + l) =
      ((screenCoordinates e k).1 + (screenCoordinates e l).1,
       (screenCoordinates e k).2 + (screenCoordinates e l).2) := by
  simp [screenCoordinates, complexTensor_add]

theorem screenCoordinates_smul (e : Tensor2) (z : ℂ) (k : ComplexTensor2) :
    screenCoordinates e (z • k) =
      (z * (screenCoordinates e k).1, z * (screenCoordinates e k).2) := by
  simp [screenCoordinates, complexTensor_smul, Pi.smul_apply, smul_eq_mul]

theorem normalization_nonzero (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (ξ : Covector) (hnormal : TensorFrame.covector frame.components ξ = NullScreen.nullCovector) :
    ξ ≠ 0 := by
  intro hξ
  apply NullScreen.nullCovector_ne_zero
  rw [← hnormal, hξ, TensorFrame.covector_zero]

theorem normalization_null (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (ξ : Covector) (hnormal : TensorFrame.covector frame.components ξ = NullScreen.nullCovector) :
    symbolNorm gInv ξ = 0 := by
  rw [← frame.inverseMetric_eq, TensorFrame.symbolNorm_transform, hnormal]
  exact NullScreen.nullCovector_symbolNorm

theorem normalized_complex_kernel (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (ξ : Covector) (hnormal : TensorFrame.covector frame.components ξ = NullScreen.nullCovector)
    (k : ComplexTensor2) (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0) :
    ∀ a b, complexRicciSymbol NullScreen.minkowskiInverse NullScreen.nullCovector
      (complexTensor frame.components k) a b = 0 := by
  have hs : symbolNorm (TensorFrame.inverseMetric frame.components) ξ = 0 := by
    rw [frame.inverseMetric_eq]
    exact normalization_null gInv frame ξ hnormal
  have hk' : ∀ a b, complexRicciSymbol (TensorFrame.inverseMetric frame.components) ξ k a b = 0 := by
    simpa only [frame.inverseMetric_eq] using hk
  have h := complex_null_kernel_transform frame.components ξ k
    (normalization_nonzero gInv frame ξ hnormal) hs hk'
  simpa only [hnormal] using h

/-- Equality of the actual two screen coordinates is equivalent to belonging
to the same gauge class; this proves injectivity on the physical classes. -/
theorem same_screenCoordinates_iff_gauge
    (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (ξ : Covector) (hnormal : TensorFrame.covector frame.components ξ = NullScreen.nullCovector)
    (k l : ComplexTensor2) (hkSymm : IsSymmetricComplexTensor k)
    (hlSymm : IsSymmetricComplexTensor l)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) :
    (∃ v : ComplexCovector, k = l + complexPureGauge ξ v) ↔
      screenCoordinates frame.components k = screenCoordinates frame.components l := by
  constructor
  · rintro ⟨v, rfl⟩
    apply Prod.ext
    · change complexTensor frame.components (l + complexPureGauge ξ v) 2 2 =
        complexTensor frame.components l 2 2
      rw [complexTensor_add, complexTensor_pureGauge, hnormal]
      simp [Pi.add_apply, complexPureGauge, NullScreen.nullCovector]
    · change complexTensor frame.components (l + complexPureGauge ξ v) 2 3 =
        complexTensor frame.components l 2 3
      rw [complexTensor_add, complexTensor_pureGauge, hnormal]
      simp [Pi.add_apply, complexPureGauge, NullScreen.nullCovector]
  · intro hc
    have hkr := normalized_complex_kernel gInv frame ξ hnormal k hk
    have hlr := normalized_complex_kernel gInv frame ξ hnormal l hl
    have hkrS := complexTensor_symmetric frame.components k hkSymm
    have hlrS := complexTensor_symmetric frame.components l hlSymm
    have ha := congrArg Prod.fst hc
    have hb := congrArg Prod.snd hc
    change complexTensor frame.components k 2 2 = complexTensor frame.components l 2 2 at ha
    change complexTensor frame.components k 2 3 = complexTensor frame.components l 2 3 at hb
    obtain ⟨v, hv⟩ := complexCovector_surjective frame.components frame.isBasis.2
      (HermitianScreen.complexGaugeVector (complexTensor frame.components k) -
       HermitianScreen.complexGaugeVector (complexTensor frame.components l))
    refine ⟨v, ?_⟩
    apply complexTensor_injective frame.components frame.isBasis.1
    rw [complexTensor_add, complexTensor_pureGauge, hnormal, hv]
    calc
      complexTensor frame.components k =
          complexPureGauge NullScreen.nullCovector
              (HermitianScreen.complexGaugeVector (complexTensor frame.components k)) +
            HermitianScreen.complexScreenTensor (complexTensor frame.components k 2 2)
              (complexTensor frame.components k 2 3) :=
        HermitianScreen.complex_kernel_decomposition _ hkrS hkr
      _ = (complexPureGauge NullScreen.nullCovector
              (HermitianScreen.complexGaugeVector (complexTensor frame.components l)) +
            HermitianScreen.complexScreenTensor (complexTensor frame.components l 2 2)
              (complexTensor frame.components l 2 3)) +
          complexPureGauge NullScreen.nullCovector
            (HermitianScreen.complexGaugeVector (complexTensor frame.components k) -
             HermitianScreen.complexGaugeVector (complexTensor frame.components l)) := by
        funext a b
        simp only [Pi.add_apply, Pi.sub_apply, complexPureGauge]
        rw [ha, hb]
        ring
      _ = _ := congrArg
        (fun z : ComplexTensor2 => z + complexPureGauge NullScreen.nullCovector
          (HermitianScreen.complexGaugeVector (complexTensor frame.components k) -
           HermitianScreen.complexGaugeVector (complexTensor frame.components l)))
        (HermitianScreen.complex_kernel_decomposition _ hlrS hlr).symm

/-- Every pair of complex coordinates is attained by an actual symmetric
amplitude in the original Ricci kernel. This is the converse dimension bound. -/
theorem screenCoordinates_surjective
    (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (ξ : Covector) (hnormal : TensorFrame.covector frame.components ξ = NullScreen.nullCovector)
    (a b : ℂ) :
    ∃ k : ComplexTensor2, IsSymmetricComplexTensor k ∧
      (∀ i j, complexRicciSymbol gInv ξ k i j = 0) ∧
      screenCoordinates frame.components k = (a, b) := by
  obtain ⟨k, hk⟩ := complexTensor_surjective frame.components frame.isBasis.2
    (HermitianScreen.complexScreenTensor a b)
  have hkSymm : IsSymmetricComplexTensor k := by
    apply complexTensor_symmetric_reflect frame.components frame.isBasis.1 k
    rw [hk]
    exact HermitianScreen.complexScreenTensor_symmetric a b
  have hξ := normalization_nonzero gInv frame ξ hnormal
  have hs : symbolNorm (TensorFrame.inverseMetric frame.components) ξ = 0 := by
    rw [frame.inverseMetric_eq]
    exact normalization_null gInv frame ξ hnormal
  have htarget : ∀ i j, complexRicciSymbol TensorFrame.standardInverse
      (TensorFrame.covector frame.components ξ) (complexTensor frame.components k) i j = 0 := by
    rw [hnormal, hk]
    exact HermitianScreen.complexScreenTensor_kernel a b
  have hkInv := (complex_null_kernel_iff frame.components frame.isBasis.1 ξ k hξ hs).mpr htarget
  have hkKernel : ∀ i j, complexRicciSymbol gInv ξ k i j = 0 := by
    simpa only [frame.inverseMetric_eq] using hkInv
  refine ⟨k, hkSymm, hkKernel, ?_⟩
  simp [screenCoordinates, hk]

/-- The original physical Hermitian form is the standard nondegenerate form
on the two actual coordinates, with the ordered-pair multiplicity factor two. -/
theorem hermitianPhysicalPairing_eq_coordinates
    (gInv : Tensor2) (frame : TensorFrame.LorentzFrame gInv)
    (ξ : Covector) (hnormal : TensorFrame.covector frame.components ξ = NullScreen.nullCovector)
    (k l : ComplexTensor2) (hkSymm : IsSymmetricComplexTensor k)
    (hlSymm : IsSymmetricComplexTensor l)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) :
    hermitianPhysicalPairing gInv k l =
      2 * ((screenCoordinates frame.components k).1 * conj (screenCoordinates frame.components l).1 +
           (screenCoordinates frame.components k).2 * conj (screenCoordinates frame.components l).2) := by
  have hkN := normalized_complex_kernel gInv frame ξ hnormal k hk
  have hlN := normalized_complex_kernel gInv frame ξ hnormal l hl
  calc
    hermitianPhysicalPairing gInv k l =
        hermitianPhysicalPairing (TensorFrame.inverseMetric frame.components) k l := by
      rw [frame.inverseMetric_eq]
    _ = hermitianPhysicalPairing TensorFrame.standardInverse
        (complexTensor frame.components k) (complexTensor frame.components l) :=
      hermitianPhysicalPairing_transform frame.components k l
    _ = _ := HermitianScreen.hermitianPhysicalPairing_eq_screen _ _
      (complexTensor_symmetric frame.components k hkSymm)
      (complexTensor_symmetric frame.components l hlSymm) hkN hlN

end Burnett.RicciSymbol.NullNormalForm
