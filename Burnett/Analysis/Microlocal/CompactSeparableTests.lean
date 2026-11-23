import Burnett.Analysis.Microlocal.RationalAngularDensity
import Burnett.Analysis.Microlocal.CompactChartInput
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Algebra.BigOperators.Ring.List

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SmoothBaseTests

open Set MvPolynomial Burnett.Microlocal.SmoothAngularTests
open scoped ContDiff ComplexConjugate

def BallData.cutoff (K : BallData) : ContDiffBump K.center :=
  ⟨K.radius + 1, K.radius + 2, by linarith [K.nonnegative], by linarith⟩

theorem cutoff_one_on_larger_ball (K : BallData) {x : Space}
    (hx : x ∈ Metric.closedBall K.center (K.radius + 1)) : K.cutoff x = 1 :=
  K.cutoff.one_of_mem_closedBall hx

theorem cutoff_one_on_ball (K : BallData) {x : Space} (hx : x ∈ K.closedBall) :
    K.cutoff x = 1 :=
  cutoff_one_on_larger_ball K
    (Metric.closedBall_subset_closedBall (le_add_of_nonneg_right zero_le_one) hx)

theorem cutoff_one_near_ball (K : BallData) :
    ∃ U : Set Space, IsOpen U ∧ K.closedBall ⊆ U ∧ Set.EqOn K.cutoff (fun _ => 1) U :=
  ⟨Metric.ball K.center (K.radius + 1), Metric.isOpen_ball,
    Metric.closedBall_subset_ball (by linarith), fun _ hx =>
      cutoff_one_on_larger_ball K (Metric.ball_subset_closedBall hx)⟩

abbrev BasePolynomial := MvPolynomial (Option (Fin 4)) ℚ

/-- The additional variable records powers of the common compact cutoff. -/
def baseVariable (K : BallData) : Option (Fin 4) → Space → ℝ
  | none => K.cutoff
  | some i => fun x => x i

theorem baseVariable_contDiff (K : BallData) (i : Option (Fin 4)) :
    ContDiff ℝ ∞ (baseVariable K i) := by
  cases i with
  | none => exact K.cutoff.contDiff
  | some i => exact (PiLp.proj 2 (fun _ : Fin 4 => ℝ) i : Space →L[ℝ] ℝ).contDiff

private theorem polynomial_contDiff {σ : Type} (v : σ → Space → ℝ)
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (p : MvPolynomial σ ℚ) :
    ContDiff ℝ ∞ (fun x => p.eval₂ (Rat.castHom ℝ) (fun i => v i x)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval₂_C] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : Space => (Rat.castHom ℝ) c))
  | add p q hp hq => simpa only [eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [eval₂_mul, eval₂_X] using hp.mul (hv i)

/-- Every term has an outer factor of the chosen cutoff. -/
def rationalBase (K : BallData) (p : BasePolynomial) (x : Space) : ℝ :=
  K.cutoff x * p.eval₂ (Rat.castHom ℝ) (fun i => baseVariable K i x)

theorem rationalBase_contDiff (K : BallData) (p : BasePolynomial) :
    ContDiff ℝ ∞ (rationalBase K p) :=
  K.cutoff.contDiff.mul (polynomial_contDiff _ (baseVariable_contDiff K) p)

theorem rationalBase_hasCompactSupport (K : BallData) (p : BasePolynomial) :
    HasCompactSupport (rationalBase K p) :=
  K.cutoff.hasCompactSupport.mul_right

theorem rationalBase_add (K : BallData) (p q : BasePolynomial) (x : Space) :
    rationalBase K (p + q) x = rationalBase K p x + rationalBase K q x := by
  simp only [rationalBase, eval₂_add, mul_add]

theorem rationalBase_sub (K : BallData) (p q : BasePolynomial) (x : Space) :
    rationalBase K (p - q) x = rationalBase K p x - rationalBase K q x := by
  change K.cutoff x * eval₂Hom _ _ (p - q) = _
  rw [map_sub, mul_sub]
  rfl

theorem rationalBase_neg (K : BallData) (p : BasePolynomial) (x : Space) :
    rationalBase K (-p) x = -rationalBase K p x := by
  change K.cutoff x * eval₂Hom _ _ (-p) = _
  rw [map_neg, mul_neg]
  rfl

theorem rationalBase_mul (K : BallData) (p q : BasePolynomial) (x : Space) :
    rationalBase K (X none * (p * q)) x =
      rationalBase K p x * rationalBase K q x := by
  simp only [rationalBase, eval₂_mul, eval₂_X, baseVariable]
  ring

theorem rationalBase_const_mul (K : BallData) (c : ℚ) (p : BasePolynomial) (x : Space) :
    rationalBase K (MvPolynomial.C c * p) x = (c : ℝ) * rationalBase K p x := by
  simp only [rationalBase, eval₂_mul, eval₂_C]
  change  K.cutoff x * ((c : ℝ) * _) = _
  ring

def complexBase (K : BallData) (p : BasePolynomial × BasePolynomial) (x : Space) : ℂ :=
  (rationalBase K p.1 x : ℂ) + Complex.I * (rationalBase K p.2 x : ℂ)

theorem complexBase_contDiff (K : BallData) (p : BasePolynomial × BasePolynomial) :
    ContDiff ℝ ∞ (complexBase K p) := by
  have hc (q : BasePolynomial) : ContDiff ℝ ∞ (fun x => (rationalBase K q x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (rationalBase_contDiff K q)
  exact (hc p.1).add (contDiff_const.mul (hc p.2))

theorem complexBase_hasCompactSupport (K : BallData) (p : BasePolynomial × BasePolynomial) :
    HasCompactSupport (complexBase K p) := by
  have hc (q : BasePolynomial) : HasCompactSupport (fun x => (rationalBase K q x : ℂ)) :=
    (rationalBase_hasCompactSupport K q).comp_left Complex.ofReal_zero
  exact (hc p.1).add (hc p.2).mul_left

theorem complexBase_tsupport_subset (K : BallData) (p : BasePolynomial × BasePolynomial) :
    tsupport (complexBase K p) ⊆ Metric.closedBall K.center (K.radius + 2) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  by_contra hx'
  have hn : x ∉ tsupport K.cutoff := by
    rw [K.cutoff.tsupport_eq]
    exact hx'
  have hzero := image_eq_zero_of_notMem_tsupport hn
  exact (Function.mem_support.mp hx) (by simp [complexBase, rationalBase, hzero])

theorem complexBase_add (K : BallData) (p q : BasePolynomial × BasePolynomial) (x : Space) :
    complexBase K (p.1 + q.1, p.2 + q.2) x = complexBase K p x + complexBase K q x := by
  simp only [complexBase, rationalBase_add, Complex.ofReal_add]
  ring

theorem complexBase_conj (K : BallData) (p : BasePolynomial × BasePolynomial) (x : Space) :
    complexBase K (p.1, -p.2) x = conj (complexBase K p x) := by
  simp [complexBase, rationalBase_neg]

theorem complexBase_mul (K : BallData) (p q : BasePolynomial × BasePolynomial) (x : Space) :
    complexBase K
      (X none * (p.1 * q.1) - X none * (p.2 * q.2),
       X none * (p.1 * q.2) + X none * (p.2 * q.1)) x =
      complexBase K p x * complexBase K q x := by
  apply Complex.ext
  · simp [complexBase, rationalBase_add, rationalBase_sub, rationalBase_mul, Complex.mul_re,
      Complex.mul_im]
  · simp [complexBase, rationalBase_add, rationalBase_sub, rationalBase_mul, Complex.mul_re,
      Complex.mul_im]

theorem exists_complexBase_absolute_square (K : BallData) (p : BasePolynomial × BasePolynomial) :
    ∃ q : BasePolynomial × BasePolynomial, ∀ x : Space,
      complexBase K q x = complexBase K p x * conj (complexBase K p x) := by
  let c := (p.1, -p.2)
  refine ⟨(X none * (p.1 * c.1) - X none * (p.2 * c.2),
    X none * (p.1 * c.2) + X none * (p.2 * c.1)), fun x => ?_⟩
  rw [complexBase_mul, complexBase_conj]

theorem complexBase_const_mul (K : BallData) (c d : ℚ)
    (p : BasePolynomial × BasePolynomial) (x : Space) :
    complexBase K
      (MvPolynomial.C c * p.1 - MvPolynomial.C d * p.2,
       MvPolynomial.C c * p.2 + MvPolynomial.C d * p.1) x =
      ((c : ℝ) + Complex.I * (d : ℝ)) * complexBase K p x := by
  apply Complex.ext
  · simp [complexBase, rationalBase_add, rationalBase_sub, rationalBase_const_mul, Complex.mul_re,
      Complex.mul_im]
  · simp [complexBase, rationalBase_add, rationalBase_sub, rationalBase_const_mul, Complex.mul_re,
      Complex.mul_im]

private theorem compact_continuous_bound (f : Space → ℂ)
    (hc : Continuous f) (hK : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Space, ‖f x‖ ≤ B := by
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨B, hB, hbd⟩ := (hK'.image hc).isBounded.exists_pos_norm_le
  exact ⟨B, hB.le, fun x => by
    by_cases hx : x ∈ tsupport f
    · exact hbd _ ⟨x, hx, rfl⟩
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact hB.le⟩

def baseSymbol (K : BallData) (p : BasePolynomial × BasePolynomial) :
    Burnett.Fourier.BoundedSymbol Space where
  toFun := complexBase K p
  measurable := (complexBase_contDiff K p).continuous.measurable.aestronglyMeasurable
  bound := (compact_continuous_bound _ (complexBase_contDiff K p).continuous
    (complexBase_hasCompactSupport K p)).choose
  bound_nonneg := (compact_continuous_bound _ (complexBase_contDiff K p).continuous
    (complexBase_hasCompactSupport K p)).choose_spec.1
  norm_le := (compact_continuous_bound _ (complexBase_contDiff K p).continuous
    (complexBase_hasCompactSupport K p)).choose_spec.2

section ContinuousMaps

variable {Z σ : Type} [TopologicalSpace Z]

private def rationalEval (g : σ → C(Z, ℝ)) : MvPolynomial σ ℚ →+* C(Z, ℝ) :=
  MvPolynomial.eval₂Hom (algebraMap ℚ C(Z, ℝ)) g

private theorem rationalEval_apply (g : σ → C(Z, ℝ)) (p : MvPolynomial σ ℚ) (x : Z) :
    rationalEval g p x = p.eval₂ (Rat.castHom ℝ) (fun i => g i x) := by
  change (ContinuousMap.evalAlgHom ℚ ℝ x).toRingHom
    (p.eval₂ (algebraMap ℚ C(Z, ℝ)) g) = _
  rw [MvPolynomial.eval₂_comp_left]
  rfl

private def rationalClosure [CompactSpace Z] (g : σ → C(Z, ℝ)) : Subalgebra ℝ C(Z, ℝ) where
  __ := (rationalEval g).range.topologicalClosure.toSubsemiring
  algebraMap_mem' := by
    intro r
    change ContinuousMap.const Z r ∈ closure (Set.range (rationalEval g))
    have hr : r ∈ closure (Set.range fun q : ℚ => (q : ℝ)) := Rat.denseRange_cast r
    have hm := image_closure_subset_closure_image (f := ContinuousMap.const Z)
      (s := Set.range fun q : ℚ => (q : ℝ)) ContinuousMap.continuous_const'
    refine closure_mono ?_ (hm ⟨r, hr, rfl⟩)
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨MvPolynomial.C q, ?_⟩
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C q) = _
    rw [MvPolynomial.eval₂_C]
    rfl

private theorem rationalEval_dense [CompactSpace Z] [T2Space Z]
    (g : σ → C(Z, ℝ)) (hsep : ∀ x y, x ≠ y → ∃ i, g i x ≠ g i y) :
    DenseRange (rationalEval g) := by
  let A := Algebra.adjoin ℝ (Set.range g)
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    have hmem : g i ∈ A := Algebra.subset_adjoin (Set.mem_range_self i)
    exact ⟨_, ⟨g i, hmem, rfl⟩, hi⟩
  have hle : A ≤ rationalClosure g := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change g i ∈ closure (Set.range (rationalEval g))
    exact subset_closure ⟨MvPolynomial.X i, MvPolynomial.eval₂_X _ _ _⟩
  have htop := Subalgebra.topologicalClosure_minimal hle
    (show IsClosed (rationalClosure g : Set C(Z, ℝ)) from isClosed_closure)
  rw [ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA] at htop
  intro f
  exact htop (show f ∈ (⊤ : Subalgebra ℝ C(Z, ℝ)) from trivial)

private def complexPair (f : C(Z, ℝ) × C(Z, ℝ)) : C(Z, ℂ) :=
  (⟨Complex.ofReal, Complex.ofRealCLM.continuous⟩ : C(ℝ, ℂ)).comp f.1 +
    ContinuousMap.const Z Complex.I *
      (⟨Complex.ofReal, Complex.ofRealCLM.continuous⟩ : C(ℝ, ℂ)).comp f.2

private theorem continuous_complexPair [CompactSpace Z] : Continuous (complexPair (Z := Z)) :=
  ((ContinuousMap.continuous_postcomp _).comp continuous_fst).add
    (continuous_const.mul ((ContinuousMap.continuous_postcomp _).comp continuous_snd))

private def complexEval (g : σ → C(Z, ℝ)) (p : MvPolynomial σ ℚ × MvPolynomial σ ℚ) :
    C(Z, ℂ) :=
  complexPair (rationalEval g p.1, rationalEval g p.2)

private theorem complexEval_dense [CompactSpace Z] [T2Space Z]
    (g : σ → C(Z, ℝ)) (hsep : ∀ x y, x ≠ y → ∃ i, g i x ≠ g i y) :
    DenseRange (complexEval g) := by
  intro f
  let q : C(Z, ℝ) × C(Z, ℝ) :=
    ((⟨Complex.re, Complex.reCLM.continuous⟩ : C(ℂ, ℝ)).comp f,
      (⟨Complex.im, Complex.imCLM.continuous⟩ : C(ℂ, ℝ)).comp f)
  let S := Set.range (rationalEval g)
  have hq : q ∈ closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact ⟨rationalEval_dense g hsep q.1, rationalEval_dense g hsep q.2⟩
  have himage : complexPair q ∈ closure (complexPair '' (S ×ˢ S)) :=
    image_closure_subset_closure_image continuous_complexPair ⟨q, hq, rfl⟩
  have hsub : complexPair '' (S ×ˢ S) ⊆ Set.range (complexEval g) := by
    rintro _ ⟨⟨u, v⟩, ⟨⟨p, rfl⟩, ⟨r, rfl⟩⟩, rfl⟩
    exact ⟨(p, r), rfl⟩
  have hqf : complexPair q = f := by
    ext x
    change ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ) = f x
    rw [mul_comm]
    exact Complex.re_add_im _
  simpa only [hqf] using closure_mono hsub himage

end ContinuousMaps

private def baseCoordinate (K : BallData) (i : Option (Fin 4)) : C(K.Point, ℝ) where
  toFun x := baseVariable K i x
  continuous_toFun := (baseVariable_contDiff K i).continuous.comp continuous_subtype_val

private theorem baseCoordinate_separates (K : BallData) (x y : K.Point) (hxy : x ≠ y) :
    ∃ i, baseCoordinate K i x ≠ baseCoordinate K i y := by
  by_contra! h
  exact hxy (Subtype.ext (PiLp.ext fun i => h (some i)))

def complexBaseOnBall (K : BallData) (p : BasePolynomial × BasePolynomial) : C(K.Point, ℂ) :=
  complexEval (baseCoordinate K) p

theorem complexBaseOnBall_apply (K : BallData) (p : BasePolynomial × BasePolynomial)
    (x : K.Point) : complexBaseOnBall K p x = baseSymbol K p x := by
  change (rationalEval (baseCoordinate K) p.1 x : ℂ) +
    Complex.I * (rationalEval (baseCoordinate K) p.2 x : ℂ) = _
  simp only [rationalEval_apply, complexBase, rationalBase, baseSymbol, baseCoordinate,
    cutoff_one_on_ball K x.property, one_mul]
  rfl

theorem complexBaseOnBall_dense (K : BallData) : DenseRange (complexBaseOnBall K) :=
  complexEval_dense _ (baseCoordinate_separates K)

private theorem countableFinsupp (α β : Type) [Countable α] [Countable β] [Zero β] :
    Countable (α →₀ β) := by
  classical
  letI : Encodable (α × β) := Encodable.ofCountable _
  letI : Countable (Finset (α × β)) := List.toFinset_surjective.countable
  exact (Finsupp.graph_injective α β).countable

private theorem countablePolynomial (σ : Type) [Countable σ] : Countable (MvPolynomial σ ℚ) := by
  letI : Countable (σ →₀ ℕ) := countableFinsupp _ _
  exact countableFinsupp (σ →₀ ℕ) ℚ

theorem exists_dense_base_enumeration (K : BallData) :
    ∃ e : ℕ → BasePolynomial × BasePolynomial,
      Function.Surjective e ∧ DenseRange (complexBaseOnBall K ∘ e) := by
  letI : Countable BasePolynomial := countablePolynomial _
  obtain ⟨e, he⟩ := exists_surjective_nat (BasePolynomial × BasePolynomial)
  refine ⟨e, he, fun f => closure_mono ?_ (complexBaseOnBall_dense K f)⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨n, rfl⟩ := he p
  exact ⟨n, rfl⟩

abbrev TermParameters :=
  (BasePolynomial × BasePolynomial) × (RationalPolynomial × RationalPolynomial)

abbrev SeparableParameters := List TermParameters

def separableValue (K : BallData) (ps : SeparableParameters) (x ξ : Space) : ℂ :=
  (ps.map fun p => baseSymbol K p.1 x * complexRationalAngularSymbol p.2 ξ).sum

private def restrictedTerm (K : BallData) (p : TermParameters) : C(K.Point × UnitSphere, ℂ) :=
  (complexBaseOnBall K p.1).comp ⟨Prod.fst, continuous_fst⟩ *
    (complexRationalSphere p.2).comp ⟨Prod.snd, continuous_snd⟩

def separableRestriction (K : BallData) (ps : SeparableParameters) : C(K.Point × UnitSphere, ℂ) :=
  (ps.map (restrictedTerm K)).sum

theorem separableRestriction_apply (K : BallData) (ps : SeparableParameters)
    (x : K.Point) (ξ : UnitSphere) : separableRestriction K ps (x, ξ) = separableValue K ps x ξ := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change restrictedTerm K p (x, ξ) + separableRestriction K ps (x, ξ) =
        baseSymbol K p.1 x * complexRationalAngularSymbol p.2 ξ + separableValue K ps x ξ
      rw [ih]
      change complexBaseOnBall K p.1 x * complexRationalSphere p.2 ξ + _ = _
      rw [complexBaseOnBall_apply, complexRationalSphere_apply]

abbrev ProductVariables := Option (Fin 4) ⊕ Fin 4

private def productCoordinate (K : BallData) : ProductVariables → C(K.Point × UnitSphere, ℝ)
  | Sum.inl i => (baseCoordinate K i).comp ⟨Prod.fst, continuous_fst⟩
  | Sum.inr i => (sphereCoordinate i).comp ⟨Prod.snd, continuous_snd⟩

private theorem productCoordinate_separates (K : BallData) (x y : K.Point × UnitSphere)
    (hxy : x ≠ y) : ∃ i, productCoordinate K i x ≠ productCoordinate K i y := by
  by_cases h : x.1 = y.1
  · have hs : x.2 ≠ y.2 := fun he => hxy (Prod.ext h he)
    obtain ⟨i, hi⟩ := sphereCoordinate_separates x.2 y.2 hs
    exact ⟨Sum.inr i, hi⟩
  · obtain ⟨i, hi⟩ := baseCoordinate_separates K x.1 y.1 h
    exact ⟨Sum.inl i, hi⟩

private def realTerm (K : BallData) (p : BasePolynomial × RationalPolynomial)
    (v : K.Point × UnitSphere) : ℝ :=
  rationalEval (baseCoordinate K) p.1 v.1 * rationalSphereEval p.2 v.2

private theorem realTerm_mul_base (K : BallData) (p : BasePolynomial × RationalPolynomial)
    (i : Option (Fin 4)) (v : K.Point × UnitSphere) :
    realTerm K (p.1 * X i, p.2) v = realTerm K p v * productCoordinate K (Sum.inl i) v := by
  have h : rationalEval (baseCoordinate K) (X i) = baseCoordinate K i := eval₂_X _ _ _
  simp only [realTerm, map_mul, h, productCoordinate, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ContinuousMap.mul_apply]
  ring

private theorem realTerm_mul_angle (K : BallData) (p : BasePolynomial × RationalPolynomial)
    (i : Fin 4) (v : K.Point × UnitSphere) :
    realTerm K (p.1, p.2 * X i) v = realTerm K p v * productCoordinate K (Sum.inr i) v := by
  have h : rationalSphereEval (X i) = sphereCoordinate i := eval₂_X _ _ _
  simp only [realTerm, map_mul, h, productCoordinate, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ContinuousMap.mul_apply]
  ring

private theorem product_eval_exists_real_terms (K : BallData)
    (p : MvPolynomial ProductVariables ℚ) :
    ∃ ps : List (BasePolynomial × RationalPolynomial), ∀ v : K.Point × UnitSphere,
      rationalEval (productCoordinate K) p v = (ps.map fun t => realTerm K t v).sum := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨[(MvPolynomial.C c, MvPolynomial.C 1)], fun v => ?_⟩
      simp [realTerm, rationalEval_apply, rationalSphereEval_apply, rationalAngular, eval₂_C]
  | add p q hp hq =>
      obtain ⟨ps, hp⟩ := hp
      obtain ⟨qs, hq⟩ := hq
      refine ⟨ps ++ qs, fun v => ?_⟩
      simp only [map_add, ContinuousMap.add_apply, hp, hq, List.map_append, List.sum_append]
  | mul_X p i hp =>
      obtain ⟨ps, hp⟩ := hp
      have hx : rationalEval (productCoordinate K) (X i) = productCoordinate K i :=
        eval₂_X _ _ _
      cases i with
      | inl j =>
          refine ⟨ps.map (fun t => (t.1 * X j, t.2)), fun v => ?_⟩
          simp only [map_mul, ContinuousMap.mul_apply, hx, hp, List.map_map]
          change _ = (ps.map (fun t => realTerm K (t.1 * X j, t.2) v)).sum
          simp only [realTerm_mul_base, List.sum_map_mul_right]
      | inr j =>
          refine ⟨ps.map (fun t => (t.1, t.2 * X j)), fun v => ?_⟩
          simp only [map_mul, ContinuousMap.mul_apply, hx, hp, List.map_map]
          change _ = (ps.map (fun t => realTerm K (t.1, t.2 * X j) v)).sum
          simp only [realTerm_mul_angle, List.sum_map_mul_right]

private def realPartParam (p : BasePolynomial × RationalPolynomial) : TermParameters :=
  ((p.1, 0), (p.2, 0))

private def imagPartParam (p : BasePolynomial × RationalPolynomial) : TermParameters :=
  ((0, p.1), (p.2, 0))

private theorem complexRationalSphere_real (p : RationalPolynomial) (ξ : UnitSphere) :
    complexRationalSphere (p, 0) ξ = (rationalSphereEval p ξ : ℂ) := by
  rw [complexRationalSphere_apply, rationalSphereEval_apply]
  change complexRationalAngular (p, 0) ξ = _
  simp [complexRationalAngular, rationalAngular, eval₂_zero]

private theorem restrictedTerm_real (K : BallData) (p : BasePolynomial × RationalPolynomial)
    (v : K.Point × UnitSphere) :
    restrictedTerm K (realPartParam p) v = (realTerm K p v : ℂ) := by
  change ((rationalEval (baseCoordinate K) p.1 v.1 : ℂ) +
      Complex.I * (rationalEval (baseCoordinate K) 0 v.1 : ℂ)) *
      complexRationalSphere (p.2, 0) v.2 = (realTerm K p v : ℂ)
  simp [complexRationalSphere_real, realTerm, Complex.ofReal_mul]

private theorem restrictedTerm_imag (K : BallData) (p : BasePolynomial × RationalPolynomial)
    (v : K.Point × UnitSphere) :
    restrictedTerm K (imagPartParam p) v = Complex.I * (realTerm K p v : ℂ) := by
  change ((rationalEval (baseCoordinate K) 0 v.1 : ℂ) +
      Complex.I * (rationalEval (baseCoordinate K) p.1 v.1 : ℂ)) *
      complexRationalSphere (p.2, 0) v.2 = Complex.I * (realTerm K p v : ℂ)
  simp [complexRationalSphere_real, realTerm, Complex.ofReal_mul, mul_assoc]

private theorem separableRestriction_real (K : BallData)
    (ps : List (BasePolynomial × RationalPolynomial)) (v : K.Point × UnitSphere) :
    separableRestriction K (ps.map realPartParam) v = ((ps.map fun t => realTerm K t v).sum : ℂ) := by
  induction ps with
  | nil => simp [separableRestriction]
  | cons p ps ih =>
      change restrictedTerm K (realPartParam p) v + separableRestriction K (ps.map realPartParam) v =
        (↑(realTerm K p v + (ps.map fun t => realTerm K t v).sum) : ℂ)
      rw [restrictedTerm_real, ih, Complex.ofReal_add]

private theorem separableRestriction_imag (K : BallData)
    (ps : List (BasePolynomial × RationalPolynomial)) (v : K.Point × UnitSphere) :
    separableRestriction K (ps.map imagPartParam) v =
      Complex.I * ((ps.map fun t => realTerm K t v).sum : ℂ) := by
  induction ps with
  | nil => simp [separableRestriction]
  | cons p ps ih =>
      change restrictedTerm K (imagPartParam p) v + separableRestriction K (ps.map imagPartParam) v =
        Complex.I * (↑(realTerm K p v + (ps.map fun t => realTerm K t v).sum) : ℂ)
      rw [restrictedTerm_imag, ih, Complex.ofReal_add, mul_add]

private theorem product_eval_exists_separable (K : BallData)
    (p : MvPolynomial ProductVariables ℚ × MvPolynomial ProductVariables ℚ) :
    ∃ ps : SeparableParameters, separableRestriction K ps = complexEval (productCoordinate K) p := by
  obtain ⟨rs, hr⟩ := product_eval_exists_real_terms K p.1
  obtain ⟨is, hi⟩ := product_eval_exists_real_terms K p.2
  refine ⟨rs.map realPartParam ++ is.map imagPartParam, ?_⟩
  ext v
  change separableRestriction K (rs.map realPartParam ++ is.map imagPartParam) v =
    (rationalEval (productCoordinate K) p.1 v : ℂ) +
      Complex.I * (rationalEval (productCoordinate K) p.2 v : ℂ)
  have happ (ps qs : SeparableParameters) :
      separableRestriction K (ps ++ qs) = separableRestriction K ps + separableRestriction K qs := by
    simp [separableRestriction, List.sum_append]
  rw [happ, ContinuousMap.add_apply, separableRestriction_real, separableRestriction_imag, hr, hi]

theorem separableRestriction_dense (K : BallData) : DenseRange (separableRestriction K) := by
  intro f
  refine closure_mono ?_ (complexEval_dense _ (productCoordinate_separates K) f)
  rintro _ ⟨p, rfl⟩
  obtain ⟨ps, hps⟩ := product_eval_exists_separable K p
  exact ⟨ps, hps⟩

theorem exists_dense_separable_enumeration (K : BallData) :
    ∃ e : ℕ → SeparableParameters,
      Function.Surjective e ∧ DenseRange (separableRestriction K ∘ e) := by
  letI : Countable BasePolynomial := countablePolynomial _
  letI : Countable RationalPolynomial := countablePolynomial _
  letI : Encodable TermParameters := Encodable.ofCountable _
  obtain ⟨e, he⟩ := exists_surjective_nat SeparableParameters
  refine ⟨e, he, fun f => closure_mono ?_ (separableRestriction_dense K f)⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨n, rfl⟩ := he p
  exact ⟨n, rfl⟩

theorem exists_separable_uniform_approximation (K : BallData)
    (f : C(K.Point × UnitSphere, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ ps : SeparableParameters, ∀ (x : K.Point) (ξ : UnitSphere),
      ‖separableValue K ps x ξ - f (x, ξ)‖ < ε := by
  obtain ⟨ps, hps⟩ := Metric.denseRange_iff.mp (separableRestriction_dense K) f ε hε
  have hn : ‖separableRestriction K ps - f‖ < ε := by
    rw [← dist_eq_norm, dist_comm]
    exact hps
  refine ⟨ps, fun x ξ => ?_⟩
  have hx := (separableRestriction K ps - f).norm_coe_le_norm (x, ξ)
  simpa only [ContinuousMap.sub_apply, separableRestriction_apply] using hx.trans_lt hn

theorem separableValue_angular_pos_smul (K : BallData) (ps : SeparableParameters)
    (x ξ : Space) (r : ℝ) (hr : 0 < r) :
    separableValue K ps x (r • ξ) = separableValue K ps x ξ := by
  unfold separableValue
  congr 1
  exact congrArg (fun f : TermParameters → ℂ => ps.map f)
    (funext fun p => congrArg (fun u : ℂ => baseSymbol K p.1 x * u)
      (complexRationalAngular_degreeZero p.2 r hr ξ))

end Burnett.Microlocal.SmoothBaseTests
