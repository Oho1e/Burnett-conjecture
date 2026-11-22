import Burnett.Analysis.Microlocal.CompactLimitFunctional

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CompactSquarePositivity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.SeparablePositive
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate

private def baseConjugate (p : BasePolynomial × BasePolynomial) :
    BasePolynomial × BasePolynomial :=
  (p.1, -p.2)

private def baseProduct (p q : BasePolynomial × BasePolynomial) :
    BasePolynomial × BasePolynomial :=
  (MvPolynomial.X none * (p.1 * q.1) - MvPolynomial.X none * (p.2 * q.2),
   MvPolynomial.X none * (p.1 * q.2) + MvPolynomial.X none * (p.2 * q.1))

private theorem baseConjugate_apply (K : BallData) (p : BasePolynomial × BasePolynomial) (x : Space) :
    baseSymbol K (baseConjugate p) x = conj (baseSymbol K p x) :=
  complexBase_conj K p x

private theorem baseProduct_apply (K : BallData) (p q : BasePolynomial × BasePolynomial) (x : Space) :
    baseSymbol K (baseProduct p q) x = baseSymbol K p x * baseSymbol K q x :=
  complexBase_mul K p q x

private def angleConjugate (p : RationalPolynomial × RationalPolynomial) :
    RationalPolynomial × RationalPolynomial :=
  (p.1, -p.2)

private def angleProduct (p q : RationalPolynomial × RationalPolynomial) :
    RationalPolynomial × RationalPolynomial :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

private def angleEval (ξ : Space) : RationalPolynomial →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (fun i => angularCoordinate i ξ)

private theorem angleConjugate_apply (p : RationalPolynomial × RationalPolynomial) (ξ : Space) :
    complexRationalAngularSymbol (angleConjugate p) ξ = conj (complexRationalAngularSymbol p ξ) := by
  change ((angleEval ξ p.1 : ℝ) : ℂ) + Complex.I * ((angleEval ξ (-p.2) : ℝ) : ℂ) =
    conj (((angleEval ξ p.1 : ℝ) : ℂ) + Complex.I * ((angleEval ξ p.2 : ℝ) : ℂ))
  simp

private theorem angleProduct_apply (p q : RationalPolynomial × RationalPolynomial) (ξ : Space) :
    complexRationalAngularSymbol (angleProduct p q) ξ =
      complexRationalAngularSymbol p ξ * complexRationalAngularSymbol q ξ := by
  let e := angleEval ξ
  change (e (p.1 * q.1 - p.2 * q.2) : ℂ) + Complex.I * (e (p.1 * q.2 + p.2 * q.1) : ℂ) =
    ((e p.1 : ℂ) + Complex.I * (e p.2 : ℂ)) *
      ((e q.1 : ℂ) + Complex.I * (e q.2 : ℂ))
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private def pairTerm (p q : TermParameters) : TermParameters :=
  (baseProduct p.1 (baseConjugate q.1), angleProduct (angleConjugate q.2) p.2)

/-- Cartesian list of terms for one symbol times the complex conjugate of another. -/
def conjugateProductParameters (ps qs : SeparableParameters) : SeparableParameters :=
  ps.flatMap (fun p => qs.map (pairTerm p))

private theorem sum_map_cross {α β γ δ : Type} [AddMonoid δ]
    (ps : List α) (qs : List β) (f : α → β → γ) (g : γ → δ) :
    (((ps.flatMap fun p => qs.map (f p))).map g).sum =
      (ps.map fun p => (qs.map fun q => g (f p q)).sum).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        List.map_cons, List.sum_cons, ih]
      rfl

private theorem pairTerm_apply (K : BallData) (p q : TermParameters) (x ξ : Space) :
    baseSymbol K (pairTerm p q).1 x * complexRationalAngularSymbol (pairTerm p q).2 ξ =
      (baseSymbol K p.1 x * complexRationalAngularSymbol p.2 ξ) *
        conj (baseSymbol K q.1 x * complexRationalAngularSymbol q.2 ξ) := by
  simp only [pairTerm, baseProduct_apply, baseConjugate_apply,
    angleProduct_apply, angleConjugate_apply, map_mul]
  ring

theorem separableValue_conjugateProduct (K : BallData) (ps qs : SeparableParameters) (x ξ : Space) :
    separableValue K (conjugateProductParameters ps qs) x ξ =
      separableValue K ps x ξ * conj (separableValue K qs x ξ) := by
  let g (t : TermParameters) := baseSymbol K t.1 x * complexRationalAngularSymbol t.2 ξ
  change (((ps.flatMap fun p => qs.map (pairTerm p))).map g).sum =
    (ps.map g).sum * conj (qs.map g).sum
  rw [sum_map_cross]
  have h (p : TermParameters) :
      (qs.map fun q => g (pairTerm p q)).sum = g p * conj (qs.map g).sum := by
    change (qs.map fun q =>
      baseSymbol K (pairTerm p q).1 x * complexRationalAngularSymbol (pairTerm p q).2 ξ).sum = _
    simp_rw [pairTerm_apply]
    rw [List.sum_map_mul_left, map_list_sum, List.map_map]
    rfl
  simp_rw [h, List.sum_map_mul_right]

theorem separableRestriction_conjugateProduct (K : BallData) (ps qs : SeparableParameters) :
    separableRestriction K (conjugateProductParameters ps qs) =
      separableRestriction K ps * star (separableRestriction K qs) := by
  ext v
  obtain ⟨x, ξ⟩ := v
  rw [ContinuousMap.mul_apply, ContinuousMap.star_apply]
  simp only [separableRestriction_apply, Complex.star_def]
  exact separableValue_conjugateProduct K ps qs x ξ

theorem separableRestriction_absoluteSquare (K : BallData) (ps : SeparableParameters) :
    separableRestriction K (conjugateProductParameters ps ps) =
      star (separableRestriction K ps) * separableRestriction K ps := by
  rw [separableRestriction_conjugateProduct, mul_comm]

private theorem symbolL2_congr_values (a b : BoundedSymbol Space)
    (h : ∀ x, a x = b x) (u : ComplexL2 Space) :
    symbolL2 a u = symbolL2 b u := by
  apply Lp.ext
  filter_upwards [symbolL2_ae a u, symbolL2_ae b u] with x ha hb
  rw [ha, hb, h x]

private theorem pairTerm_operator (K : BallData) (p q : TermParameters) :
    separableOperator (baseSymbol K (pairTerm p q).1) (complexRationalAngularSymbol (pairTerm p q).2) =
      squareSymbolTerm (baseSymbol K p.1) (baseSymbol K q.1)
        (complexRationalAngularSymbol p.2) (complexRationalAngularSymbol q.2) := by
  let a := baseSymbol K (pairTerm p q).1
  let m := complexRationalAngularSymbol (pairTerm p q).2
  let ae := productSymbol (baseSymbol K p.1) (conjugateSymbol (baseSymbol K q.1))
  let me := productSymbol (conjugateSymbol (complexRationalAngularSymbol q.2))
    (complexRationalAngularSymbol p.2)
  have ha (x : Space) : a x = ae x := by
    change baseSymbol K (pairTerm p q).1 x =
      productSymbol (baseSymbol K p.1) (conjugateSymbol (baseSymbol K q.1)) x
    simp only [pairTerm, baseProduct_apply, baseConjugate_apply, productSymbol_apply, conjugateSymbol_apply]
  have hm (ξ : Space) : m ξ = me ξ := by
    change complexRationalAngularSymbol (pairTerm p q).2 ξ =
      productSymbol (conjugateSymbol (complexRationalAngularSymbol q.2)) (complexRationalAngularSymbol p.2) ξ
    simp only [pairTerm, angleProduct_apply, angleConjugate_apply, productSymbol_apply, conjugateSymbol_apply]
  apply ContinuousLinearMap.ext
  intro u
  change symbolL2 a (fourierMultiplier m u) = symbolL2 ae (fourierMultiplier me u)
  have hfreq : fourierMultiplier m u = fourierMultiplier me u := by
    rw [fourierMultiplier_apply, fourierMultiplier_apply, symbolL2_congr_values m me hm]
  rw [hfreq, symbolL2_congr_values a ae ha]

private theorem sum_via_get {α β : Type} [AddCommMonoid β] (ps : List α) (f : α → β) :
    (ps.map f).sum = ∑ i : Fin ps.length, f (ps.get i) := by
  calc
    _ = ((List.ofFn ps.get).map f).sum := by rw [List.ofFn_get]
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem listOperator_absoluteSquare (K : BallData) (ps : SeparableParameters) :
    listOperator K (conjugateProductParameters ps ps) =
      finiteSquareOperator
        (fun i : Fin ps.length => baseSymbol K (ps.get i).1)
        (fun i : Fin ps.length => complexRationalAngularSymbol (ps.get i).2) := by
  unfold listOperator conjugateProductParameters finiteSquareOperator
  rw [sum_map_cross, sum_via_get]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_via_get]
  exact Finset.sum_congr rfl (fun j _ => pairTerm_operator K (ps.get i) (ps.get j))

end Burnett.Microlocal.CompactSquarePositivity

namespace Burnett.Microlocal.CompactSquarePositivity

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.SeparablePositive
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate

/-- On the specified subsequence the actual diagonal functional is positive on each list square. -/
theorem listSquare_positive_of_matching_limits (K : BallData)
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n x, f n x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : Burnett.X02.SobolevTestJet.D,
      Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (G : TestSpace K →L[ℂ] ℂ)
    (hG : ∀ ps : SeparableParameters,
      Tendsto (fun n =>
        let u := (sourceSchwartz (hs (σ n)) χ₀ (hχ₀ (σ n))).toLp 2 volume
        inner ℂ u (listOperator K ps u)) atTop (𝓝 (G (separableRestriction K ps))))
    (ps : SeparableParameters) :
    let q := separableRestriction K ps
    0 ≤ (G (star q * q)).re ∧ (G (star q * q)).im = 0 := by
  intro q
  let a (i : Fin ps.length) := baseSymbol K (ps.get i).1
  let m (i : Fin ps.length) := complexRationalAngularSymbol (ps.get i).2
  let z := G (star q * q)
  have hz := hG (conjugateProductParameters ps ps)
  rw [listOperator_absoluteSquare, separableRestriction_absoluteSquare] at hz
  have hc := (Complex.continuous_conj.tendsto z).comp hz
  have hc' : Tendsto (fun n =>
      let u := (sourceSchwartz (hs (σ n)) χ₀ (hχ₀ (σ n))).toLp 2 volume
      inner ℂ (finiteSquareOperator a m u) u) atTop (𝓝 (conj z)) := by
    apply hc.congr
    intro n
    let u := (sourceSchwartz (hs (σ n)) χ₀ (hχ₀ (σ n))).toLp 2 volume
    exact inner_conj_symm (finiteSquareOperator a m u) u
  have h := finiteSquare_pair_limit_nonnegative_of_localized_weak_zero a m
    (fun i => complexBase_contDiff K (ps.get i).1)
    (fun i => complexBase_hasCompactSupport K (ps.get i).1)
    (fun i => complexRationalAngular_contDiffOn (ps.get i).2)
    (fun i => complexRationalAngular_degreeZero (ps.get i).2)
    (fun n => f (σ n)) (fun n => hs (σ n)) (fun n => hf (σ n)) χ₀ (fun n => hχ₀ (σ n))
    B (fun n => hB (σ n)) (fun φ => (ht φ).comp hσ.tendsto_atTop) (conj z) hc'
  have hreal : 0 ≤ z.re := by simpa only [Complex.conj_re] using h.1
  have him : z.im = 0 := by
    have hi : -z.im = 0 := by simpa only [Complex.conj_im] using h.2
    exact neg_eq_zero.mp hi
  exact ⟨hreal, him⟩

/-- The same extracted diagonal functionals and ordered limits, with positivity on every list square. -/
theorem exists_commonCompactDiagonalFunctional_listSquare_positive {κ : Type} [Countable κ]
    (K : BallData) (f : ℕ → κ → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n c x, f n c x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : κ) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    let u (n : ℕ) (c : κ) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L : SeparableParameters → κ → κ → ℂ,
      ∃ G : κ → (TestSpace K →L[ℂ] ℂ),
        (∀ ps c d, Tendsto (fun n => inner ℂ (u (σ n) d) (listOperator K ps (u (σ n) c)))
          atTop (𝓝 (L ps c d))) ∧
        (∀ c ps, G c (separableRestriction K ps) = L ps c c) ∧
        (∀ c g, ‖G c g‖ ≤ B ^ 2 * ‖g‖) ∧
        ∀ c ps, let q := separableRestriction K ps
          0 ≤ (G c (star q * q)).re ∧ (G c (star q * q)).im = 0 := by
  intro u
  obtain ⟨σ, hσ, L, G, hL, hG, hB'⟩ :=
    exists_commonCompactDiagonalFunctional K f hs hf χ₀ hχ₀ hKf B hB ht
  refine ⟨σ, hσ, L, G, hL, hG, hB', fun c ps => ?_⟩
  apply listSquare_positive_of_matching_limits K (fun n => f n c) (fun n => hs n c)
    (fun n => hf n c) χ₀ (fun n => hχ₀ n c) B (fun n => hB n c) (ht c) σ hσ (G c) _ ps
  intro qs
  rw [hG]
  exact hL qs c c

end Burnett.Microlocal.CompactSquarePositivity
