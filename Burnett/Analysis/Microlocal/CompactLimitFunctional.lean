import Burnett.Analysis.Microlocal.CompactSeparableTests
import Burnett.Analysis.Microlocal.CompactSeparableBound
import Burnett.Analysis.Microlocal.DenseRationalFunctional

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CompactFunctionalProducer

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SeparablePositive
open scoped InnerProduct BigOperators ContDiff Topology

abbrev TestSpace (K : BallData) := C(K.Point × UnitSphere, ℂ)

private def gaussianScalar (r s : ℚ) : ℂ :=
  (r : ℝ) + Complex.I * (s : ℝ)

private def scaleTerm (r s : ℚ) (p : TermParameters) : TermParameters :=
  ((MvPolynomial.C r * p.1.1 - MvPolynomial.C s * p.1.2,
    MvPolynomial.C r * p.1.2 + MvPolynomial.C s * p.1.1), p.2)

/-- Multiply the base factor of each term by the same Gaussian rational. -/
def rationalScale (r s : ℚ) (ps : SeparableParameters) : SeparableParameters :=
  ps.map (scaleTerm r s)

private theorem scaledBaseSymbol_apply (K : BallData) (r s : ℚ) (p : TermParameters) (x : Space) :
    baseSymbol K (scaleTerm r s p).1 x = gaussianScalar r s * baseSymbol K p.1 x :=
  complexBase_const_mul K r s p.1 x

theorem separableRestriction_nil (K : BallData) : separableRestriction K [] = 0 :=
  rfl

theorem separableRestriction_append (K : BallData) (ps qs : SeparableParameters) :
    separableRestriction K (ps ++ qs) = separableRestriction K ps + separableRestriction K qs := by
  simp only [separableRestriction, List.map_append, List.sum_append]

private theorem separableValue_scale (K : BallData) (r s : ℚ)
    (ps : SeparableParameters) (x ξ : Space) :
    separableValue K (rationalScale r s ps) x ξ = gaussianScalar r s * separableValue K ps x ξ := by
  induction ps with
  | nil => simp [rationalScale, separableValue]
  | cons p ps ih =>
      change baseSymbol K (scaleTerm r s p).1 x * complexRationalAngularSymbol p.2 ξ +
        separableValue K (rationalScale r s ps) x ξ =
          gaussianScalar r s *
            (baseSymbol K p.1 x * complexRationalAngularSymbol p.2 ξ + separableValue K ps x ξ)
      rw [scaledBaseSymbol_apply, ih, mul_add, mul_assoc]

theorem separableRestriction_scale (K : BallData) (r s : ℚ) (ps : SeparableParameters) :
    separableRestriction K (rationalScale r s ps) = gaussianScalar r s • separableRestriction K ps := by
  ext v
  obtain ⟨x, ξ⟩ := v
  rw [ContinuousMap.smul_apply, separableRestriction_apply, separableRestriction_apply, smul_eq_mul]
  exact separableValue_scale K r s ps x ξ

theorem separableRestriction_rat_smul (K : BallData) (r : ℚ) (ps : SeparableParameters) :
    separableRestriction K (rationalScale r 0 ps) = r • separableRestriction K ps := by
  rw [separableRestriction_scale, show gaussianScalar r 0 = (r : ℂ) by
    simp [gaussianScalar, Complex.ofReal_ratCast]]
  exact ratCast_smul_eq ℂ ℚ r (separableRestriction K ps)

theorem separableRestriction_I_smul (K : BallData) (ps : SeparableParameters) :
    separableRestriction K (rationalScale 0 1 ps) = Complex.I • separableRestriction K ps := by
  rw [separableRestriction_scale, show gaussianScalar 0 1 = Complex.I by simp [gaussianScalar]]

/-- The actual restrictions of the finite test lists form a rational submodule. -/
def rationalRestrictionModule (K : BallData) : Submodule ℚ (TestSpace K) where
  carrier := Set.range (separableRestriction K)
  zero_mem' := ⟨[], separableRestriction_nil K⟩
  add_mem' := by
    rintro _ _ ⟨ps, rfl⟩ ⟨qs, rfl⟩
    exact ⟨ps ++ qs, separableRestriction_append K ps qs⟩
  smul_mem' := by
    rintro r _ ⟨ps, rfl⟩
    exact ⟨rationalScale r 0 ps, separableRestriction_rat_smul K r ps⟩

theorem rationalRestrictionModule_dense (K : BallData) :
    Dense (rationalRestrictionModule K : Set (TestSpace K)) :=
  separableRestriction_dense K

theorem rationalRestrictionModule_I_mem (K : BallData) (x : rationalRestrictionModule K) :
    Complex.I • (x : TestSpace K) ∈ rationalRestrictionModule K := by
  obtain ⟨ps, he⟩ := x.property
  exact ⟨rationalScale 0 1 ps, (separableRestriction_I_smul K ps).trans (congrArg (Complex.I • ·) he)⟩

/-- A finite list of actual physical-after-Fourier quantizations. -/
def listOperator (K : BallData) (ps : SeparableParameters) : ComplexL2 Space →L[ℂ] ComplexL2 Space :=
  (ps.map fun p => separableOperator (baseSymbol K p.1) (complexRationalAngularSymbol p.2)).sum

theorem listOperator_nil (K : BallData) : listOperator K [] = 0 :=
  rfl

theorem listOperator_append (K : BallData) (ps qs : SeparableParameters) :
    listOperator K (ps ++ qs) = listOperator K ps + listOperator K qs := by
  simp only [listOperator, List.map_append, List.sum_append]

private theorem physical_smul_of_values (a a' : BoundedSymbol Space) (z : ℂ)
    (h : ∀ x, a' x = z * a x) (v : ComplexL2 Space) :
    symbolCLM a' v = z • symbolCLM a v := by
  change symbolL2 a' v = z • symbolL2 a v
  apply Lp.ext
  filter_upwards [symbolL2_ae a' v, symbolL2_ae a v, Lp.coeFn_smul z (symbolL2 a v)]
    with x ha' ha hs
  rw [ha', hs, Pi.smul_apply, smul_eq_mul, ha, h x, mul_assoc]

private theorem scaled_term_operator (K : BallData) (r s : ℚ) (p : TermParameters) :
    separableOperator (baseSymbol K (scaleTerm r s p).1) (complexRationalAngularSymbol p.2) =
      gaussianScalar r s • separableOperator (baseSymbol K p.1) (complexRationalAngularSymbol p.2) := by
  apply ContinuousLinearMap.ext
  intro u
  exact physical_smul_of_values _ _ _ (scaledBaseSymbol_apply K r s p) _

theorem listOperator_scale (K : BallData) (r s : ℚ) (ps : SeparableParameters) :
    listOperator K (rationalScale r s ps) = gaussianScalar r s • listOperator K ps := by
  induction ps with
  | nil => simp only [rationalScale, List.map_nil, listOperator_nil, smul_zero]
  | cons p ps ih =>
      change separableOperator (baseSymbol K (scaleTerm r s p).1) (complexRationalAngularSymbol p.2) +
        listOperator K (rationalScale r s ps) =
        gaussianScalar r s •
          (separableOperator (baseSymbol K p.1) (complexRationalAngularSymbol p.2) + listOperator K ps)
      rw [scaled_term_operator, ih, smul_add]

theorem listOperator_rat_smul (K : BallData) (r : ℚ) (ps : SeparableParameters) :
    listOperator K (rationalScale r 0 ps) = (r : ℂ) • listOperator K ps := by
  rw [listOperator_scale]
  simp [gaussianScalar, Complex.ofReal_ratCast]

theorem listOperator_I_smul (K : BallData) (ps : SeparableParameters) :
    listOperator K (rationalScale 0 1 ps) = Complex.I • listOperator K ps := by
  rw [listOperator_scale]
  simp [gaussianScalar]

private theorem list_sum_via_get {α β : Type} [AddCommMonoid β] (ps : List α) (f : α → β) :
    (ps.map f).sum = ∑ i : Fin ps.length, f (ps.get i) := by
  calc
    _ = ((List.ofFn ps.get).map f).sum := by rw [List.ofFn_get]
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem listOperator_eq_finiteSeparable (K : BallData) (ps : SeparableParameters) :
    listOperator K ps = finiteSeparableOperator
      (fun i : Fin ps.length => baseSymbol K (ps.get i).1)
      (fun i : Fin ps.length => complexRationalAngularSymbol (ps.get i).2) :=
  list_sum_via_get ps _

theorem separableValue_eq_finite (K : BallData) (ps : SeparableParameters) (x ξ : Space) :
    separableValue K ps x ξ = ∑ i : Fin ps.length,
      baseSymbol K (ps.get i).1 x * complexRationalAngularSymbol (ps.get i).2 ξ :=
  list_sum_via_get ps _

end Burnett.Microlocal.CompactFunctionalProducer

namespace Burnett.Microlocal.CompactFunctionalProducer

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SeparablePositive Burnett.Microlocal.AngularCommutator
open Burnett.Microlocal.SeparableSupBound (offzero_symbol_bound_of_sphere
  eventually_finiteSeparable_pairing_le_uniform_of_localized_weak_zero norm_limit_le_of_eventually_le_add)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate

/-- One subsequence for all finite lists and all ordered component pairs. The operator is in
the second slot, so the limit is linear in the symbol. -/
theorem exists_listPairing_common_subsequence {κ : Type} [Countable κ]
    (K : BallData) (u : ℕ → κ → ComplexL2 Space) (B : ℝ) (hB : ∀ n c, ‖u n c‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : SeparableParameters → κ → κ → ℂ,
      ∀ ps c d, Tendsto (fun n => inner ℂ (u (σ n) d) (listOperator K ps (u (σ n) c)))
        atTop (𝓝 (A ps c d)) := by
  obtain ⟨e, he, _⟩ := exists_dense_separable_enumeration K
  letI : Countable SeparableParameters := he.countable
  obtain ⟨σ, hσ, A, _, hA⟩ := exists_subsequence_bounded_ordered_pairings
    (listOperator K) (fun ps => ‖listOperator K ps‖) (fun _ => norm_nonneg _)
    (fun ps v => (listOperator K ps).le_opNorm v) u B hB
  refine ⟨σ, hσ, fun ps c d => conj (A ps c d), fun ps c d => ?_⟩
  have h := (Complex.continuous_conj.tendsto (A ps c d)).comp (hA ps c d)
  apply h.congr
  intro n
  exact inner_conj_symm (u (σ n) d) (listOperator K ps (u (σ n) c))

/-- A single list pairing has the genuine compact-cosphere uniform symbol bound. -/
theorem eventually_listPairing_le_of_localized_weak_zero
    (K : BallData) (ps : SeparableParameters)
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n x, f n x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n x, f n x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : Burnett.X02.SobolevTestJet.D,
      Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    let u (n : ℕ) := (sourceSchwartz (hs n) χ₀ (hχ₀ n)).toLp 2 volume
    ∀ᶠ n in atTop, ‖inner ℂ (u n) (listOperator K ps (u n))‖ ≤
      ‖separableRestriction K ps‖ * B ^ 2 + ε := by
  intro u
  let a (i : Fin ps.length) := baseSymbol K (ps.get i).1
  let m (i : Fin ps.length) := complexRationalAngularSymbol (ps.get i).2
  have hd (i : Fin ps.length) : DegreeZero (m i : Space → ℂ) :=
    complexRationalAngular_degreeZero (ps.get i).2
  have hM : ∀ x ∈ K.closedBall, ∀ ξ : UnitSphere,
      ‖∑ i, a i x * m i ξ‖ ≤ ‖separableRestriction K ps‖ := by
    intro x hx ξ
    let y : K.Point := ⟨x, hx⟩
    change ‖∑ i : Fin ps.length, baseSymbol K (ps.get i).1 x *
      complexRationalAngularSymbol (ps.get i).2 ξ‖ ≤ _
    rw [← separableValue_eq_finite K ps x ξ]
    have hy := (separableRestriction K ps).norm_coe_le_norm (y, ξ)
    simpa only [separableRestriction_apply] using hy
  have h :=
    eventually_finiteSeparable_pairing_le_uniform_of_localized_weak_zero a m
      (fun i => (complexBase_contDiff K (ps.get i).1).continuous)
      (fun i => complexRationalAngular_contDiffOn (ps.get i).2) hd
      K.closedBall (isCompact_closedBall _ _) ‖separableRestriction K ps‖ (norm_nonneg _)
      (offzero_symbol_bound_of_sphere a m hd K.closedBall _ hM) f hs hf χ₀ hχ₀ hKf B hB ht ε hε
  filter_upwards [h] with n hn
  rw [norm_inner_symm (𝕜 := ℂ), listOperator_eq_finiteSeparable]
  exact hn

/-- Algebraic test-list addition and scalar operations pass to the simultaneous
limits, even if distinct lists are different quantizations. -/
theorem listPairing_limit_algebra (K : BallData)
    (u v : ℕ → ComplexL2 Space) (L : SeparableParameters → ℂ)
    (hL : ∀ ps, Tendsto (fun n => inner ℂ (v n) (listOperator K ps (u n))) atTop (𝓝 (L ps))) :
    L [] = 0 ∧
    (∀ ps qs, L (ps ++ qs) = L ps + L qs) ∧
    (∀ (r : ℚ) ps, L (rationalScale r 0 ps) = r • L ps) ∧
    (∀ ps, L (rationalScale 0 1 ps) = Complex.I * L ps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (hL [])
    simpa only [listOperator_nil, ContinuousLinearMap.zero_apply, inner_zero_right] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  · intro ps qs
    apply tendsto_nhds_unique (hL (ps ++ qs))
    simpa only [listOperator_append, ContinuousLinearMap.add_apply, inner_add_right] using
      (hL ps).add (hL qs)
  · intro r ps
    apply tendsto_nhds_unique (hL (rationalScale r 0 ps))
    have he : r • L ps = (r : ℂ) * L ps :=
      (ratCast_smul_eq ℂ ℚ r (L ps)).symm
    rw [he]
    simpa only [listOperator_rat_smul, ContinuousLinearMap.smul_apply, inner_smul_right] using
      (hL ps).const_mul (r : ℂ)
  · intro ps
    apply tendsto_nhds_unique (hL (rationalScale 0 1 ps))
    simpa only [listOperator_I_smul, ContinuousLinearMap.smul_apply, inner_smul_right] using
      (hL ps).const_mul Complex.I

end Burnett.Microlocal.CompactFunctionalProducer

namespace Burnett.Microlocal.CompactFunctionalProducer

open Set Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.DenseComplexFunctional

private theorem listLimit_eq_of_restriction_eq (K : BallData) (L : SeparableParameters → ℂ)
    (hadd : ∀ ps qs, L (ps ++ qs) = L ps + L qs)
    (hscale : ∀ (r : ℚ) ps, L (rationalScale r 0 ps) = r • L ps)
    (B : ℝ) (hB : ∀ ps, ‖L ps‖ ≤ B ^ 2 * ‖separableRestriction K ps‖)
    (ps qs : SeparableParameters) (h : separableRestriction K ps = separableRestriction K qs) :
    L ps = L qs := by
  let rs := ps ++ rationalScale (-1) 0 qs
  have hzero : separableRestriction K rs = 0 := by
    change separableRestriction K (ps ++ rationalScale (-1) 0 qs) = 0
    rw [separableRestriction_append, separableRestriction_rat_smul, h, neg_one_smul, add_neg_cancel]
  have hL : L rs = L ps - L qs := by
    change L (ps ++ rationalScale (-1) 0 qs) = L ps - L qs
    rw [hadd, hscale, neg_one_smul, sub_eq_add_neg]
  have hb := hB rs
  rw [hL, hzero, norm_zero, mul_zero] at hb
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)

/-- The limits descend by the symbol bound to the actual restriction submodule. -/
theorem exists_ratFunctional_of_listLimits (K : BallData) (L : SeparableParameters → ℂ)
    (hadd : ∀ ps qs, L (ps ++ qs) = L ps + L qs)
    (hscale : ∀ (r : ℚ) ps, L (rationalScale r 0 ps) = r • L ps)
    (hI : ∀ ps, L (rationalScale 0 1 ps) = Complex.I * L ps)
    (B : ℝ) (hB : ∀ ps, ‖L ps‖ ≤ B ^ 2 * ‖separableRestriction K ps‖) :
    ∃ F : rationalRestrictionModule K →L[ℚ] ℂ,
      (∀ ps, F ⟨separableRestriction K ps, ⟨ps, rfl⟩⟩ = L ps) ∧
      (∀ x : rationalRestrictionModule K, ‖F x‖ ≤ B ^ 2 * ‖(x : TestSpace K)‖) ∧
      (∀ x : rationalRestrictionModule K,
        F ⟨Complex.I • (x : TestSpace K), rationalRestrictionModule_I_mem K x⟩ = Complex.I * F x) := by
  let S := rationalRestrictionModule K
  let rep (x : S) : SeparableParameters := x.property.choose
  have hrep (x : S) : separableRestriction K (rep x) = (x : TestSpace K) :=
    x.property.choose_spec
  have hsame := listLimit_eq_of_restriction_eq K L hadd hscale B hB
  let F₀ : S →ₗ[ℚ] ℂ := {
    toFun x := L (rep x)
    map_add' := fun x y => by
      change L (rep (x + y)) = L (rep x) + L (rep y)
      rw [← hadd]
      apply hsame
      rw [hrep (x+y), separableRestriction_append, hrep x, hrep y]
      rfl
    map_smul' := fun r x => by
      change L (rep (r • x)) = r • L (rep x)
      rw [← hscale]
      apply hsame
      rw [hrep (r • x), separableRestriction_rat_smul, hrep x]
      rfl
  }
  have hF₀ (x : S) : ‖F₀ x‖ ≤ B ^ 2 * ‖x‖ := by
    change ‖L (rep x)‖ ≤ B ^ 2 * ‖(x : TestSpace K)‖
    simpa only [hrep x] using hB (rep x)
  let F := F₀.mkContinuous (B ^ 2) hF₀
  refine ⟨F, ?_, fun x => hF₀ x, ?_⟩
  · intro ps
    let x : S := ⟨separableRestriction K ps, ⟨ps, rfl⟩⟩
    change L (rep x) = L ps
    exact hsame _ _ (hrep x)
  · intro x
    let y : S := ⟨Complex.I • (x : TestSpace K), rationalRestrictionModule_I_mem K x⟩
    change L (rep y) = Complex.I * L (rep x)
    rw [← hI]
    apply hsame
    rw [hrep y, separableRestriction_I_smul, hrep x]

/-- There is a unique bounded complex-linear functional extending the exact list limits. -/
theorem existsUnique_complexFunctional_of_listLimits (K : BallData) (L : SeparableParameters → ℂ)
    (hadd : ∀ ps qs, L (ps ++ qs) = L ps + L qs)
    (hscale : ∀ (r : ℚ) ps, L (rationalScale r 0 ps) = r • L ps)
    (hI : ∀ ps, L (rationalScale 0 1 ps) = Complex.I * L ps)
    (B : ℝ) (hB : ∀ ps, ‖L ps‖ ≤ B ^ 2 * ‖separableRestriction K ps‖) :
    ∃! F : TestSpace K →L[ℂ] ℂ,
      (∀ ps, F (separableRestriction K ps) = L ps) ∧
      ∀ x : TestSpace K, ‖F x‖ ≤ B ^ 2 * ‖x‖ := by
  obtain ⟨F, hF, hnorm, hFi⟩ := exists_ratFunctional_of_listLimits K L hadd hscale hI B hB
  obtain ⟨G, hG, huniq⟩ := existsUnique_complexFunctional_of_dense_rat_submodule
    (rationalRestrictionModule K) (rationalRestrictionModule_dense K) F
    (rationalRestrictionModule_I_mem K) hFi (B ^ 2) hnorm
  refine ⟨G, ⟨fun ps => (hG.1 ⟨separableRestriction K ps, ⟨ps, rfl⟩⟩).trans (hF ps), hG.2⟩, ?_⟩
  intro H hH
  apply huniq H
  refine ⟨fun x => ?_, hH.2⟩
  obtain ⟨ps, he⟩ := x.property
  let y : rationalRestrictionModule K := ⟨separableRestriction K ps, ⟨ps, rfl⟩⟩
  have hy : y = x := Subtype.ext he
  rw [← hy]
  exact (hH.1 ps).trans (hF ps).symm

end Burnett.Microlocal.CompactFunctionalProducer

namespace Burnett.Microlocal.CompactFunctionalProducer

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SeparableSupBound (norm_limit_le_of_eventually_le_add)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology

/-- On one subsequence all ordered list pairings converge. The diagonal limits extend to
genuine complex-linear functionals on the actual compact ball times its round cosphere. -/
theorem exists_commonCompactDiagonalFunctional {κ : Type} [Countable κ]
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
        ∀ c g, ‖G c g‖ ≤ B ^ 2 * ‖g‖ := by
  intro u
  have hu (n : ℕ) (c : κ) : ‖u n c‖ ≤ B := by
    have heq : ‖u n c‖ = ‖(hf n c).toLp (f n c)‖ := by
      simp only [u, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f n c x))
    exact heq.trans_le (hB n c)
  obtain ⟨σ, hσ, L, hL⟩ := exists_listPairing_common_subsequence K u B hu
  have hG (c : κ) : ∃ G : TestSpace K →L[ℂ] ℂ,
      (∀ ps, G (separableRestriction K ps) = L ps c c) ∧
      ∀ g : TestSpace K, ‖G g‖ ≤ B ^ 2 * ‖g‖ := by
    let A (ps : SeparableParameters) := L ps c c
    have ha (ps : SeparableParameters) : ‖A ps‖ ≤ B ^ 2 * ‖separableRestriction K ps‖ := by
      rw [mul_comm]
      apply norm_limit_le_of_eventually_le_add _ _ _ (hL ps c c)
      intro ε hε
      have h := eventually_listPairing_le_of_localized_weak_zero K ps (fun n => f n c)
        (fun n => hs n c) (fun n => hf n c) χ₀ (fun n => hχ₀ n c)
        (fun n => hKf n c) B (fun n => hB n c) (ht c) ε hε
      exact hσ.tendsto_atTop.eventually h
    obtain ⟨_, hadd, hr, hI⟩ :=
      listPairing_limit_algebra K (fun n => u (σ n) c) (fun n => u (σ n) c) A
        (fun ps => hL ps c c)
    obtain ⟨F, hF, _⟩ := existsUnique_complexFunctional_of_listLimits K A hadd hr hI B ha
    exact ⟨F, hF⟩
  exact ⟨σ, hσ, L, fun c => (hG c).choose, hL,
    fun c => (hG c).choose_spec.1, fun c => (hG c).choose_spec.2⟩

end Burnett.Microlocal.CompactFunctionalProducer
