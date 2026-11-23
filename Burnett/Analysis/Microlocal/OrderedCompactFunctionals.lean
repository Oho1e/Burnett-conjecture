import Burnett.Analysis.Microlocal.CompactSquarePositivity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CompactOrderedFunctional

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothSquarePartition (physicalCutoffSymbol)
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.CompactFunctionalProducer
open Burnett.Microlocal.SeparableSupBound (eventually_finiteSeparable_pairing_le_uniform
  offzero_symbol_bound_of_sphere norm_limit_le_of_eventually_le_add)
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate

private def Q (A : ComplexL2 Space →L[ℂ] ComplexL2 Space) (x : ComplexL2 Space) : ℂ :=
  inner ℂ x (A x)

/-- Polarization for the operator-second pairing of an arbitrary complex-linear operator. -/
theorem four_mul_orderedPairing_eq_quadratic (A : ComplexL2 Space →L[ℂ] ComplexL2 Space)
    (u v : ComplexL2 Space) :
    (4 : ℂ) * inner ℂ u (A v) =
      (Q A (u + (1 : ℂ) • v) - Q A (u + (-1 : ℂ) • v)) -
        Complex.I * (Q A (u + Complex.I • v) - Q A (u + (-Complex.I) • v)) := by
  simp only [Q, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_neg, map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem norm_orderedPairing_le_quadratic_sum
    (A : ComplexL2 Space →L[ℂ] ComplexL2 Space) (u v : ComplexL2 Space) :
    4 * ‖inner ℂ u (A v)‖ ≤
      (‖Q A (u + (1 : ℂ) • v)‖ + ‖Q A (u + (-1 : ℂ) • v)‖) +
        (‖Q A (u + Complex.I • v)‖ + ‖Q A (u + (-Complex.I) • v)‖) := by
  have h := congrArg norm (four_mul_orderedPairing_eq_quadratic A u v)
  simp only [norm_mul, Complex.norm_ofNat] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)

private theorem eventually_listDiagonal_le_of_commutations
    (K : BallData) (ps : SeparableParameters) (u : ℕ → ComplexL2 Space)
    (B : ℝ) (hB : ∀ n, ‖u n‖ ≤ B)
    (hu : ∀ n, ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ u n x = 0)
    (hcomm : ∀ (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
        (i : Fin ps.length),
      Tendsto (fun n => cutoffCommutator (complexRationalAngularSymbol (ps.get i).2)
        (physicalCutoffSymbol χ hχ hc) (u n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖Q (listOperator K ps) (u n)‖ ≤
      ‖separableRestriction K ps‖ * B ^ 2 + ε := by
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
  have h := eventually_finiteSeparable_pairing_le_uniform a m
    (fun i => (complexBase_contDiff K (ps.get i).1).continuous)
    K.closedBall (isCompact_closedBall _ _) ‖separableRestriction K ps‖ (norm_nonneg _)
    (offzero_symbol_bound_of_sphere a m hd K.closedBall _ hM)
    u B hB hu hcomm ε hε
  simpa only [Q, listOperator_eq_finiteSeparable] using h

/-- The same list and compact symbol norm control each ordered pairing, using four diagonal bounds. -/
theorem eventually_listOrderedPairing_le_of_commutations
    (K : BallData) (ps : SeparableParameters) (u v : ℕ → ComplexL2 Space)
    (B : ℝ) (hBu : ∀ n, ‖u n‖ ≤ B) (hBv : ∀ n, ‖v n‖ ≤ B)
    (hu : ∀ n, ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ u n x = 0)
    (hv : ∀ n, ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ v n x = 0)
    (hcu : ∀ (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
        (i : Fin ps.length),
      Tendsto (fun n => cutoffCommutator (complexRationalAngularSymbol (ps.get i).2)
        (physicalCutoffSymbol χ hχ hc) (u n)) atTop (𝓝 0))
    (hcv : ∀ (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
        (i : Fin ps.length),
      Tendsto (fun n => cutoffCommutator (complexRationalAngularSymbol (ps.get i).2)
        (physicalCutoffSymbol χ hχ hc) (v n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖inner ℂ (u n) (listOperator K ps (v n))‖ ≤
      ‖separableRestriction K ps‖ * (2 * B) ^ 2 + ε := by
  let A := listOperator K ps
  let D := ‖separableRestriction K ps‖ * (2 * B) ^ 2 + ε
  have hcomb (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ∀ᶠ n in atTop, ‖Q A (u n + z • v n)‖ ≤ D := by
    let w (n : ℕ) := u n + z • v n
    have hBw (n : ℕ) : ‖w n‖ ≤ 2 * B := by
      calc
        _ ≤ ‖u n‖ + ‖z • v n‖ := norm_add_le _ _
        _ ≤ B + B := by
          apply add_le_add (hBu n)
          rw [norm_smul]
          exact (mul_le_mul_of_nonneg_right hz (norm_nonneg (v n))).trans (by simpa only [one_mul] using hBv n)
        _ = _ := by ring
    have hsw (n : ℕ) : ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ w n x = 0 := by
      filter_upwards [hu n, hv n, Lp.coeFn_add (u n) (z • v n), Lp.coeFn_smul z (v n)]
        with x hx hy ha hs
      by_cases hk : x ∈ K.closedBall
      · exact Or.inl hk
      · right
        have hx0 := hx.resolve_left hk
        have hy0 := hy.resolve_left hk
        change (u n + z • v n : ComplexL2 Space) x = 0
        rw [ha, Pi.add_apply, hs, Pi.smul_apply, hx0, hy0, smul_zero, add_zero]
    have hcw (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
        (i : Fin ps.length) :
        Tendsto (fun n => cutoffCommutator (complexRationalAngularSymbol (ps.get i).2)
          (physicalCutoffSymbol χ hχ hc) (w n)) atTop (𝓝 0) := by
      have h := (hcu χ hχ hc i).add ((hcv χ hχ hc i).const_smul z)
      simpa only [w, map_add, map_smul, smul_zero, add_zero] using h
    exact eventually_listDiagonal_le_of_commutations K ps w (2 * B) hBw hsw hcw ε hε
  filter_upwards [hcomb 1 (by simp), hcomb (-1) (by simp), hcomb Complex.I (by simp),
    hcomb (-Complex.I) (by simp)] with n h₁ h₂ h₃ h₄
  have hp := norm_orderedPairing_le_quadratic_sum A (u n) (v n)
  change ‖inner ℂ (u n) (A (v n))‖ ≤ D
  linarith

end Burnett.Microlocal.CompactOrderedFunctional

namespace Burnett.Microlocal.CompactOrderedFunctional

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothSquarePartition (physicalCutoffSymbol)
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.CompactFunctionalProducer
open Burnett.Microlocal.SeparableSupBound (norm_limit_le_of_eventually_le_add)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology

/-- Every ordered pair limit on the given common subsequence extends to a continuous
complex-linear functional of the actual compact-cosphere symbol. -/
theorem exists_orderedFunctionals_of_commonListLimits {κ : Type}
    (K : BallData) (f : ℕ → κ → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n c x, f n c x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : κ) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (L : SeparableParameters → κ → κ → ℂ)
    (hL : ∀ ps c d, Tendsto (fun n =>
      let v := (sourceSchwartz (hs (σ n) c) χ₀ (hχ₀ (σ n) c)).toLp 2 volume
      let u := (sourceSchwartz (hs (σ n) d) χ₀ (hχ₀ (σ n) d)).toLp 2 volume
      inner ℂ u (listOperator K ps v)) atTop (𝓝 (L ps c d))) :
    ∃ G : κ → κ → (TestSpace K →L[ℂ] ℂ),
      (∀ ps c d, G c d (separableRestriction K ps) = L ps c d) ∧
      ∀ c d g, ‖G c d g‖ ≤ (2 * B) ^ 2 * ‖g‖ := by
  let w (n : ℕ) (c : κ) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
  have hnorm (n : ℕ) (c : κ) : ‖w n c‖ ≤ B := by
    have heq : ‖w n c‖ = ‖(hf n c).toLp (f n c)‖ := by
      simp only [w, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f n c x))
    exact heq.trans_le (hB n c)
  have hsupport (n : ℕ) (c : κ) : ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ w n c x = 0 := by
    filter_upwards [(sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).coeFn_toLp 2 volume] with x hx
    by_cases hk : x ∈ K.closedBall
    · exact Or.inl hk
    · right
      change w n c x = (f n c x : ℂ) at hx
      have hz : f n c x = 0 := by
        by_contra hn
        exact hk (hKf n c x hn)
      rw [hx, hz, Complex.ofReal_zero]
  have hcomm (c : κ) (p : RationalPolynomial × RationalPolynomial)
      (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
      Tendsto (fun n => cutoffCommutator (complexRationalAngularSymbol p)
        (physicalCutoffSymbol χ hχ hc) (w n c)) atTop (𝓝 0) :=
    cutoffCommutator_tendsto_zero_of_localized_weak_zero
      (complexRationalAngularSymbol p) (physicalCutoffSymbol χ hχ hc)
      (complexRationalAngular_contDiffOn p) (complexRationalAngular_degreeZero p)
      (Complex.ofRealCLM.contDiff.comp hχ) (hc.comp_left Complex.ofReal_zero)
      (fun n => f n c) (fun n => hs n c) (fun n => hf n c) χ₀ (fun n => hχ₀ n c)
      B (fun n => hB n c) (ht c)
  have hExists (c d : κ) : ∃ G : TestSpace K →L[ℂ] ℂ,
      (∀ ps, G (separableRestriction K ps) = L ps c d) ∧
      ∀ g : TestSpace K, ‖G g‖ ≤ (2 * B) ^ 2 * ‖g‖ := by
    let A (ps : SeparableParameters) := L ps c d
    have hnormA (ps : SeparableParameters) : ‖A ps‖ ≤ (2 * B) ^ 2 * ‖separableRestriction K ps‖ := by
      rw [mul_comm]
      apply norm_limit_le_of_eventually_le_add _ _ _ (hL ps c d)
      intro ε hε
      have he := eventually_listOrderedPairing_le_of_commutations K ps
        (fun n => w n d) (fun n => w n c) B
        (fun n => hnorm n d) (fun n => hnorm n c)
        (fun n => hsupport n d) (fun n => hsupport n c)
        (fun χ hχ hc i => hcomm d (ps.get i).2 χ hχ hc)
        (fun χ hχ hc i => hcomm c (ps.get i).2 χ hχ hc) ε hε
      exact hσ.tendsto_atTop.eventually he
    obtain ⟨_, hadd, hscale, hI⟩ := listPairing_limit_algebra K
      (fun n => w (σ n) c) (fun n => w (σ n) d) A (fun ps => hL ps c d)
    obtain ⟨G, hG, _⟩ := existsUnique_complexFunctional_of_listLimits K A hadd hscale hI (2 * B) hnormA
    exact ⟨G, hG⟩
  exact ⟨fun c d => (hExists c d).choose, fun ps c d => (hExists c d).choose_spec.1 ps,
    fun c d => (hExists c d).choose_spec.2⟩

/-- Agreement on the actual restriction lists determines the functional. -/
theorem orderedFunctional_eq_of_sameListValues (K : BallData) (G H : TestSpace K →L[ℂ] ℂ)
    (h : ∀ ps, G (separableRestriction K ps) = H (separableRestriction K ps)) :
    G = H := by
  apply ContinuousLinearMap.coeFn_injective
  apply (separableRestriction_dense K).equalizer G.continuous H.continuous
  funext ps
  exact h ps

end Burnett.Microlocal.CompactOrderedFunctional

namespace Burnett.Microlocal.CompactOrderedFunctional

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.CompactSquarePositivity
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate

private theorem finiteCombination_inner {ι : Type} [Fintype ι]
    (T : ComplexL2 Space →L[ℂ] ComplexL2 Space) (v : ι → ℂ) (u : ι → ComplexL2 Space) :
    inner ℂ (∑ i, v i • u i) (T (∑ j, v j • u j)) =
      ∑ i, ∑ j, conj (v i) * v j * inner ℂ (u i) (T (u j)) := by
  rw [sum_inner]
  simp only [map_sum, map_smul, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The dense-list square test of every constant-vector compression is real nonnegative
for the same ordered limits and original component sequences. -/
theorem listSquare_compression_positive_of_orderedLimits {ι : Type} [Fintype ι]
    (K : BallData) (u : ℕ → ι → ComplexL2 Space) (B : ℝ) (hB : ∀ n i, ‖u n i‖ ≤ B)
    (F : ι → ι → (TestSpace K →L[ℂ] ℂ))
    (hF : ∀ qs i j, Tendsto (fun n => inner ℂ (u n i) (listOperator K qs (u n j)))
      atTop (𝓝 (F i j (separableRestriction K qs))))
    (ps : SeparableParameters)
    (hcomm : ∀ (i j : Fin ps.length) c, Tendsto
      (fun n => cutoffCommutator (complexRationalAngularSymbol (ps.get j).2)
        (productSymbol (conjugateSymbol (baseSymbol K (ps.get i).1))
          (baseSymbol K (ps.get j).1)) (u n c)) atTop (𝓝 0))
    (v : ι → ℂ) :
    let q := separableRestriction K ps
    let z := ∑ i, ∑ j, conj (v i) * v j * F i j (star q * q)
    0 ≤ z.re ∧ z.im = 0 := by
  intro q z
  let qs := conjugateProductParameters ps ps
  let a (i : Fin ps.length) := baseSymbol K (ps.get i).1
  let m (i : Fin ps.length) := complexRationalAngularSymbol (ps.get i).2
  let w (n : ℕ) : ComplexL2 Space := ∑ i, v i • u n i
  let C : ℝ := (∑ i, ‖v i‖) * B
  have hC (n : ℕ) : ‖w n‖ ≤ C := by
    calc
      _ ≤ ∑ i, ‖v i • u n i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖v i‖ * B := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB n i) (norm_nonneg _)
      _ = _ := (Finset.sum_mul ..).symm
  have hwcomm (i j : Fin ps.length) :
      Tendsto (fun n => cutoffCommutator (m j) (productSymbol (conjugateSymbol (a i)) (a j)) (w n))
        atTop (𝓝 0) := by
    have heach (l : ι) := (hcomm i j l).const_smul (v l)
    simpa only [w, map_sum, map_smul, smul_zero, Finset.sum_const_zero] using
      (tendsto_finset_sum Finset.univ (fun l _ => heach l))
  have hsum : Tendsto (fun n => ∑ i, ∑ j, conj (v i) * v j *
      inner ℂ (u n i) (listOperator K qs (u n j))) atTop (𝓝 z) := by
    have h := tendsto_finset_sum Finset.univ (fun i _ =>
      tendsto_finset_sum Finset.univ (fun j _ => (hF qs i j).const_mul (conj (v i) * v j)))
    simpa only [qs, separableRestriction_absoluteSquare, z] using h
  have hlim : Tendsto (fun n => inner ℂ (w n) (listOperator K qs (w n))) atTop (𝓝 z) :=
    hsum.congr (fun n => (finiteCombination_inner (listOperator K qs) v (u n)).symm)
  have hconj := (Complex.continuous_conj.tendsto z).comp hlim
  have hsq (n : ℕ) : listOperator K qs (w n) = finiteSquareOperator a m (w n) :=
    DFunLike.congr_fun (listOperator_absoluteSquare K ps) (w n)
  have hlim' : Tendsto (fun n => inner ℂ (finiteSquareOperator a m (w n)) (w n)) atTop (𝓝 (conj z)) := by
    apply hconj.congr
    intro n
    change conj (inner ℂ (w n) (listOperator K qs (w n))) = _
    rw [hsq n]
    exact inner_conj_symm _ _
  obtain ⟨hr, hi⟩ := finiteSquare_pair_limit_nonnegative_of_commutator a m w C hC hwcomm (conj z) hlim'
  refine ⟨?_, ?_⟩
  · simpa only [Complex.conj_re] using hr
  · exact neg_eq_zero.mp (by simpa only [Complex.conj_im] using hi)

end Burnett.Microlocal.CompactOrderedFunctional

namespace Burnett.Microlocal.CompactOrderedFunctional

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.CompactSquarePositivity
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexConjugate

/-- One actual ordered functional matrix on the fixed compact product, positive on every
constant-vector compression of every square from the dense finite lists. -/
theorem exists_commonCompactMatrixFunctional_positive {ι : Type} [Fintype ι]
    (K : BallData) (f : ℕ → ι → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n c x, f n c x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : ι) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    let u (n : ℕ) (c : ι) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ F : ι → ι → (TestSpace K →L[ℂ] ℂ),
      (∀ ps i j, Tendsto (fun n => inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j)))
        atTop (𝓝 (F i j (separableRestriction K ps)))) ∧
      (∀ i g, ‖F i i g‖ ≤ B ^ 2 * ‖g‖) ∧
      (∀ i j g, ‖F i j g‖ ≤ (2 * B) ^ 2 * ‖g‖) ∧
      ∀ (v : ι → ℂ) ps,
        let q := separableRestriction K ps
        let z := ∑ i, ∑ j, conj (v i) * v j * F i j (star q * q)
        0 ≤ z.re ∧ z.im = 0 := by
  intro u
  obtain ⟨σ, hσ, L, Gdiag, hL, hDiagList, hDiagBound, _⟩ :=
    exists_commonCompactDiagonalFunctional_listSquare_positive K f hs hf χ₀ hχ₀ hKf B hB ht
  obtain ⟨G, hG, hNormG⟩ := exists_orderedFunctionals_of_commonListLimits K f hs hf χ₀ hχ₀ hKf
    B hB ht σ hσ L hL
  let F (i j : ι) := G j i
  have hF (ps : SeparableParameters) (i j : ι) :
      Tendsto (fun n => inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j)))
        atTop (𝓝 (F i j (separableRestriction K ps))) := by
    change Tendsto _ _ (𝓝 (G j i (separableRestriction K ps)))
    rw [hG]
    exact hL ps j i
  have hdiag (i : ι) : F i i = Gdiag i :=
    orderedFunctional_eq_of_sameListValues K _ _ fun ps =>
      (hG ps i i).trans (hDiagList i ps).symm
  refine ⟨σ, hσ, F, hF, fun i g => ?_, fun i j g => hNormG j i g, fun v ps => ?_⟩
  · rw [hdiag]
    exact hDiagBound i g
  · have hB' (n : ℕ) (c : ι) : ‖u (σ n) c‖ ≤ B := by
      have heq : ‖u (σ n) c‖ = ‖(hf (σ n) c).toLp (f (σ n) c)‖ := by
        simp only [u, SchwartzMap.toLp, Lp.norm_toLp]
        congr 1
        exact eLpNorm_congr_norm_ae
          (Eventually.of_forall fun x => Complex.norm_real (f (σ n) c x))
      exact heq.trans_le (hB (σ n) c)
    apply listSquare_compression_positive_of_orderedLimits K (fun n c => u (σ n) c)
      B hB' F hF ps _ v
    intro i j c
    let a (k : Fin ps.length) := baseSymbol K (ps.get k).1
    let m := complexRationalAngularSymbol (ps.get j).2
    let b := productSymbol (conjugateSymbol (a i)) (a j)
    have hsb : ContDiff ℝ ∞ (b : Space → ℂ) :=
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (complexBase_contDiff K (ps.get i).1)).mul
        (complexBase_contDiff K (ps.get j).1)
    have hcb : HasCompactSupport (b : Space → ℂ) :=
      ((complexBase_hasCompactSupport K (ps.get i).1).comp_left
        (by simp : (starRingEnd ℂ) 0 = 0)).mul_right
    exact cutoffCommutator_tendsto_zero_of_localized_weak_zero m b
      (complexRationalAngular_contDiffOn (ps.get j).2) (complexRationalAngular_degreeZero (ps.get j).2)
      hsb hcb (fun n => f (σ n) c) (fun n => hs (σ n) c) (fun n => hf (σ n) c)
      χ₀ (fun n => hχ₀ (σ n) c) B (fun n => hB (σ n) c)
      (fun φ => (ht c φ).comp hσ.tendsto_atTop)

end Burnett.Microlocal.CompactOrderedFunctional
