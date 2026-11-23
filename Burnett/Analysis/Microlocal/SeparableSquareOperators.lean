import Burnett.Analysis.PrincipalEnergy.Fourier.SymbolProduct
import Burnett.Analysis.Compactness.OrderedPairings
import Burnett.Analysis.Microlocal.AngularCommutator.Infrared
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Burnett.Fourier
open scoped InnerProduct ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def conjugateSymbol (a : BoundedSymbol V) : BoundedSymbol V where
  toFun x := conj (a x)
  measurable := Complex.continuous_conj.comp_aestronglyMeasurable a.measurable
  bound := a.bound
  bound_nonneg := a.bound_nonneg
  norm_le x := by simpa only [Complex.norm_conj] using a.norm_le x

@[simp] theorem conjugateSymbol_apply (a : BoundedSymbol V) (x : V) :
    conjugateSymbol a x = conj (a x) := rfl

@[simp] theorem conjugateSymbol_conjugateSymbol (a : BoundedSymbol V) :
    conjugateSymbol (conjugateSymbol a) = a := by
  cases a with
  | mk f hm B hb hn =>
    unfold conjugateSymbol
    congr 1
    funext x
    exact Complex.conj_conj (f x)

@[simp] theorem conjugateSymbol_productSymbol (a b : BoundedSymbol V) :
    conjugateSymbol (productSymbol a b) =
      productSymbol (conjugateSymbol a) (conjugateSymbol b) := by
  cases a
  cases b
  unfold conjugateSymbol productSymbol
  congr 1
  funext x
  exact map_mul _ _ _

theorem symbolCLM_product (a b : BoundedSymbol V) (u : ComplexL2 V) :
    symbolCLM (productSymbol a b) u = symbolCLM a (symbolCLM b u) := by
  change symbolL2 (productSymbol a b) u = symbolL2 a (symbolL2 b u)
  apply Lp.ext
  filter_upwards [symbolL2_ae (productSymbol a b) u, symbolL2_ae a (symbolL2 b u),
    symbolL2_ae b u] with x hx hax hbx
  rw [hx, hax, hbx, productSymbol_apply, mul_assoc]

theorem fourierMultiplier_product (a b : BoundedSymbol V) (u : ComplexL2 V) :
    fourierMultiplier (productSymbol a b) u = fourierMultiplier a (fourierMultiplier b u) := by
  apply (fourierL2Equiv (V := V)).injective
  simp only [fourier_fourierMultiplier]
  exact symbolCLM_product a b (fourierL2Equiv u)

theorem inner_symbolCLM_left (a : BoundedSymbol V) (u v : ComplexL2 V) :
    inner ℂ (symbolCLM a u) v = inner ℂ u (symbolCLM (conjugateSymbol a) v) := by
  change inner ℂ (symbolL2 a u) v = inner ℂ u (symbolL2 (conjugateSymbol a) v)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae a u, symbolL2_ae (conjugateSymbol a) v] with x hx hy
  rw [hx, hy, conjugateSymbol_apply, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  ring

theorem inner_fourierMultiplier_left (a : BoundedSymbol V) (u v : ComplexL2 V) :
    inner ℂ (fourierMultiplier a u) v = inner ℂ u (fourierMultiplier (conjugateSymbol a) v) := by
  let F := fourierL2Equiv (V := V)
  calc
    _ = inner ℂ (F (fourierMultiplier a u)) (F v) := (F.inner_map_map _ _).symm
    _ = inner ℂ (F u) (F (fourierMultiplier (conjugateSymbol a) v)) := by
      simp only [F, fourier_fourierMultiplier]
      exact inner_symbolCLM_left a (F u) (F v)
    _ = _ := F.inner_map_map _ _

theorem symbolCLM_adjoint (a : BoundedSymbol V) :
    (symbolCLM a)† = symbolCLM (conjugateSymbol a) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro u v
  rw [inner_symbolCLM_left, conjugateSymbol_conjugateSymbol]

theorem fourierMultiplier_adjoint (a : BoundedSymbol V) :
    (fourierMultiplier a)† = fourierMultiplier (conjugateSymbol a) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro u v
  rw [inner_fourierMultiplier_left, conjugateSymbol_conjugateSymbol]

end Burnett.Microlocal.SeparablePositive

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Filter Burnett.Fourier Burnett.Microlocal.AngularCommutator
open scoped InnerProduct Topology ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The ordered factor in the expansion of a squared separable symbol. -/
def squareSymbolTerm (a b m n : BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  separableOperator (productSymbol a (conjugateSymbol b)) (productSymbol (conjugateSymbol n) m)

/-- The commutator error in the pair of elementary quantizations acts on the
original input. Lean's inner product is conjugate-linear in the first slot. -/
theorem separableOperator_pair_difference (a b m n : BoundedSymbol V) (u : ComplexL2 V) :
    inner ℂ (separableOperator a m u) (separableOperator b n u) -
      inner ℂ (squareSymbolTerm a b m n u) u =
      -inner ℂ (fourierMultiplier m u) (cutoffCommutator n (productSymbol (conjugateSymbol a) b) u) := by
  let c := productSymbol (conjugateSymbol a) b
  have hleft : inner ℂ (separableOperator a m u) (separableOperator b n u) =
      inner ℂ (fourierMultiplier m u) (symbolCLM c (fourierMultiplier n u)) := by
    change inner ℂ (symbolCLM a (fourierMultiplier m u)) (symbolCLM b (fourierMultiplier n u)) = _
    rw [inner_symbolCLM_left, ← symbolCLM_product]
  have hright : inner ℂ (squareSymbolTerm a b m n u) u =
      inner ℂ (fourierMultiplier m u) (fourierMultiplier n (symbolCLM c u)) := by
    change inner ℂ (symbolCLM (productSymbol a (conjugateSymbol b))
      (fourierMultiplier (productSymbol (conjugateSymbol n) m) u)) u = _
    rw [fourierMultiplier_product, inner_symbolCLM_left, conjugateSymbol_productSymbol,
      conjugateSymbol_conjugateSymbol, inner_fourierMultiplier_left, conjugateSymbol_conjugateSymbol]
  rw [hleft, hright]
  change _ = -inner ℂ (fourierMultiplier m u)
    (fourierMultiplier n (symbolCLM c u) - symbolCLM c (fourierMultiplier n u))
  rw [inner_sub_right]
  ring

theorem separableOperator_pair_difference_tendsto_zero
    (a b m n : BoundedSymbol V) (u : ℕ → ComplexL2 V) (B : ℝ) (hB : ∀ k, ‖u k‖ ≤ B)
    (hcomm : Tendsto (fun k => cutoffCommutator n (productSymbol (conjugateSymbol a) b) (u k))
      atTop (𝓝 0)) :
    Tendsto (fun k => inner ℂ (separableOperator a m (u k)) (separableOperator b n (u k)) -
      inner ℂ (squareSymbolTerm a b m n (u k)) (u k)) atTop (𝓝 0) := by
  simp_rw [separableOperator_pair_difference]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun k => m.bound * B *
      ‖cutoffCommutator n (productSymbol (conjugateSymbol a) b) (u k)‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hcomm.norm.const_mul (m.bound * B)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro k
  rw [norm_neg]
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (fourierMultiplier_norm_le m (u k)).trans <| mul_le_mul_of_nonneg_left (hB k) m.bound_nonneg

end Burnett.Microlocal.SeparablePositive

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Filter Burnett.Fourier Burnett.Microlocal.AngularCommutator
open scoped InnerProduct Topology ComplexConjugate BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

def finiteSeparableOperator (a m : ι → BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  ∑ i, separableOperator (a i) (m i)

/-- The quantization of the pointwise squared modulus of a finite
separable symbol, expanded over its ordered pairs. -/
def finiteSquareOperator (a m : ι → BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  ∑ i, ∑ j, squareSymbolTerm (a i) (a j) (m i) (m j)

theorem finiteSeparable_adjoint_pair (a m : ι → BoundedSymbol V) (u : ComplexL2 V) :
    inner ℂ ((((finiteSeparableOperator a m)†).comp (finiteSeparableOperator a m)) u) u =
      inner ℂ (finiteSeparableOperator a m u) (finiteSeparableOperator a m u) :=
  (finiteSeparableOperator a m).adjoint_inner_left u (finiteSeparableOperator a m u)

theorem finiteSquare_symbol_eq_sq_norm (a m : ι → BoundedSymbol V) (x ξ : V) :
    (∑ i, ∑ j, productSymbol (a i) (conjugateSymbol (a j)) x *
       productSymbol (conjugateSymbol (m j)) (m i) ξ) =
      (‖∑ i, a i x * m i ξ‖ : ℂ) ^ 2 := by
  let A (i : ι) := a i x * m i ξ
  calc
    _ = ∑ i, ∑ j, A i * conj (A j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [A, productSymbol_apply, conjugateSymbol_apply, map_mul]
      ring
    _ = (∑ i, A i) * conj (∑ j, A j) := by
      rw [map_sum, Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = _ := Complex.mul_conj' _

theorem finiteSquare_difference_tendsto_zero
    (a m : ι → BoundedSymbol V) (u : ℕ → ComplexL2 V) (B : ℝ) (hB : ∀ k, ‖u k‖ ≤ B)
    (hcomm : ∀ i j, Tendsto
      (fun k => cutoffCommutator (m j) (productSymbol (conjugateSymbol (a i)) (a j)) (u k)) atTop (𝓝 0)) :
    Tendsto (fun k => inner ℂ (finiteSeparableOperator a m (u k)) (finiteSeparableOperator a m (u k)) -
      inner ℂ (finiteSquareOperator a m (u k)) (u k)) atTop (𝓝 0) := by
  let q (i j : ι) (k : ℕ) :=
    inner ℂ (separableOperator (a i) (m i) (u k)) (separableOperator (a j) (m j) (u k)) -
      inner ℂ (squareSymbolTerm (a i) (a j) (m i) (m j) (u k)) (u k)
  have hq (i j : ι) : Tendsto (q i j) atTop (𝓝 0) :=
    separableOperator_pair_difference_tendsto_zero (a i) (a j) (m i) (m j) u B hB (hcomm i j)
  have hs (i : ι) : Tendsto (fun k => ∑ j, q i j k) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hq i j)
  have hsum : Tendsto (fun k => ∑ i, ∑ j, q i j k) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hs i)
  apply hsum.congr
  intro k
  simp only [q, finiteSeparableOperator, finiteSquareOperator, ContinuousLinearMap.sum_apply,
    sum_inner, inner_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-- A complex limit of the actual quadratic functional on a finite square
must be real and nonnegative. The paper pairing is linear in the input
and conjugate-linear in the tested image. -/
theorem finiteSquare_pair_limit_nonnegative_of_commutator
    (a m : ι → BoundedSymbol V) (u : ℕ → ComplexL2 V) (B : ℝ) (hB : ∀ k, ‖u k‖ ≤ B)
    (hcomm : ∀ i j, Tendsto
      (fun k => cutoffCommutator (m j) (productSymbol (conjugateSymbol (a i)) (a j)) (u k)) atTop (𝓝 0))
    (z : ℂ)
    (hz : Tendsto (fun k => inner ℂ (finiteSquareOperator a m (u k)) (u k)) atTop (𝓝 z)) :
    0 ≤ z.re ∧ z.im = 0 := by
  have herr := finiteSquare_difference_tendsto_zero a m u B hB hcomm
  have hself : Tendsto
      (fun k => inner ℂ (finiteSeparableOperator a m (u k)) (finiteSeparableOperator a m (u k))) atTop
      (𝓝 z) := by
    simpa only [zero_add, sub_add_cancel] using herr.add hz
  have hre := (Complex.continuous_re.tendsto z).comp hself
  have him := (Complex.continuous_im.tendsto z).comp hself
  have hpos : ∀ᶠ k in atTop,
      0 ≤ (inner ℂ (finiteSeparableOperator a m (u k)) (finiteSeparableOperator a m (u k))).re :=
    Filter.Eventually.of_forall fun _ => inner_self_nonneg (𝕜 := ℂ)
  refine ⟨ge_of_tendsto (x := (atTop : Filter ℕ)) hre hpos, ?_⟩
  have hz0 : Tendsto
      (fun k => (inner ℂ (finiteSeparableOperator a m (u k)) (finiteSeparableOperator a m (u k))).im)
      atTop (𝓝 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr
    intro k
    exact (inner_self_im (𝕜 := ℂ) (finiteSeparableOperator a m (u k))).symm
  exact tendsto_nhds_unique (l := (atTop : Filter ℕ)) him hz0

open Burnett.X02.SobolevTestJet Burnett.Analysis.LocalHminusFourier
open scoped ContDiff

/-- The actual localized weak-zero inputs have the required pairwise
commutator limits simultaneously for a fixed finite square. -/
theorem finiteSquare_pair_limit_nonnegative_of_localized_weak_zero
    (a m : ι → BoundedSymbol Space)
    (hsa : ∀ i, ContDiff ℝ ∞ (a i : Space → ℂ))
    (hca : ∀ i, HasCompactSupport (a i : Space → ℂ))
    (hsm : ∀ i, ContDiffOn ℝ ∞ (m i : Space → ℂ) ({0}ᶜ : Set Space))
    (hh : ∀ i, DegreeZero (m i : Space → ℂ))
    (f : ℕ → Space → ℝ) (hs : ∀ k, ContDiff ℝ ∞ (f k))
    (hf : ∀ k, MemLp (f k) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ k x, f k x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ k, ‖(hf k).toLp (f k)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun k => ∫ x, f k x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (z : ℂ)
    (hz : Tendsto (fun k =>
      let u := (sourceSchwartz (hs k) χ0 (hχ0 k)).toLp 2 volume
      inner ℂ (finiteSquareOperator a m u) u) atTop (𝓝 z)) :
    0 ≤ z.re ∧ z.im = 0 := by
  let u (k : ℕ) := (sourceSchwartz (hs k) χ0 (hχ0 k)).toLp 2 volume
  have hu (k : ℕ) : ‖u k‖ ≤ B := by
    have heq : ‖u k‖ = ‖(hf k).toLp (f k)‖ := by
      simp only [u, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => Complex.norm_real (f k x))
    exact heq.trans_le (hB k)
  apply finiteSquare_pair_limit_nonnegative_of_commutator a m u B hu _ z hz
  intro i j
  let b := productSymbol (conjugateSymbol (a i)) (a j)
  have hsb : ContDiff ℝ ∞ (b : Space → ℂ) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (hsa i)).mul (hsa j)
  have hcb : HasCompactSupport (b : Space → ℂ) :=
    ((hca i).comp_left (by simp : (starRingEnd ℂ) 0 = 0)).mul_right
  exact cutoffCommutator_tendsto_zero_of_localized_weak_zero (m j) b (hsm j) (hh j) hsb hcb
    f hs hf χ0 hχ0 B hB ht

end Burnett.Microlocal.SeparablePositive

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Filter Burnett.Fourier
open scoped BigOperators InnerProduct Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem finiteSeparableOperator_norm_le {ι : Type*} [Fintype ι]
    (a m : ι → BoundedSymbol V) (u : ComplexL2 V) :
    ‖finiteSeparableOperator a m u‖ ≤ (∑ i, (a i).bound * (m i).bound) * ‖u‖ := by
  simp only [finiteSeparableOperator, ContinuousLinearMap.sum_apply, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => separableOperator_norm_le (a i) (m i) u))

theorem squareSymbolTerm_norm_le (a b m n : BoundedSymbol V) (u : ComplexL2 V) :
    ‖squareSymbolTerm a b m n u‖ ≤ ((a.bound * b.bound) * (n.bound * m.bound)) * ‖u‖ :=
  separableOperator_norm_le (productSymbol a (conjugateSymbol b)) (productSymbol (conjugateSymbol n) m) u
end Burnett.Microlocal.SeparablePositive
