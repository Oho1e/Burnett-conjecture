import Burnett.Analysis.Microlocal.LocalizedSeparablePairings
import Burnett.Analysis.Microlocal.SpatialSquarePartition
import Burnett.Analysis.Microlocal.RationalAngularDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SeparableSupBound

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open scoped InnerProduct BigOperators Topology ComplexConjugate

abbrev Space := Burnett.X02.SobolevTestJet.Space

private theorem ae_coe_finset_sum {ι : Type} (s : Finset ι) (f : ι → ComplexL2 Space) :
    ((∑ i ∈ s, f i : ComplexL2 Space) : Space → ℂ) =ᵐ[volume]
      (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero (E := ℂ)
      (p := 2) (μ := (volume : Measure Space)))
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x h1 h2
      rw [h1]
      change f i x + (∑ j ∈ s, f j : ComplexL2 Space) x = _
      rw [h2]

/-- Weighted sum of the actual Fourier multipliers after freezing the spatial coefficients. -/
def frozenAction {J : Type} [Fintype J] (m : J → BoundedSymbol Space)
    (d : J → ℂ) (v : ComplexL2 Space) : ComplexL2 Space :=
  ∑ j, d j • fourierMultiplier (m j) v

theorem frozenAction_norm_le {J : Type} [Fintype J] (m : J → BoundedSymbol Space)
    (d : J → ℂ) (v : ComplexL2 Space) (M : ℝ)
    (hM : ∀ ξ : Space, ξ ≠ 0 → ‖∑ j, d j * m j ξ‖ ≤ M) :
    ‖frozenAction m d v‖ ≤ M * ‖v‖ := by
  let F := fourierL2Equiv (V := Space)
  let P (j : J) := d j • symbolL2 (m j) (F v)
  have hF : F (frozenAction m d v) = ∑ j, P j := by
    simp only [P, F, frozenAction, map_sum, map_smul, fourier_fourierMultiplier]
  have hP : ∀ᵐ ξ ∂volume, ∀ j, P j ξ = d j * (m j ξ * F v ξ) := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (d j) (symbolL2 (m j) (F v)),
      symbolL2_ae (m j) (F v)] with ξ hs hm
    change ((d j • symbolL2 (m j) (F v)) : ComplexL2 Space) ξ = _
    rw [hs, Pi.smul_apply, hm, smul_eq_mul]
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, setOf_eq_eq_singleton, measure_singleton]
  rw [← F.norm_map (frozenAction m d v), hF, ← F.norm_map v]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ae_coe_finset_sum Finset.univ P, hP, hne] with ξ hs hp hn
  rw [hs]
  simp only [hp, ← mul_assoc, ← Finset.sum_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hM ξ hn) (norm_nonneg _)

private theorem norm_adjoint_coefficient_difference (a χ : BoundedSymbol Space)
    (c : ℂ) (δ : ℝ)
    (hsmall : ∀ x, χ x ≠ 0 → ‖a x - c‖ ≤ δ) (u : ComplexL2 Space) :
    let v := symbolCLM χ u
    ‖symbolCLM (conjugateSymbol a) v - conj c • v‖ ≤ δ * ‖v‖ := by
  dsimp only
  let v := symbolCLM χ u
  change ‖symbolL2 (conjugateSymbol a) v - conj c • v‖ ≤ δ * ‖v‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (symbolL2 (conjugateSymbol a) v) (conj c • v),
    symbolL2_ae (conjugateSymbol a) v, Lp.coeFn_smul (conj c) v, symbolL2_ae χ u]
    with x hsub ha hc hv
  change ‖(symbolL2 (conjugateSymbol a) v - conj c • v : ComplexL2 Space) x‖ ≤ δ * ‖v x‖
  rw [hsub, Pi.sub_apply, ha, hc, Pi.smul_apply, smul_eq_mul, conjugateSymbol_apply, ← sub_mul,
    norm_mul, ← map_sub, Complex.norm_conj]
  by_cases hx : χ x = 0
  · change v x = χ x * u x at hv
    simp [hv, hx]
  · exact mul_le_mul_of_nonneg_right (hsmall x hx) (norm_nonneg _)

private theorem pairing_single_coefficient_error
    (a m χ : BoundedSymbol Space) (c : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : ∀ x, χ x ≠ 0 → ‖a x - c‖ ≤ δ) (u : ComplexL2 Space) :
    let v := symbolCLM χ u
    ‖inner ℂ v (separableOperator a m v) -
        inner ℂ v (c • fourierMultiplier m v)‖ ≤ (δ * m.bound) * ‖v‖ ^ 2 := by
  dsimp only
  let v := symbolCLM χ u
  let w := fourierMultiplier m v
  have heq : inner ℂ v (separableOperator a m v) - inner ℂ v (c • w) =
      inner ℂ (symbolCLM (conjugateSymbol a) v - conj c • v) w := by
    have hleft := inner_symbolCLM_left (conjugateSymbol a) v w
    rw [conjugateSymbol_conjugateSymbol] at hleft
    change inner ℂ v (symbolCLM a w) - inner ℂ v (c • w) = _
    rw [inner_sub_left, inner_smul_left, Complex.conj_conj, inner_smul_right, hleft]
  change ‖inner ℂ v (separableOperator a m v) - inner ℂ v (c • w)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖symbolCLM (conjugateSymbol a) v - conj c • v‖ * ‖w‖ :=
      norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ (δ * ‖v‖) * (m.bound * ‖v‖) :=
      mul_le_mul (norm_adjoint_coefficient_difference a χ c δ hsmall u)
        (fourierMultiplier_norm_le m v) (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))
    _ = _ := by ring

/-- A localized pairing is controlled by the uniform frozen symbol bound and coefficient oscillation. -/
theorem finiteSeparable_pairing_frozen_piece_bound {J : Type} [Fintype J]
    (a m : J → BoundedSymbol Space) (χ : BoundedSymbol Space) (c : Space)
    (u : ComplexL2 Space) (M δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ ξ : Space, ξ ≠ 0 → ‖∑ j, a j c * m j ξ‖ ≤ M)
    (hsmall : ∀ j x, χ x ≠ 0 → ‖a j x - a j c‖ ≤ δ) :
    let v := symbolCLM χ u
    ‖inner ℂ v (finiteSeparableOperator a m v)‖ ≤
      (M + δ * ∑ j, (m j).bound) * ‖v‖ ^ 2 := by
  dsimp only
  let v := symbolCLM χ u
  let Q := inner ℂ v (finiteSeparableOperator a m v)
  let P := inner ℂ v (frozenAction m (fun j => a j c) v)
  let e (j : J) : ℂ :=
    inner ℂ v (separableOperator (a j) (m j) v) -
      inner ℂ v (a j c • fourierMultiplier (m j) v)
  have hdiff : Q - P = ∑ j, e j := by
    simp only [Q, P, e, finiteSeparableOperator, frozenAction, ContinuousLinearMap.sum_apply,
      inner_sum, Finset.sum_sub_distrib]
  have herr : ‖Q - P‖ ≤ (δ * ∑ j, (m j).bound) * ‖v‖ ^ 2 := by
    rw [hdiff]
    calc
      _ ≤ ∑ j, ‖e j‖ := norm_sum_le _ _
      _ ≤ ∑ j, (δ * (m j).bound) * ‖v‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => pairing_single_coefficient_error (a j) (m j)
          χ (a j c) δ hδ (hsmall j) u)
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  have hP : ‖P‖ ≤ M * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖v‖ * ‖frozenAction m (fun j => a j c) v‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖v‖ * (M * ‖v‖) :=
        mul_le_mul_of_nonneg_left (frozenAction_norm_le m (fun j => a j c) v M hM) (norm_nonneg _)
      _ = _ := by ring
  change ‖Q‖ ≤ (M + δ * ∑ j, (m j).bound) * ‖v‖ ^ 2
  calc
    _ = ‖(Q - P) + P‖ := by rw [sub_add_cancel]
    _ ≤ ‖Q - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ (δ * ∑ j, (m j).bound) * ‖v‖ ^ 2 + M * ‖v‖ ^ 2 := add_le_add herr hP
    _ = _ := by ring

end Burnett.Microlocal.SeparableSupBound

namespace Burnett.Microlocal.SeparableSupBound

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.SmoothSquarePartition Burnett.Microlocal.SeparablePairingLocalization
open Burnett.Microlocal.SmoothAngularTests (UnitSphere)
open Burnett.Analysis.LocalHminusFourier
open scoped InnerProduct BigOperators Topology ComplexConjugate ContDiff

/-- For a compactly localized sequence, the limsup of the absolute scalar pairing is bounded
by the uniform symbol bound times the squared L² input bound. -/
theorem eventually_finiteSeparable_pairing_le_uniform {J : Type} [Fintype J]
    (a m : J → BoundedSymbol Space) (ha : ∀ j, Continuous (a j : Space → ℂ))
    (K : Set Space) (hK : IsCompact K) (M : ℝ) (hM₀ : 0 ≤ M)
    (hM : ∀ x ∈ K, ∀ ξ : Space, ξ ≠ 0 → ‖∑ j, a j x * m j ξ‖ ≤ M)
    (u : ℕ → ComplexL2 Space) (B : ℝ) (hB : ∀ n, ‖u n‖ ≤ B)
    (hu : ∀ n, ∀ᵐ x ∂volume, x ∈ K ∨ u n x = 0)
    (hcomm : ∀ (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (j : J),
      Tendsto (fun n => cutoffCommutator (m j) (physicalCutoffSymbol χ hχ hc) (u n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖inner ℂ (u n) (finiteSeparableOperator a m (u n))‖ ≤ M * B ^ 2 + ε := by
  let C : ℝ := ∑ j, (m j).bound
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => (m j).bound_nonneg
  have hB₀ : 0 ≤ B := (norm_nonneg (u 0)).trans (hB 0)
  have hCB : 0 ≤ C * B ^ 2 := mul_nonneg hC (sq_nonneg _)
  let δ := ε / (2 * (1 + C * B ^ 2))
  have hden : 0 < 2 * (1 + C * B ^ 2) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδerr : δ * C * B ^ 2 ≤ ε / 2 := by
    have hδden : δ * (2 * (1 + C * B ^ 2)) = ε :=
      div_mul_cancel₀ _ hden.ne'
    nlinarith [hδ.le]
  obtain ⟨N, c, χ, hcenters, hs, hcompact, _, hosc, hsq⟩ :=
    exists_smooth_square_partition_for_oscillation K hK Set.univ (fun _ _ => univ_mem)
      (fun j => (a j : Space → ℂ)) ha δ hδ
  let b (i : Fin N) := physicalCutoffSymbol (χ i) (hs i) (hcompact i)
  have hb (x : Space) (hx : x ∈ K) : ∑ i, conj (b i x) * b i x = 1 :=
    sum_physicalCutoffSymbol_conj_mul χ hs hcompact (hsq x hx)
  have hsmall (i : Fin N) (j : J) (x : Space) (hx : b i x ≠ 0) :
      ‖a j x - a j (c i)‖ ≤ δ := by
    have hχx : χ i x ≠ 0 := by
      intro hz
      exact hx (by simp only [b, physicalCutoffSymbol_apply, hz, Complex.ofReal_zero])
    exact (hosc i x (subset_tsupport _ (Function.mem_support.mpr hχx)) j).le
  let P (n : ℕ) : ℂ := ∑ i, inner ℂ (symbolCLM (b i) (u n))
    (finiteSeparableOperator a m (symbolCLM (b i) (u n)))
  have hP (n : ℕ) : ‖P n‖ ≤ (M + δ * C) * B ^ 2 := by
    calc
      ‖P n‖ ≤ ∑ i, ‖inner ℂ (symbolCLM (b i) (u n))
          (finiteSeparableOperator a m (symbolCLM (b i) (u n)))‖ := norm_sum_le _ _
      _ ≤ ∑ i, (M + δ * C) * ‖symbolCLM (b i) (u n)‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          finiteSeparable_pairing_frozen_piece_bound a m (b i) (c i) (u n) M δ hδ.le
            (hM (c i) (hcenters i)) (hsmall i))
      _ = (M + δ * C) * ‖u n‖ ^ 2 := by
        rw [← Finset.mul_sum, sum_norm_sq_squareCutoff K b hb (u n) (hu n)]
      _ ≤ (M + δ * C) * B ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (add_nonneg hM₀ (mul_nonneg hδ.le hC))
        exact (sq_le_sq₀ (norm_nonneg _) hB₀).mpr (hB n)
  let Q (n : ℕ) := inner ℂ (u n) (finiteSeparableOperator a m (u n))
  have hlim : Tendsto (fun n => Q n - P n) atTop (𝓝 0) :=
    finiteSeparable_pairing_minus_localized_tendsto_zero a m K b hb u hu B hB
      (fun i j => hcomm (χ i) (hs i) (hcompact i) j)
  have hnear : ∀ᶠ n in atTop, ‖Q n - P n‖ < ε / 2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hlim) (ε / 2) (by positivity)
  filter_upwards [hnear] with n hn
  change ‖Q n‖ ≤ M * B ^ 2 + ε
  calc
    ‖Q n‖ = ‖(Q n - P n) + P n‖ := by rw [sub_add_cancel]
    _ ≤ ‖Q n - P n‖ + ‖P n‖ := norm_add_le _ _
    _ ≤ ε / 2 + (M + δ * C) * B ^ 2 := add_le_add hn.le (hP n)
    _ ≤ _ := by nlinarith [hδerr]

/-- The same bound for the actual complexified compactly localized real sequence. -/
theorem eventually_finiteSeparable_pairing_le_uniform_of_localized_weak_zero
    {J : Type} [Fintype J]
    (a m : J → BoundedSymbol Space) (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hsm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ j, DegreeZero (m j : Space → ℂ))
    (K : Set Space) (hK : IsCompact K) (M : ℝ) (hM₀ : 0 ≤ M)
    (hM : ∀ x ∈ K, ∀ ξ : Space, ξ ≠ 0 → ‖∑ j, a j x * m j ξ‖ ≤ M)
    (f : ℕ → Space → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (f n))
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n x, f n x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n x, f n x ≠ 0 → x ∈ K)
    (B : ℝ) (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : Burnett.X02.SobolevTestJet.D,
      Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    let u (n : ℕ) := (sourceSchwartz (hs n) χ₀ (hχ₀ n)).toLp 2 volume
    ∀ᶠ n in atTop, ‖inner ℂ (finiteSeparableOperator a m (u n)) (u n)‖ ≤ M * B ^ 2 + ε := by
  intro u
  have hBu (n : ℕ) : ‖u n‖ ≤ B := by
    have heq : ‖u n‖ = ‖(hf n).toLp (f n)‖ := by
      simp only [u, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f n x))
    exact heq.trans_le (hB n)
  have hu (n : ℕ) : ∀ᵐ x ∂volume, x ∈ K ∨ u n x = 0 := by
    filter_upwards [(sourceSchwartz (hs n) χ₀ (hχ₀ n)).coeFn_toLp 2 volume] with x hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · right
      change u n x = (f n x : ℂ) at hx
      have hz : f n x = 0 := by
        by_contra hn
        exact hk (hKf n x hn)
      rw [hx, hz, Complex.ofReal_zero]
  have hcomm (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (j : J) :
      Tendsto (fun n => cutoffCommutator (m j) (physicalCutoffSymbol χ hχ hc) (u n)) atTop (𝓝 0) :=
    cutoffCommutator_tendsto_zero_of_localized_weak_zero (m j) (physicalCutoffSymbol χ hχ hc)
      (hsm j) (hd j) (Complex.ofRealCLM.contDiff.comp hχ) (hc.comp_left Complex.ofReal_zero)
      f hs hf χ₀ hχ₀ B hB ht
  have h := eventually_finiteSeparable_pairing_le_uniform a m ha K hK M hM₀ hM u B hBu hu
    hcomm ε hε
  filter_upwards [h] with n hn
  rw [norm_inner_symm (𝕜 := ℂ)]
  exact hn

theorem norm_limit_le_of_eventually_le_add (q : ℕ → ℂ) (z : ℂ) (L : ℝ)
    (hz : Tendsto q atTop (𝓝 z))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ‖q n‖ ≤ L + ε) :
    ‖z‖ ≤ L := by
  by_contra! hgt
  let ε : ℝ := (‖z‖ - L) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hle : ‖z‖ ≤ L + ε := le_of_tendsto hz.norm (h ε hε)
  dsimp [ε] at hle
  linarith

/-- Positive homogeneity transfers the round-cosphere uniform bound to every nonzero frequency. -/
theorem offzero_symbol_bound_of_sphere {J : Type} [Fintype J]
    (a m : J → BoundedSymbol Space) (hd : ∀ j, DegreeZero (m j : Space → ℂ))
    (K : Set Space) (M : ℝ)
    (hM : ∀ x ∈ K, ∀ ξ : UnitSphere, ‖∑ j, a j x * m j ξ‖ ≤ M) :
    ∀ x ∈ K, ∀ ξ : Space, ξ ≠ 0 → ‖∑ j, a j x * m j ξ‖ ≤ M := by
  intro x hx ξ hξ
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let r := ‖ξ‖⁻¹
  have hr : 0 < r := inv_pos.mpr hξn
  let e : UnitSphere := ⟨r • ξ, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_cancel₀ hξn.ne'⟩
  have hsum : ∑ j, a j x * m j e = ∑ j, a j x * m j ξ := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun value => a j x * value) (hd j r hr ξ)
  simpa only [hsum] using hM x hx e

end Burnett.Microlocal.SeparableSupBound
