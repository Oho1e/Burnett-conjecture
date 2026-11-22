import Burnett.Analysis.Microlocal.OrderedCompactFunctionals

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.FixedSubsequenceSeparableExtension

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothSquarePartition (physicalCutoffSymbol)
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.CompactOrderedFunctional
open Burnett.Microlocal.SeparableSupBound (eventually_finiteSeparable_pairing_le_uniform
  offzero_symbol_bound_of_sphere)
open scoped InnerProduct BigOperators ContDiff Topology

/-- The actual restriction to the compact product of a finite smooth separated symbol. -/
def finiteSmoothRestriction {J : Type} [Fintype J]
    (K : BallData) (a m : J → BoundedSymbol Space)
    (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space)) : TestSpace K :=
  ∑ j, (⟨a j, ha j⟩ : C(Space, ℂ)).comp
    ⟨fun x : K.Point × UnitSphere => (x.1 : Space), continuous_subtype_val.comp continuous_fst⟩ *
      (restrictAngular (m j) (hm j)).comp ⟨Prod.snd, continuous_snd⟩

theorem finiteSmoothRestriction_apply {J : Type} [Fintype J]
    (K : BallData) (a m : J → BoundedSymbol Space)
    (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
    (x : K.Point) (ξ : UnitSphere) :
    finiteSmoothRestriction K a m ha hm (x, ξ) = ∑ j, a j x * m j ξ := by
  simp only [finiteSmoothRestriction, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, restrictAngular]

private def Q (A : ComplexL2 Space →L[ℂ] ComplexL2 Space) (x : ComplexL2 Space) : ℂ :=
  inner ℂ x (A x)

private theorem norm_orderedPairing_le_quadratic_sum
    (A : ComplexL2 Space →L[ℂ] ComplexL2 Space) (u v : ComplexL2 Space) :
    4 * ‖inner ℂ u (A v)‖ ≤
      (‖Q A (u + (1 : ℂ) • v)‖ + ‖Q A (u + (-1 : ℂ) • v)‖) +
        (‖Q A (u + Complex.I • v)‖ + ‖Q A (u + (-Complex.I) • v)‖) := by
  have h := congrArg norm (four_mul_orderedPairing_eq_quadratic A u v)
  change ‖(4 : ℂ) * inner ℂ u (A v)‖ =
    ‖(Q A (u + (1 : ℂ) • v) - Q A (u + (-1 : ℂ) • v)) -
      Complex.I * (Q A (u + Complex.I • v) - Q A (u + (-Complex.I) • v))‖ at h
  simp only [norm_mul, Complex.norm_ofNat] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)

/-- Asymptotic ordered pairing bound for any finite family of continuous base and smooth
degree-zero frequency factors, with the actual given commutators on both inputs. -/
theorem eventually_finiteSmoothPairing_le_of_commutations {J : Type} [Fintype J]
    (K : BallData) (a m : J → BoundedSymbol Space)
    (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ j, DegreeZero (m j : Space → ℂ))
    (u v : ℕ → ComplexL2 Space)
    (B : ℝ) (hBu : ∀ n, ‖u n‖ ≤ B) (hBv : ∀ n, ‖v n‖ ≤ B)
    (hu : ∀ n, ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ u n x = 0)
    (hv : ∀ n, ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ v n x = 0)
    (hcu : ∀ (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (j : J),
      Tendsto (fun n => cutoffCommutator (m j) (physicalCutoffSymbol χ hχ hc) (u n)) atTop (𝓝 0))
    (hcv : ∀ (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (j : J),
      Tendsto (fun n => cutoffCommutator (m j) (physicalCutoffSymbol χ hχ hc) (v n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖inner ℂ (u n) (finiteSeparableOperator a m (v n))‖ ≤
      ‖finiteSmoothRestriction K a m ha hm‖ * (2 * B) ^ 2 + ε := by
  let A := finiteSeparableOperator a m
  let M := ‖finiteSmoothRestriction K a m ha hm‖
  let D := M * (2 * B) ^ 2 + ε
  have hM : ∀ x ∈ K.closedBall, ∀ ξ : UnitSphere, ‖∑ j, a j x * m j ξ‖ ≤ M := by
    intro x hx ξ
    let y : K.Point := ⟨x, hx⟩
    have hy := (finiteSmoothRestriction K a m ha hm).norm_coe_le_norm (y, ξ)
    simpa only [finiteSmoothRestriction_apply] using hy
  have hcomb (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ∀ᶠ n in atTop, ‖Q A (u n + z • v n)‖ ≤ D := by
    let w (n : ℕ) := u n + z • v n
    have hBw (n : ℕ) : ‖w n‖ ≤ 2 * B := by
      calc
        _ ≤ ‖u n‖ + ‖z • v n‖ := norm_add_le _ _
        _ ≤ B + B := by
          apply add_le_add (hBu n)
          rw [norm_smul]
          exact (mul_le_mul_of_nonneg_right hz (norm_nonneg (v n))).trans
            (by simpa only [one_mul] using hBv n)
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
    have hcw (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (j : J) :
        Tendsto (fun n => cutoffCommutator (m j) (physicalCutoffSymbol χ hχ hc) (w n))
          atTop (𝓝 0) := by
      have h := (hcu χ hχ hc j).add ((hcv χ hχ hc j).const_smul z)
      simpa only [w, map_add, map_smul, smul_zero, add_zero] using h
    exact eventually_finiteSeparable_pairing_le_uniform a m ha K.closedBall (isCompact_closedBall _ _)
      M (norm_nonneg _) (offzero_symbol_bound_of_sphere a m hd K.closedBall _ hM)
      w (2 * B) hBw hsw hcw ε hε
  filter_upwards [hcomb 1 (by simp), hcomb (-1) (by simp), hcomb Complex.I (by simp),
    hcomb (-Complex.I) (by simp)] with n h₁ h₂ h₃ h₄
  have hp := norm_orderedPairing_le_quadratic_sum A (u n) (v n)
  change ‖inner ℂ (u n) (A (v n))‖ ≤ D
  linarith

end Burnett.Microlocal.FixedSubsequenceSeparableExtension

namespace Burnett.Microlocal.FixedSubsequenceSeparableExtension

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothSquarePartition (physicalCutoffSymbol)
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.CompactFunctionalProducer
open scoped InnerProduct BigOperators ContDiff Topology

/-- Convergence for every specified smooth finite separated symbol follows
on the original subsequence, from the actual list limits and the localized bounds. -/
theorem tendsto_finiteSmoothPairing_of_commonListLimits_and_commutations
    {ι J : Type} [Fintype J]
    (K : BallData) (a m : J → BoundedSymbol Space)
    (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ j, DegreeZero (m j : Space → ℂ))
    (u : ℕ → ι → ComplexL2 Space) (B : ℝ) (hB : ∀ n i, ‖u n i‖ ≤ B)
    (hsupp : ∀ n i, ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ u n i x = 0)
    (hcomm : ∀ (i : ι) (s : BoundedSymbol Space)
        (_ : ContDiffOn ℝ ∞ (s : Space → ℂ) ({0}ᶜ : Set Space))
        (_ : DegreeZero (s : Space → ℂ))
        (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
      Tendsto (fun n => cutoffCommutator s (physicalCutoffSymbol χ hχ hc) (u n i)) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (F : ι → ι → (TestSpace K →L[ℂ] ℂ))
    (hF : ∀ ps i j, Tendsto (fun n => inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j)))
      atTop (𝓝 (F i j (separableRestriction K ps)))) (i j : ι) :
    Tendsto (fun n => inner ℂ (u (σ n) i) (finiteSeparableOperator a m (u (σ n) j)))
      atTop (𝓝 (F i j (finiteSmoothRestriction K a m ha hm))) := by
  let R := finiteSmoothRestriction K a m ha hm
  let C := (2 * B) ^ 2
  let N := ‖F i j‖
  have hC : 0 ≤ C := sq_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := ε / (4 * (1 + C + N))
  have hden : 0 < 4 * (1 + C + N) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have heps : δ * (4 * (1 + C + N)) = ε := div_mul_cancel₀ _ hden.ne'
  have hcδ : δ * C ≤ ε / 4 := by nlinarith [mul_nonneg hδ.le hN, hδ.le]
  have hnδ : N * δ ≤ ε / 4 := by nlinarith [mul_nonneg hδ.le hC, hδ.le]
  obtain ⟨ps, hps⟩ := Metric.denseRange_iff.mp (separableRestriction_dense K) R δ hδ
  have happ : ‖R - separableRestriction K ps‖ < δ := by simpa only [dist_eq_norm] using hps
  let neg := rationalScale (-1) 0 ps
  let b (k : Fin neg.length) := baseSymbol K (neg.get k).1
  let p (k : Fin neg.length) := complexRationalAngularSymbol (neg.get k).2
  let A := Sum.elim a b
  let M := Sum.elim m p
  have hA : ∀ k, Continuous (A k : Space → ℂ)
    | .inl k => ha k
    | .inr k => (complexBase_contDiff K (neg.get k).1).continuous
  have hM : ∀ k, ContDiffOn ℝ ∞ (M k : Space → ℂ) ({0}ᶜ : Set Space)
    | .inl k => hm k
    | .inr k => complexRationalAngular_contDiffOn (neg.get k).2
  have hD : ∀ k, DegreeZero (M k : Space → ℂ)
    | .inl k => hd k
    | .inr k => complexRationalAngular_degreeZero (neg.get k).2
  have hOp : finiteSeparableOperator A M = finiteSeparableOperator a m - listOperator K ps := by
    have hsum : finiteSeparableOperator A M =
        finiteSeparableOperator a m + finiteSeparableOperator b p := by
      simp only [finiteSeparableOperator, Fintype.sum_sum_type, A, M, Sum.elim_inl, Sum.elim_inr]
    rw [hsum, ← listOperator_eq_finiteSeparable K neg]
    change finiteSeparableOperator a m + listOperator K (rationalScale (-1) 0 ps) = _
    rw [listOperator_rat_smul]
    simp [sub_eq_add_neg]
  have hR : finiteSmoothRestriction K A M hA hM = R - separableRestriction K ps := by
    ext z
    obtain ⟨x, ξ⟩ := z
    change finiteSmoothRestriction K A M hA hM (x, ξ) =
      (finiteSmoothRestriction K a m ha hm - separableRestriction K ps) (x, ξ)
    rw [finiteSmoothRestriction_apply, ContinuousMap.sub_apply, finiteSmoothRestriction_apply]
    simp only [Fintype.sum_sum_type, A, M, Sum.elim_inl, Sum.elim_inr, b, p]
    rw [← separableValue_eq_finite K neg, ← separableRestriction_apply]
    change _ + separableRestriction K (rationalScale (-1) 0 ps) (x, ξ) = _
    rw [separableRestriction_rat_smul, neg_one_smul, ContinuousMap.neg_apply, sub_eq_add_neg]
  have hh := eventually_finiteSmoothPairing_le_of_commutations K A M hA hM hD
    (fun n => u n i) (fun n => u n j) B (fun n => hB n i) (fun n => hB n j)
    (fun n => hsupp n i) (fun n => hsupp n j)
    (fun χ hχ hc k => hcomm i (M k) (hM k) (hD k) χ hχ hc)
    (fun χ hχ hc k => hcomm j (M k) (hM k) (hD k) χ hχ hc) (ε / 4) (by positivity)
  have hdiff := hσ.tendsto_atTop.eventually hh
  simp only [hOp, hR, ContinuousLinearMap.sub_apply, inner_sub_right] at hdiff
  have hlist := (Metric.tendsto_nhds.mp (hF ps i j)) (ε / 4) (by positivity)
  have hFdiff : ‖F i j (separableRestriction K ps) - F i j R‖ ≤ ε / 4 := by
    calc
      _ = ‖F i j (R - separableRestriction K ps)‖ := by rw [map_sub, norm_sub_rev]
      _ ≤ N * ‖R - separableRestriction K ps‖ := (F i j).le_opNorm _
      _ ≤ N * δ := mul_le_mul_of_nonneg_left happ.le hN
      _ ≤ _ := hnδ
  filter_upwards [hdiff, hlist] with n h₁ h₂
  let t := inner ℂ (u (σ n) i) (finiteSeparableOperator a m (u (σ n) j))
  let r := inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j))
  let z := F i j (separableRestriction K ps)
  let w := F i j R
  have ht₁ : ‖t - r‖ ≤ ε / 2 := by
    have hh₁ : ‖t - r‖ ≤ ‖R - separableRestriction K ps‖ * C + ε / 4 := h₁
    have hh₂ := (mul_le_mul_of_nonneg_right happ.le hC).trans hcδ
    linarith
  have ht₂ : ‖r - z‖ < ε / 4 := by simpa only [dist_eq_norm] using h₂
  change dist t w < ε
  rw [dist_eq_norm]
  calc
    _ = ‖(t - r) + (r - z) + (z - w)‖ := by congr 1; abel
    _ ≤ (‖t - r‖ + ‖r - z‖) + ‖z - w‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ < ε := by
      change ‖z - w‖ ≤ ε / 4 at hFdiff
      linarith

end Burnett.Microlocal.FixedSubsequenceSeparableExtension

namespace Burnett.Microlocal.FixedSubsequenceSeparableExtension

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothSquarePartition (physicalCutoffSymbol)
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.CompactFunctionalProducer
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology

/-- The ordered limits extend to all finite smooth separated tests on the already selected
subsequence of the actual localized real weak-zero component sequences. -/
theorem tendsto_finiteSmoothPairing_of_commonListLimits_localized_weak_zero
    {ι J : Type} [Fintype J]
    (K : BallData) (a m : J → BoundedSymbol Space)
    (ha : ∀ j, Continuous (a j : Space → ℂ))
    (hm : ∀ j, ContDiffOn ℝ ∞ (m j : Space → ℂ) ({0}ᶜ : Set Space))
    (hd : ∀ j, DegreeZero (m j : Space → ℂ))
    (f : ℕ → ι → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n c x, f n c x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : ι) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (F : ι → ι → (TestSpace K →L[ℂ] ℂ))
    (hF : ∀ ps i j, Tendsto (fun n =>
      let u := (sourceSchwartz (hs (σ n) i) χ₀ (hχ₀ (σ n) i)).toLp 2 volume
      let v := (sourceSchwartz (hs (σ n) j) χ₀ (hχ₀ (σ n) j)).toLp 2 volume
      inner ℂ u (listOperator K ps v)) atTop (𝓝 (F i j (separableRestriction K ps)))) (i j : ι) :
    Tendsto (fun n =>
      let u := (sourceSchwartz (hs (σ n) i) χ₀ (hχ₀ (σ n) i)).toLp 2 volume
      let v := (sourceSchwartz (hs (σ n) j) χ₀ (hχ₀ (σ n) j)).toLp 2 volume
      inner ℂ u (finiteSeparableOperator a m v))
      atTop (𝓝 (F i j (finiteSmoothRestriction K a m ha hm))) := by
  let w (n : ℕ) (c : ι) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
  have hnorm (n : ℕ) (c : ι) : ‖w n c‖ ≤ B := by
    have heq : ‖w n c‖ = ‖(hf n c).toLp (f n c)‖ := by
      simp only [w, SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f n c x))
    exact heq.trans_le (hB n c)
  have hsupport (n : ℕ) (c : ι) : ∀ᵐ x ∂volume, x ∈ K.closedBall ∨ w n c x = 0 := by
    filter_upwards [(sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).coeFn_toLp 2 volume] with x hx
    by_cases hk : x ∈ K.closedBall
    · exact Or.inl hk
    · right
      change w n c x = (f n c x : ℂ) at hx
      have hz : f n c x = 0 := by
        by_contra hn
        exact hk (hKf n c x hn)
      rw [hx, hz, Complex.ofReal_zero]
  apply tendsto_finiteSmoothPairing_of_commonListLimits_and_commutations
    K a m ha hm hd w B hnorm hsupport _ σ hσ F hF i j
  intro c s hsm hsd χ hχ hc
  exact cutoffCommutator_tendsto_zero_of_localized_weak_zero
    s (physicalCutoffSymbol χ hχ hc) hsm hsd
    (Complex.ofRealCLM.contDiff.comp hχ) (hc.comp_left Complex.ofReal_zero)
    (fun n => f n c) (fun n => hs n c) (fun n => hf n c) χ₀ (fun n => hχ₀ n c)
    B (fun n => hB n c) (ht c)

end Burnett.Microlocal.FixedSubsequenceSeparableExtension
