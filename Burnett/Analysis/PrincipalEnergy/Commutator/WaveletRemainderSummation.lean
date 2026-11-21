import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletBlockOpening
import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletH1Reconstruction
import Burnett.Analysis.PrincipalEnergy.Commutator.FiniteWaveletPairSum

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.CotlarStein
open Burnett.Analysis.SymmetricEnergy (coordinateH1)
open scoped BigOperators ComplexConjugate Topology

private theorem reconstructing_scale_pos {t : ℝ} (ht : 0<t) (N j : ℕ) :
    0<reproducingScale t N j := by
  unfold reproducingScale compactWaveletScale
  positivity

/-- The finite geometric block sum converges to the original Schwartz
pairing in the first-order norm. Its bound depends only on the two \(L^2\) norms. -/
theorem exists_wavelet_remainder_L2_pair_bound
    (φ ψ θ : SchwartzMap Space ℂ) (hφ : (∫ z, φ z)=1) (hψ : (∫ z, ψ z)=0)
    (hθ : ∀ z, 1<‖z‖ → θ z=0) (hFac : WaveletFactorization φ ψ θ) :
    ∃ M : ℝ, 0≤M ∧
      ∀ (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
        (_hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
        (_hSkew : ∀ f g, R g f= -conj (R f g))
        (D : ℝ) (_hD : 0≤D) (_hR : ∀ f g, ‖R f g‖≤D*coordinateH1 f*coordinateH1 g)
        (A B : ℝ) (_hA : 0≤A) (_hB : 0≤B),
      (∀ s t : ℝ, ∀ (hs : 0<s) (ht : 0<t), s≤t →
        (∀ x y : Space,
          ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet θ hθ s hs x)‖≤
            A*Real.sqrt (s/t)*(t^4)⁻¹) ∧
        (∀ x y : Space, 4*t≤‖x-y‖ →
          ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet θ hθ s hs x)‖≤
            B*s*(‖x-y‖^5)⁻¹)) →
      ∀ (t₀ : ℝ), 0<t₀ → ∀ f g : SchwartzMap Space ℂ,
        ‖R f g‖≤M*(A*(∫ z, waveletNearCutoff 1 z)+B*(∫ z, inverseFifthTail 1 z)/4)*
          ‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  obtain ⟨Q,hQ,hSquare⟩ := exists_waveletMultiplier_square_bound ψ hψ
  let β := Real.sqrt (1/2:ℝ)
  have hβ : 0≤β := Real.sqrt_nonneg _
  have hβ₁ : β<1 := by
    simpa only [β,Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)
  let J := 2*(1-β)⁻¹
  have hJ : 0≤J := mul_nonneg (by norm_num) (inv_nonneg.mpr (sub_nonneg.mpr hβ₁.le))
  refine ⟨J*Q,mul_nonneg hJ hQ,?_⟩
  intro R hLin hSkew D hD hR A B hA hB hPacket t₀ ht₀ f g
  let C := A*(∫ z, waveletNearCutoff 1 z)+B*(∫ z, inverseFifthTail 1 z)/4
  have hBall : 0≤∫ z, waveletNearCutoff 1 z := by
    apply integral_nonneg
    intro z
    change (0:ℝ)≤waveletNearCutoff 1 z
    by_cases hz : z ∈ Metric.closedBall (0:Space) (4*1)
    · simpa only [waveletNearCutoff,Set.indicator_of_mem hz] using (zero_le_one : (0:ℝ)≤1)
    · simpa only [waveletNearCutoff,Set.indicator_of_notMem hz] using (le_rfl : (0:ℝ)≤0)
  have hTail : 0≤∫ z : Space, inverseFifthTail 1 z := integral_nonneg (inverseFifthTail_nonneg 1)
  have hC : 0≤C := by dsimp only [C]; positivity
  let S := reproducingPartialSchwartz ψ θ t₀ ht₀
  have hL0 (w : SchwartzMap Space ℂ) : R 0 w=0 := by simpa using hLin w w w 1
  have hR0 (w : SchwartzMap Space ℂ) : R w 0=0 := by rw [hSkew 0 w,hL0,map_zero,neg_zero]
  have hLadd (u v w : SchwartzMap Space ℂ) : R (u+v) w=R u w+R v w := by
    simpa only [neg_one_smul,neg_one_mul,sub_neg_eq_add] using hLin u v w (-1)
  have hRadd (u v w : SchwartzMap Space ℂ) : R u (v+w)=R u v+R u w := by
    rw [hSkew (v+w) u,hLadd,map_add,hSkew v u,hSkew w u]
    ring
  have hSL (I : Finset ℕ) (U : ℕ → SchwartzMap Space ℂ) (v : SchwartzMap Space ℂ) :
      R (∑ i ∈ I, U i) v=∑ i ∈ I, R (U i) v := by
    induction I using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,hL0]
    | insert i I hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,hLadd,ih]
  have hSR (I : Finset ℕ) (U : ℕ → SchwartzMap Space ℂ) (v : SchwartzMap Space ℂ) :
      R v (∑ i ∈ I, U i)=∑ i ∈ I, R v (U i) := by
    induction I using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,hR0]
    | insert i I hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,hRadd,ih]
  have hFinite (N : ℕ) : ‖R (S N f) (S N g)‖≤(J*Q)*C*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
    let I := Finset.range (N+N)
    let s (i : ℕ) := reproducingScale t₀ N i
    have hs (i : ℕ) : 0<s i := reconstructing_scale_pos ht₀ N i
    let U (i : ℕ) := schwartzWaveletAction ψ (s i) (hs i) f
    let V (i : ℕ) := schwartzWaveletAction ψ (s i) (hs i) g
    let X (i : ℕ) := schwartzWaveletAction θ (s i) (hs i) (U i)
    let Y (i : ℕ) := schwartzWaveletAction θ (s i) (hs i) (V i)
    have hScaleNorm (i j : ℕ) :
        ‖R (X i) (Y j)‖≤C*β^(scaleGap i j)*‖(U i).toLp 2 volume‖*‖(V j).toLp 2 volume‖ := by
      by_cases hij : i≤j
      · obtain ⟨hScale,hRatio⟩ := reproducingScale_ratio_sqrt ht₀ N i j hij
        have h :=
          schwartzWaveletPair_block_bound R hLin hSkew D hR θ θ hθ hθ A B hA hB (s j) (s i) (hs j) (hs i)
            hScale (fun x y _ => (hPacket _ _ (hs j) (hs i) hScale).1 x y)
            (hPacket _ _ (hs j) (hs i) hScale).2 (U i) (V j)
        change Real.sqrt (s j/s i)=β^(scaleGap i j) at hRatio
        simpa only [X,Y,C,hRatio] using h
      · have hji : j ≤ i := (lt_of_not_ge hij).le
        obtain ⟨hScale,hRatio⟩ := reproducingScale_ratio_sqrt ht₀ N j i hji
        have h :=
          schwartzWaveletPair_block_bound R hLin hSkew D hR θ θ hθ hθ A B hA hB (s i) (s j) (hs i) (hs j)
            hScale (fun x y _ => (hPacket _ _ (hs i) (hs j) hScale).1 x y)
            (hPacket _ _ (hs i) (hs j) hScale).2 (V j) (U i)
        change Real.sqrt (s i/s j)=β^(scaleGap j i) at hRatio
        have hGap : scaleGap j i=scaleGap i j := by unfold scaleGap; omega
        rw [hSkew (Y j) (X i),norm_neg,Complex.norm_conj]
        apply h.trans_eq
        rw [hRatio,hGap]
        dsimp only [C]
        ring
    have hTwo (w : SchwartzMap Space ℂ) :
        (∑ i ∈ I, ‖(schwartzWaveletAction ψ (s i) (hs i) w).toLp 2 volume‖^2)≤Q*‖w.toLp 2 volume‖^2 := by
      simp_rw [schwartzWaveletAction_toLp]
      exact hSquare (t₀*(2:ℝ)^N) (by positivity) I (w.toLp 2 volume)
    have hU : Real.sqrt (∑ i ∈ I, ‖(U i).toLp 2 volume‖^2)≤Real.sqrt Q*‖f.toLp 2 volume‖ :=
      (Real.sqrt_le_sqrt (hTwo f)).trans_eq (by
        rw [Real.sqrt_mul hQ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)])
    have hV : Real.sqrt (∑ i ∈ I, ‖(V i).toLp 2 volume‖^2)≤Real.sqrt Q*‖g.toLp 2 volume‖ :=
      (Real.sqrt_le_sqrt (hTwo g)).trans_eq (by
        rw [Real.sqrt_mul hQ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)])
    change ‖R (∑ i ∈ I, X i) (∑ j ∈ I, Y j)‖≤_
    rw [hSL]
    simp_rw [hSR]
    have hSum := finite_geometric_wavelet_pair_bound (fun i j => R (X i) (Y j))
      (fun i => ‖(U i).toLp 2 volume‖) (fun j => ‖(V j).toLp 2 volume‖) C β hC hβ hβ₁ hScaleNorm I I
    calc
      _ ≤ C*J*Real.sqrt (∑ i ∈ I, ‖(U i).toLp 2 volume‖^2)*
        Real.sqrt (∑ i ∈ I, ‖(V i).toLp 2 volume‖^2) := hSum
      _ ≤ C*J*(Real.sqrt Q*‖f.toLp 2 volume‖)*(Real.sqrt Q*‖g.toLp 2 volume‖) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hU (mul_nonneg hC hJ)) hV
          (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by
        rw [show C*J*(Real.sqrt Q*‖f.toLp 2 volume‖)*(Real.sqrt Q*‖g.toLp 2 volume‖) =
          C*J*(Real.sqrt Q)^2*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ by ring,Real.sq_sqrt hQ]
        ring
  have hRf := reproducing_windows_coordinateH1_tendsto φ ψ θ hφ hFac t₀ ht₀ f
  have hRg := reproducing_windows_coordinateH1_tendsto φ ψ θ hφ hFac t₀ ht₀ g
  have hT : Tendsto (fun N => R (S N f) (S N g)) atTop (𝓝 (R f g)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hL (u v w : SchwartzMap Space ℂ) : R (u-v) w=R u w-R v w := by
      simpa only [one_smul,one_mul] using hLin u v w 1
    have hVd (u v w : SchwartzMap Space ℂ) : R u (v-w)=R u v-R u w := by
      rw [hSkew (v-w) u,hL,map_sub,hSkew v u,hSkew w u]
      ring
    let E (N : ℕ) :=
      D*coordinateH1 (S N f-f)*(coordinateH1 (S N g-g)+coordinateH1 g)+
        D*coordinateH1 f*coordinateH1 (S N g-g)
    have hE : Tendsto E atTop (𝓝 0) := by
      have h := ((hRf.const_mul D).mul (hRg.add_const (coordinateH1 g))).add
        (hRg.const_mul (D*coordinateH1 f))
      simpa only [E,mul_zero,zero_mul,zero_add] using h
    have hDom (N : ℕ) : ‖R (S N f) (S N g)-R f g‖≤E N := by
      have hG : coordinateH1 (S N g)≤coordinateH1 (S N g-g)+coordinateH1 g := by
        rw [← schwartzIntoCoordinateH1_norm,← schwartzIntoCoordinateH1_norm,← schwartzIntoCoordinateH1_norm,
          map_sub]
        exact le_trans (le_of_eq (congrArg norm (sub_add_cancel
          (schwartzIntoCoordinateH1 (S N g)) (schwartzIntoCoordinateH1 g)).symm))
          (norm_add_le _ _)
      have hDiff :
          R (S N f) (S N g)-R f g=R (S N f-f) (S N g)+R f (S N g-g) := by
        rw [hL,hVd]
        ring
      rw [hDiff]
      exact (norm_add_le _ _).trans (add_le_add
        ((hR _ _).trans (mul_le_mul_of_nonneg_left hG (mul_nonneg hD (Real.sqrt_nonneg _))))
        (hR _ _))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hDom)
  exact le_of_tendsto' hT.norm hFinite

end Burnett.Analysis.CarlesonEmbedding
