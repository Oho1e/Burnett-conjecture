import Burnett.Analysis.PrincipalEnergy.Commutator.CenteredWaveletPackets
import Burnett.Analysis.PrincipalEnergy.Commutator.SeparatedKernelBounds

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter
open scoped ComplexConjugate Topology

private theorem integrable_distant_kernel_section {K : Space → Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds K C) (f : SchwartzMap Space ℂ) (c : Space)
    (d : ℝ) (hd : 0<d) (hGap : ∀ y, f y≠0 → d≤‖c-y‖) :
    Integrable (fun y => K c y*f y) volume := by
  let F (y : Space) := K c y*f y
  have hZero (y : Space) (hy : ‖c-y‖<d) : F y=0 := by
    have hf : f y=0 := by
      by_contra hn
      exact (not_le_of_gt hy) (hGap y hn)
    simp [F,hf]
  have hCont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hcy : c=y
    · subst y
      have hSmall : ‖c-c‖<d := by simpa using hd
      have hOpen : IsOpen {z : Space | ‖c-z‖<d} :=
        isOpen_lt (continuous_const.sub continuous_id).norm continuous_const
      have hNear : ∀ᶠ z : Space in 𝓝 c, ‖c-z‖<d := hOpen.mem_nhds hSmall
      change Tendsto F (𝓝 c) (𝓝 (F c))
      rw [hZero c hSmall]
      exact tendsto_const_nhds.congr' (hNear.mono fun z hz => (hZero z hz).symm)
    · have h := (hK.continuousAt_offDiagonal c y hcy).comp
        (f := fun z : Space => (c,z)) (continuous_const.prodMk continuous_id).continuousAt
      exact h.mul f.continuous.continuousAt
  refine ((f.integrable (μ := (volume : Measure Space))).norm.const_mul (C*(d^4)⁻¹)).mono'
    hCont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  change ‖K c y*f y‖≤(C*(d^4)⁻¹)*‖f y‖
  by_cases hfy : f y=0
  · simp [hfy]
  have hD := hGap y hfy
  have hP := hd.trans_le hD
  have hInv : (‖c-y‖^4)⁻¹≤(d^4)⁻¹ :=
    (inv_le_inv₀ (pow_pos hP _) (pow_pos hd _)).mpr (pow_le_pow_left₀ hd.le hD _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((hK.size c y (sub_ne_zero.mp (norm_pos_iff.mp hP))).trans
      (mul_le_mul_of_nonneg_left hInv hK.const_nonneg)) (norm_nonneg _)

/-- The integral of a separated pairing with a mean-zero output is
unchanged by subtracting the target kernel at a fixed separated center. -/
theorem meanZero_separatedPair_eq_kernelDifference {K : Space → Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds K C)
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hPair : ∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
      ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
      R f g = ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
        ∂((volume : Measure Space).prod volume))
    (f g : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) (hg : (∫ x, g x)=0)
    (c : Space) (d : ℝ) (hd : 0<d)
    (hGap : ∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖)
    (hCenter : ∀ y : Space, f y≠0 → d≤‖c-y‖) :
    let I (p : Space × Space) := conj (g p.1)*((K p.1 p.2-K c p.2)*f p.2)
    Integrable I ((volume : Measure Space).prod volume) ∧
      R f g = ∫ p, I p ∂((volume : Measure Space).prod volume) := by
  intro I
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  let A (p : Space × Space) := conj (g p.1)*(K p.1 p.2*f p.2)
  let B (p : Space × Space) := conj (g p.1)*(K c p.2*f p.2)
  have hA : Integrable A μ := integrable_separated_kernel_pair hK f g d hd hGap
  have hSection := integrable_distant_kernel_section hK f c d hd hCenter
  have hG : Integrable (fun x => conj (g x)) :=
    (g.integrable (μ := (volume : Measure Space))).norm.mono' g.continuous.aestronglyMeasurable.star
      (Eventually.of_forall fun x => (Complex.norm_conj (g x)).le)
  have hB : Integrable B μ := hG.mul_prod hSection
  have hI : I = fun p => A p-B p := by funext p; dsimp only [I,A,B]; ring
  have hZero : (∫ p, B p ∂μ)=0 := by
    have hProd : (∫ p, B p ∂μ)=(∫ x, conj (g x))*(∫ y, K c y*f y) :=
      integral_prod_mul (fun x : Space => conj (g x)) (fun y : Space => K c y*f y)
    rw [hProd,integral_conj,hg,map_zero,zero_mul]
  refine ⟨?_,?_⟩
  · rw [hI]
    exact hA.sub hB
  · rw [hI,integral_sub hA hB,hZero,sub_zero]
    exact hPair f g hf d hd hGap

/-- The actual translated wavelet pairing in the far region. The output
packet has scale s, mean zero, and center x. -/
theorem centeredWaveletPair_far_bound {K : Space → Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds K C)
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hPair : ∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
      ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
      R f g = ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
        ∂((volume : Measure Space).prod volume))
    (θ η : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0)
    (hη₀ : (∫ z, η z)=0) (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≤t)
    (x y : Space) (hFar : 4*t≤‖x-y‖) :
    ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x)‖≤
      32*C*s*(∫ z, ‖θ z‖)*(∫ z, ‖η z‖)*(‖x-y‖^5)⁻¹ := by
  let f := centeredWavelet θ hθ t ht y
  let g := centeredWavelet η hη s hs x
  let D := ‖x-y‖
  have hD : 0<D := (mul_pos (by norm_num : 0<(4:ℝ)) ht).trans_le hFar
  have hf : HasCompactSupport (f : Space → ℂ) := centeredWavelet_hasCompactSupport θ hθ t ht y
  have hg : (∫ z, g z)=0 := (centeredWavelet_integral η hη s hs x).trans hη₀
  have hIn (z : Space) (hz : f z≠0) : ‖z-y‖≤t := by
    have hSupp : z ∈ tsupport (f : Space → ℂ) := subset_closure hz
    have hBall : z ∈ Metric.closedBall y t := centeredWavelet_support θ hθ t ht y hSupp
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hBall
  have hOut (w : Space) (hw : g w≠0) : ‖x-w‖≤s := by
    have hSupp : w ∈ tsupport (g : Space → ℂ) := subset_closure hw
    have hBall : w ∈ Metric.closedBall x s := centeredWavelet_support η hη s hs x hSupp
    rw [norm_sub_rev x w,← dist_eq_norm]
    exact Metric.mem_closedBall.mp hBall
  have hCenter (z : Space) (hz : f z≠0) : D/2≤‖x-z‖ := by
    have hTri := norm_add_le (x-z) (z-y)
    rw [show x-z+(z-y)=x-y by abel] at hTri
    change D≤‖x-z‖+‖z-y‖ at hTri
    change 4*t≤D at hFar
    linarith [hIn z hz]
  have hGap (w z : Space) (hz : f z≠0) (hw : g w≠0) : D/2≤‖w-z‖ := by
    have h₁ := norm_add_le (x-w) (w-z)
    rw [show x-w+(w-z)=x-z by abel] at h₁
    have h₂ := norm_add_le (x-z) (z-y)
    rw [show x-z+(z-y)=x-y by abel] at h₂
    change D≤‖x-z‖+‖z-y‖ at h₂
    change 4*t≤D at hFar
    linarith [hIn z hz,hOut w hw]
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  let I (p : Space × Space) := conj (g p.1)*((K p.1 p.2-K x p.2)*f p.2)
  obtain ⟨_,hRep⟩ := meanZero_separatedPair_eq_kernelDifference hK R hPair f g hf hg
    x (D/2) (half_pos hD) hGap hCenter
  let A := C*s*((D/2)^5)⁻¹
  let Z (p : Space × Space) := ‖g p.1‖*‖f p.2‖
  have hA : Integrable (fun p : Space × Space => A*Z p) μ :=
    ((g.integrable (μ := (volume : Measure Space))).norm.mul_prod
      (f.integrable (μ := (volume : Measure Space))).norm).const_mul A
  have hDom (p : Space × Space) : ‖I p‖≤A*Z p := by
    by_cases hf₀ : f p.2=0
    · simp [I,Z,hf₀]
    by_cases hg₀ : g p.1=0
    · simp [I,Z,hg₀]
    have hDist := hCenter p.2 hf₀
    have hPos := (half_pos hD).trans_le hDist
    have hxy : x≠p.2 := sub_ne_zero.mp (norm_pos_iff.mp hPos)
    have hShift : ‖x-p.1‖≤‖x-p.2‖/2 := by
      change 4*t≤D at hFar
      linarith [hOut p.1 hg₀]
    have hInv : (‖x-p.2‖^5)⁻¹≤((D/2)^5)⁻¹ :=
      (inv_le_inv₀ (pow_pos hPos _) (pow_pos (half_pos hD) _)).mpr
        (pow_le_pow_left₀ (half_pos hD).le hDist _)
    have hDiff : ‖K p.1 p.2-K x p.2‖≤A := by
      rw [norm_sub_rev]
      exact (hK.target x p.1 p.2 hxy hShift).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (hOut p.1 hg₀) hK.const_nonneg) hInv
          (by positivity) (mul_nonneg hK.const_nonneg hs.le))
    calc
      _ = ‖K p.1 p.2-K x p.2‖*Z p := by dsimp only [I,Z]; rw [norm_mul,Complex.norm_conj,norm_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDiff (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hScale : ((D/2)^5)⁻¹=32*(D^5)⁻¹ := by field_simp [hD.ne']; ring
  calc
    _ = ‖∫ p, I p ∂μ‖ := congrArg norm hRep
    _ ≤ ∫ p, ‖I p‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, A*Z p ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      hA (Eventually.of_forall hDom)
    _ = _ := by
      have hProd : (∫ p, Z p ∂μ)=(∫ z, ‖g z‖)*(∫ z, ‖f z‖) :=
        integral_prod_mul (fun z : Space => ‖g z‖) (fun z : Space => ‖f z‖)
      rw [integral_const_mul,hProd]
      dsimp only [f,g]
      rw [centeredWavelet_integral_norm,centeredWavelet_integral_norm]
      dsimp only [A]
      rw [hScale]
      dsimp only [D]
      ring

end Burnett.Analysis.CarlesonEmbedding
