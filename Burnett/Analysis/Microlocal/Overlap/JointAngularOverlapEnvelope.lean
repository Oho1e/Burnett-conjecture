import Burnett.Analysis.Microlocal.Overlap.JointAngularShellDecay

/-! Uniform overlap estimates for the actual shell kernel with a moving output symbol. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 3500000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Set Burnett.Fourier Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapKernel
open scoped ContDiff

open private far_decay_to_integrable_envelope
  from Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierLimit

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Both chart kernels sample the same symbol at the actual target output
position. One Schur-decay envelope works for the whole compact overlap. -/
theorem jointAngular_overlapShell_uniform_envelope
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (p : E → BoundedSymbol E)
    (hp : ContDiffOn ℝ ∞ (fun z : E × E => p z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (hSlice : ∀ x, ContDiffOn ℝ ∞ (p x : E → ℂ) ({0}ᶜ : Set E)) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (j : ℕ) (x : E), x ∈ K → ∀ y ∈ K,
      let s := dyadicScale j
      ‖halfDensityKernelDifference Φ w (shellKernel (p (Φ x)) (hSlice (Φ x)) j) x y‖ ≤
        C * s^3 / (1 + s * b * ‖x - y‖)^5 := by
  intro Φ w
  obtain ⟨q, L, W, H, δ, hq, hL, hW, hH, hδ, hNear, hΦ, hLip, hInv, hw, hwLip⟩ :=
    overlapKernel_geometry_bounds c d K hK hKU hConv
  obtain ⟨a, ha, hFar⟩ := overlapFar_uniform_arguments c d K hK hKU hδ
  have hImage : IsCompact (Φ '' K) :=
    hK.image_of_continuousOn ((overlapTransition_contDiffOn c d).continuousOn.mono hKU)
  obtain ⟨C₀, C₁, hC₀, hC₁, hDecay⟩ :=
    shellKernel_decay_bounds_uniform_on_compact p hp hSlice (Φ '' K) hImage
  let Cn := W * H * C₀ / (q / 2) + W^2 * C₁ * L / (q / 2)^2
  let Cf := 2 * W^2 * C₀
  let R := Metric.diam K + 1
  let b := min (q / 2) (a / R)
  let C := Cn + Cf / a
  have hR : 0 < R := by dsimp only [R]; linarith [Metric.diam_nonneg (s := K)]
  have hb : 0 < b := lt_min (half_pos hq) (div_pos ha hR)
  have hn₀ : 0 ≤ Cn := by dsimp only [Cn]; positivity
  have hf₀ : 0 ≤ Cf := by dsimp only [Cf]; positivity
  refine ⟨b, C, hb, add_nonneg hn₀ (div_nonneg hf₀ ha.le), fun j x hx y hy => ?_⟩
  let s := dyadicScale j
  let r := ‖x - y‖
  let k := shellKernel (p (Φ x)) (hSlice (Φ x)) j
  let D := 1 + s * b * r
  have hs : 0 < s := by unfold s dyadicScale; positivity
  have hr : 0 ≤ r := norm_nonneg _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hKx : Φ x ∈ Φ '' K := mem_image_of_mem Φ hx
  have hk : Differentiable ℝ k := fun z =>
    (shellKernel_hasFDerivAt (p (Φ x)) (hSlice (Φ x)) j z).differentiableAt
  have hDec₀ (z : E) : (1 + s * ‖z‖)^7 * ‖k z‖ ≤ C₀ * s^4 := (hDecay _ hKx j z).1
  have hDec₁ (z : E) : (1 + s * ‖z‖)^7 * ‖fderiv ℝ k z‖ ≤ C₁ * s^5 := (hDecay _ hKx j z).2
  have hrR : r ≤ R := (by
    simpa only [r, dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded hx hy
    : r ≤ Metric.diam K).trans (le_add_of_nonneg_right zero_le_one)
  have hba : b * r ≤ a := calc
    _ ≤ b * R := mul_le_mul_of_nonneg_left hrR hb.le
    _ ≤ (a / R) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    _ = a := div_mul_cancel₀ a hR.ne'
  change ‖halfDensityKernelDifference Φ w k x y‖ ≤ C * s^3 / D^5
  by_cases hsmall : r ≤ δ
  · have hDenom : D^5 ≤ (1 + s * (q / 2) * r)^5 := by
      apply pow_le_pow_left₀ hD.le
      exact add_le_add_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le) hr) _
    calc
      _ ≤ Cn * s^3 / (1 + s * (q / 2) * r)^5 :=
        halfDensityKernelDifference_near_bound hConv Φ w k hΦ hk hq hL hW hH hs hC₀ hC₁
          hLip hInv hw hwLip hDec₀ hDec₁ hx hy (hNear _ hr hsmall)
      _ ≤ Cn * s^3 / D^5 := div_le_div_of_nonneg_left (by positivity) (pow_pos hD _) hDenom
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (div_nonneg hf₀ ha.le)) (by positivity)) (pow_nonneg hD.le _)
  · obtain ⟨hu, hv⟩ := hFar x hx y hy (le_of_lt (lt_of_not_ge hsmall))
    calc
      _ ≤ 2 * W^2 * (C₀ * s^4 / (1 + s * a)^7) :=
        halfDensityKernelDifference_far_bound Φ w k hW hs ha.le hDec₀ (hw x hx) (hw y hy) hu hv
      _ = Cf * (s^4 / (1 + s * a)^7) := by unfold Cf; ring
      _ ≤ Cf * ((s^3 / a) / D^5) :=
        mul_le_mul_of_nonneg_left (far_decay_to_integrable_envelope hs ha hb.le hr hba) hf₀
      _ = (Cf / a) * s^3 / D^5 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hn₀) (by positivity)) (pow_nonneg hD.le _)

end Burnett.Microlocal.AtlasOverlapKernel
