import Burnett.Analysis.Microlocal.Overlap.KernelRemainder
import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open Set Burnett.Fourier Burnett.Geometry Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open scoped BigOperators ContDiff Manifold

private theorem schwartz_derivative_decay (p : SchwartzMap E ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, (1 + ‖z‖)^7 * ‖iteratedFDeriv ℝ n p z‖ ≤ C := by
  let C₀ := SchwartzMap.seminorm ℝ 0 n p
  let C₇ := SchwartzMap.seminorm ℝ 7 n p
  let C := max C₀ C₇
  have hC : 0 ≤ C := (apply_nonneg _ _).trans (le_max_left _ _)
  refine ⟨(2 : ℝ)^7 * C, by positivity, fun z => ?_⟩
  let r := ‖z‖
  let d := ‖iteratedFDeriv ℝ n (p : E → ℂ) z‖
  have hr : 0 ≤ r := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have h₀ : d ≤ C := (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ p n z).trans (le_max_left _ _)
  have h₇ : r^7 * d ≤ C := (SchwartzMap.le_seminorm ℝ 7 n p z).trans (le_max_right _ _)
  change (1 + r)^7 * d ≤ _
  by_cases h : r ≤ 1
  · exact mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith) _) h₀ hd (by positivity)
  · calc
      (1 + r)^7 * d ≤ (2 * r)^7 * d := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by linarith) (by linarith [lt_of_not_ge h]) _) hd
      _ = (2 : ℝ)^7 * (r^7 * d) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left h₇ (by positivity)

private theorem fderiv_norm_le_iterated (p : E → ℂ) (z : E) :
    ‖fderiv ℝ p z‖ ≤ ‖iteratedFDeriv ℝ 1 p z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  let args : Fin 1 → E := fun _ => v
  calc
    ‖fderiv ℝ p z v‖ = ‖iteratedFDeriv ℝ 1 p z args‖ := by
      rw [iteratedFDeriv_one_apply]
    _ ≤ ‖iteratedFDeriv ℝ 1 p z‖ * ∏ i, ‖args i‖ :=
      (iteratedFDeriv ℝ 1 p z).le_opNorm args
    _ = _ := by simp [args]

/-- Uniform size and first derivative decay for the actual annular inverse
Fourier kernels. The constants depend on the one undilated Schwartz profile. -/
theorem shellKernel_decay_bounds (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ (j : ℕ) (z : E),
      let s := dyadicScale j
      (1 + s * ‖z‖)^7 * ‖shellKernel m hm j z‖ ≤ C₀ * s^4 ∧
      (1 + s * ‖z‖)^7 * ‖fderiv ℝ (shellKernel m hm j) z‖ ≤ C₁ * s^5 := by
  let p := inverseAnnularSchwartz m hm
  obtain ⟨C₀, hC₀, h₀⟩ := schwartz_derivative_decay p 0
  obtain ⟨C₁, hC₁, h₁⟩ := schwartz_derivative_decay p 1
  refine ⟨C₀, C₁, hC₀, hC₁, fun j z => ?_⟩
  let s := dyadicScale j
  have hs : 0 < s := by unfold s dyadicScale; positivity
  have hnorm : ‖s • z‖ = s * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
  have h₀' : (1 + s * ‖z‖)^7 * ‖p (s • z)‖ ≤ C₀ := by
    simpa only [hnorm, norm_iteratedFDeriv_zero] using h₀ (s • z)
  have h₁' : (1 + s * ‖z‖)^7 * ‖fderiv ℝ (p : E → ℂ) (s • z)‖ ≤ C₁ := by
    calc
      _ ≤ (1 + s * ‖z‖)^7 * ‖iteratedFDeriv ℝ 1 (p : E → ℂ) (s • z)‖ :=
        mul_le_mul_of_nonneg_left (fderiv_norm_le_iterated _ _) (by positivity)
      _ ≤ _ := by simpa only [hnorm] using h₁ (s • z)
  change (1 + s * ‖z‖)^7 * ‖s^4 • p (s • z)‖ ≤ C₀ * s^4 ∧ _
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hs.le 4)]
    calc
      _ = s^4 * ((1 + s * ‖z‖)^7 * ‖p (s • z)‖) := by ring
      _ ≤ C₀ * s^4 := by
        rw [mul_comm C₀]
        exact mul_le_mul_of_nonneg_left h₀' (pow_nonneg hs.le _)
  · rw [(shellKernel_hasFDerivAt m hm j z).fderiv, norm_smul,
      Real.norm_of_nonneg (pow_nonneg hs.le 5)]
    change (1 + s * ‖z‖)^7 * (s^5 * ‖fderiv ℝ (p : E → ℂ) (s • z)‖) ≤ C₁ * s^5
    calc
      _ = s^5 * ((1 + s * ‖z‖)^7 * ‖fderiv ℝ (p : E → ℂ) (s • z)‖) := by ring
      _ ≤ C₁ * s^5 := by
        rw [mul_comm C₁]
        exact mul_le_mul_of_nonneg_left h₁' (pow_nonneg hs.le _)

/-- The genuine near and far kernels of the fixed preferred-chart
transition admit bounds uniform over all dyadic shells. -/
theorem overlap_shellKernel_near_far_bounds
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c d : M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    ∃ q a δ₀ Cnear Cfar : ℝ, 0 < q ∧ 0 < a ∧ 0 < δ₀ ∧ 0 ≤ Cnear ∧ 0 ≤ Cfar ∧
      ∀ (j : ℕ) (x : E), x ∈ K → ∀ y ∈ K,
        let s := dyadicScale j
        let R := halfDensityKernelDifference Φ w (shellKernel m hm j) x y
        (‖x - y‖ ≤ δ₀ →
          ‖R‖ ≤ Cnear * s^3 / (1+s*q*‖x - y‖)^5) ∧
        (δ₀ ≤ ‖x - y‖ →
          ‖R‖ ≤ Cfar * s^4 / (1+s*a)^7) := by
  intro Φ w
  obtain ⟨q, L, W, H, δ₀, hq, hL, hW, hH, hδ, hNear, hΦ, hLip, hInv, hw, hwLip⟩ :=
    overlapKernel_geometry_bounds B hB hn c d K hK hKU hConv
  obtain ⟨a, ha, hFar⟩ := overlapFar_uniform_arguments c d K hK hKU hδ
  obtain ⟨C₀, C₁, hC₀, hC₁, hDecay⟩ := shellKernel_decay_bounds m hm
  refine ⟨q/2, a, δ₀, W * H * C₀ / (q/2) + W^2 * C₁ * L / (q/2)^2,
    2*W^2*C₀, half_pos hq, ha, hδ, by positivity, by positivity, ?_⟩
  intro j x hx y hy
  let s := dyadicScale j
  have hs : 0 < s := by unfold s dyadicScale; positivity
  have hk : Differentiable ℝ (shellKernel m hm j) := fun z =>
    (shellKernel_hasFDerivAt m hm j z).differentiableAt
  refine ⟨fun hnxy => ?_, fun hfxy => ?_⟩
  · exact halfDensityKernelDifference_near_bound hConv Φ w _ hΦ hk hq hL hW hH hs hC₀ hC₁
      hLip hInv hw hwLip (fun z => (hDecay j z).1) (fun z => (hDecay j z).2)
      hx hy (hNear _ (norm_nonneg _) hnxy)
  · obtain ⟨hu, hv⟩ := hFar x hx y hy hfxy
    calc
      _ ≤ 2*W^2*(C₀*s^4/(1+s*a)^7) :=
        halfDensityKernelDifference_far_bound Φ w _ hW hs ha.le
          (fun z => (hDecay j z).1) (hw x hx) (hw y hy) hu hv
      _ = _ := by ring

private theorem far_decay_to_integrable_envelope
    {s a b r : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : b*r ≤ a) :
    s^4 / (1+s*a)^7 ≤ (s^3 / a) / (1+s*b*r)^5 := by
  let A := 1+s*a
  let D := 1+s*b*r
  have hA : 0 < A := by dsimp only [A]; positivity
  have hA1 : 1 ≤ A := le_add_of_nonneg_right (mul_nonneg hs.le ha.le)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDA : D ≤ A := by
    simpa only [A, D, mul_assoc] using add_le_add_left (mul_le_mul_of_nonneg_left h hs.le) 1
  have hProd : (s*a) * D^5 ≤ A^7 := by
    calc
      _ ≤ A * A^5 := mul_le_mul (le_add_of_nonneg_left zero_le_one)
        (pow_le_pow_left₀ hD.le hDA 5) (pow_nonneg hD.le _) hA.le
      _ = A^6 := by ring
      _ ≤ A^7 := pow_le_pow_right₀ hA1 (by norm_num)
  have hRatio : (s*a)/A^7 ≤ 1/D^5 :=
    (div_le_div_iff₀ (pow_pos hA _) (pow_pos hD _)).2 (by simpa only [one_mul] using hProd)
  change s^4/A^7 ≤ (s^3/a)/D^5
  calc
    _ = (s^3/a)*((s*a)/A^7) := by field_simp [ha.ne', hA.ne']
    _ ≤ (s^3/a)*(1/D^5) := mul_le_mul_of_nonneg_left hRatio (by positivity)
    _ = _ := by ring

/-- One integrable radial profile dominates the pair of shell kernels on
the whole compact overlap. The scale in the amplitude is (s^3). -/
theorem overlap_shellKernel_uniform_envelope
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c d : M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (j : ℕ) (x : E), x ∈ K → ∀ y ∈ K,
      let s := dyadicScale j
      ‖halfDensityKernelDifference Φ w (shellKernel m hm j) x y‖ ≤
        C*s^3/(1+s*b*‖x-y‖)^5 := by
  intro Φ w
  obtain ⟨q, a, δ₀, Cnear, Cfar, hq, ha, _, hCnear, hCfar, hBounds⟩ :=
    overlap_shellKernel_near_far_bounds B hB hn c d K hK hKU hConv m hm
  let R := Metric.diam K + 1
  let b := min q (a/R)
  let C := Cnear + Cfar/a
  have hR : 0 < R := by dsimp only [R]; linarith [Metric.diam_nonneg (s := K)]
  have hb : 0 < b := lt_min hq (div_pos ha hR)
  have hC : 0 ≤ C := add_nonneg hCnear (div_nonneg hCfar ha.le)
  refine ⟨b, C, hb, hC, fun j x hx y hy => ?_⟩
  let s := dyadicScale j
  let r := ‖x-y‖
  let D := 1+s*b*r
  have hs : 0 < s := by unfold s dyadicScale; positivity
  have hr : 0 ≤ r := norm_nonneg _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hrR : r ≤ R := (by
    simpa only [r, dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded hx hy
      : r ≤ Metric.diam K).trans (le_add_of_nonneg_right zero_le_one)
  have hba : b*r ≤ a := calc
    _ ≤ b*R := mul_le_mul_of_nonneg_left hrR hb.le
    _ ≤ (a/R)*R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    _ = a := div_mul_cancel₀ a hR.ne'
  have hCnearC : Cnear ≤ C := le_add_of_nonneg_right (div_nonneg hCfar ha.le)
  have hCfarC : Cfar/a ≤ C := le_add_of_nonneg_left hCnear
  obtain ⟨hNear, hFar⟩ := hBounds j x hx y hy
  change ‖halfDensityKernelDifference Φ w (shellKernel m hm j) x y‖ ≤ C*s^3/D^5
  by_cases hsmall : r ≤ δ₀
  · have hDenom : D^5 ≤ (1+s*q*r)^5 := by
      apply pow_le_pow_left₀ hD.le
      exact add_le_add_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le) hr) _
    calc
      _ ≤ Cnear*s^3/(1+s*q*r)^5 := hNear hsmall
      _ ≤ Cnear*s^3/D^5 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hD _) hDenom
      _ ≤ C*s^3/D^5 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCnearC (by positivity)) (pow_nonneg hD.le _)
  · calc
      _ ≤ Cfar*s^4/(1+s*a)^7 := hFar (le_of_lt (lt_of_not_ge hsmall))
      _ = Cfar * (s^4/(1+s*a)^7) := by ring
      _ ≤ Cfar * ((s^3/a)/D^5) :=
        mul_le_mul_of_nonneg_left (far_decay_to_integrable_envelope hs ha hb.le hr hba) hCfar
      _ = (Cfar/a)*s^3/D^5 := by ring
      _ ≤ C*s^3/D^5 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCfarC (by positivity)) (pow_nonneg hD.le _)

end Burnett.Microlocal.OverlapKernel
