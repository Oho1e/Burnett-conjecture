import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierLimit
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Joint angular symbols give continuous families of genuine annular Schwartz kernels. -/
set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 3600000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Set Filter Function Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff Topology

private theorem continuous_frequency_iteratedFDeriv {p : E × E → ℂ}
    (hp : ContDiff ℝ ∞ p) (n : ℕ) :
    Continuous (fun z : E × E => iteratedFDeriv ℝ n (fun ζ => p (z.1, ζ)) z.2) := by
  let A : E →L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hEq (z : E × E) : iteratedFDeriv ℝ n (fun ζ => p (z.1, ζ)) z.2 =
      (iteratedFDeriv ℝ n p z).compContinuousLinearMap (fun _ => A) := by
    let q (w : E × E) := p (w + (z.1, 0))
    have hq : ContDiff ℝ ∞ q := hp.comp (contDiff_id.add contDiff_const)
    have hQA : q ∘ A = fun ζ => p (z.1, ζ) := by
      funext ζ
      simp [q, A]
    have hAdd : iteratedFDeriv ℝ n q (A z.2) = iteratedFDeriv ℝ n p z := by
      change iteratedFDeriv ℝ n (fun w => p (w + (z.1, 0))) (0, z.2) = _
      rw [iteratedFDeriv_comp_add_right]
      simp
    rw [← hQA, A.iteratedFDeriv_comp_right hq z.2 hn, hAdd]
  simp_rw [hEq]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => A)).continuous.comp
    (hp.continuous_iteratedFDeriv hn)

private theorem continuous_compactFrequency_schwartz
    (f : E → SchwartzMap E ℂ) (hf : ContDiff ℝ ∞ (fun z : E × E => f z.1 z.2))
    (hSupp : ∀ x, tsupport (f x : E → ℂ) ⊆ Metric.closedBall (0 : E) 4) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto f (𝓝 x) (𝓝 (f x))
  rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  let U := Metric.closedBall x 1
  let V := Metric.closedBall (0 : E) 4
  let D (x ξ : E) := iteratedFDeriv ℝ n (f x : E → ℂ) ξ
  let B : ℝ := 4 ^ k
  have hB : 0 < B := by positivity
  have hDU : UniformContinuousOn ↿D (U ×ˢ V) :=
    ((isCompact_closedBall x 1).prod (isCompact_closedBall (0 : E) 4))
      |>.uniformContinuousOn_of_continuous
        (continuous_frequency_iteratedFDeriv hf n).continuousOn
  have hx : x ∈ U := Metric.mem_closedBall_self (by norm_num)
  have hLocal : 𝓝[U] x = 𝓝 x :=
    nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds x (by norm_num))
  have hEvent := Metric.tendstoUniformlyOn_iff.mp (hDU.tendstoUniformlyOn hx) (ε / (2 * B))
    (div_pos hε (mul_pos (by norm_num) hB))
  rw [hLocal] at hEvent
  filter_upwards [hEvent] with y hy
  change SchwartzMap.seminorm ℝ k n (f y - f x) < ε
  have hNorm : SchwartzMap.seminorm ℝ k n (f y - f x) ≤ ε / 2 := by
    apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
    intro ξ
    by_cases hξ : ξ ∈ V
    · have hdist : ‖D y ξ - D x ξ‖ ≤ ε / (2 * B) := by
        have h := (hy ξ hξ).le
        rw [dist_comm, dist_eq_norm] at h
        exact h
      have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      have hyN : ContDiffAt ℝ n (f y : E → ℂ) ξ := ((f y).smooth'.contDiffAt (x := ξ)).of_le hn
      have hxN : ContDiffAt ℝ n (-(f x : E → ℂ)) ξ := (((f x).smooth'.contDiffAt (x := ξ)).of_le hn).neg
      have hEq : (fun z => f y z - f x z) = (f y : E → ℂ) + -(f x : E → ℂ) :=
        funext fun z => sub_eq_add_neg _ _
      have hDeriv : iteratedFDeriv ℝ n ((f y : E → ℂ) + -(f x : E → ℂ)) ξ = D y ξ - D x ξ := by
        rw [iteratedFDeriv_add_apply hyN hxN, iteratedFDeriv_neg_apply, ← sub_eq_add_neg]
      change ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f y z - f x z) ξ‖ ≤ ε / 2
      rw [hEq, hDeriv]
      have hξ₀ : ‖ξ‖ ≤ 4 := by simpa only [V, Metric.mem_closedBall, dist_zero_right] using hξ
      calc
        _ ≤ B * (ε / (2 * B)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hξ₀ k) hdist (norm_nonneg _) hB.le
        _ = ε / 2 := by field_simp
    · have hts : tsupport ((f y - f x : SchwartzMap E ℂ) : E → ℂ) ⊆ V := by
        apply closure_minimal _ Metric.isClosed_closedBall
        intro z hz
        by_contra hzV
        exact hz (by
          change f y z - f x z = 0
          rw [image_eq_zero_of_notMem_tsupport (fun hzS => hzV (hSupp y hzS)),
            image_eq_zero_of_notMem_tsupport (fun hzS => hzV (hSupp x hzS)), sub_self])
      have hZero : iteratedFDeriv ℝ n ((f y - f x : SchwartzMap E ℂ) : E → ℂ) ξ = 0 := by
        by_contra hh
        exact hξ (hts (support_iteratedFDeriv_subset n hh))
      rw [hZero, norm_zero, mul_zero]
      positivity
  exact hNorm.trans_lt (by linarith)

private theorem contDiff_annularAngularFamily (a : E → BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E))) :
    ContDiff ℝ ∞ (fun z : E × E => annularSymbol (a z.1) z.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.2 = 0
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hB : ∀ᶠ w : E × E in 𝓝 z, ‖w.2‖ < 1 :=
      continuous_snd.norm.tendsto z |>.eventually (Iio_mem_nhds (by simp [hz]))
    filter_upwards [hB] with w hw
    simp [annularSymbol, annulus_eq_zero_near _ hw.le]
  · have hOpen : IsOpen ((univ : Set E) ×ˢ ({0}ᶜ : Set E)) :=
      isOpen_univ.prod isOpen_compl_singleton
    exact ((Complex.ofRealCLM.contDiff.comp (annulus_contDiff.comp contDiff_snd)).contDiffAt).mul
      (ha.contDiffAt (hOpen.mem_nhds ⟨mem_univ _, hz⟩))

/-- The actual inverse annular profile varies continuously in all Schwartz seminorms
as the position parameter changes. -/
theorem continuous_inverseAnnularSchwartz_family (a : E → BoundedSymbol E)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (haSlice : ∀ x, ContDiffOn ℝ ∞ (a x : E → ℂ) ({0}ᶜ : Set E)) :
    Continuous (fun x => inverseAnnularSchwartz (a x) (haSlice x)) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).symm.continuous.comp
  apply continuous_compactFrequency_schwartz
  · exact contDiff_annularAngularFamily a ha
  · intro x
    apply closure_minimal _ Metric.isClosed_closedBall
    intro ξ hξ
    by_contra hh
    have hFar : 4 ≤ ‖ξ‖ := (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hh)).le
    exact hξ (by change annularSymbol (a x) ξ = 0; simp [annularSymbol, annulus_eq_zero_far _ hFar])

end Burnett.Microlocal.AtlasOverlapKernel
