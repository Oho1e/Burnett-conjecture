import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities
import Burnett.Geometry.ConnectionDifference

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology NNReal ENNReal

abbrev SmoothCoordinateComponents (g : CoordinateSpace → Tensor2) : Prop :=
  ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)

/-- The scalar cutoff fluctuation extended by zero. -/
def localizedMetricEntry (g g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (i j : Index) (x : CoordinateSpace) : ℝ := χ x * (g x i j - g₀ x i j)

private theorem localizedMetricEntry_smooth (g g₀ : CoordinateSpace → Tensor2)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (i j : Index) :
    ContDiff ℝ ∞ (localizedMetricEntry g g₀ χ i j) :=
  hχ.mul ((hg i j).sub (hg₀ i j))

/-- The original cutoff metric fluctuation on the Schwartz Fourier domain. -/
def localizedMetricSchwartz (g g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀) :
    ProjectionSchwartzMatrix := fun i j =>
  let f := localizedMetricEntry g g₀ χ i j
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) :=
    hc.mono' (by
      intro x hx
      apply subset_tsupport χ
      intro hz
      apply hx
      simp [f, localizedMetricEntry, hz])
  hc'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (localizedMetricEntry_smooth g g₀ hg hg₀ χ hχ i j))

private theorem matrix_entry_norm_le (H : Tensor2) (i j : Index) :
    ‖H i j‖ ≤ ‖H‖ := by
  have hi : ‖H i‖ ≤ ‖H‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg H)).1 le_rfl i
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg H)).1 hi j

private theorem norm_localizedMetricEntry_fderiv_le
    (g g₀ : CoordinateSpace → Tensor2)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (i j : Index)
    (A D B G : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hχA : ∀ x ∈ tsupport χ, ‖χ x‖ ≤ A)
    (hχD : ∀ x ∈ tsupport χ, ‖fderiv ℝ χ x‖ ≤ D)
    (hgG : ∀ x ∈ tsupport χ, ‖g x i j - g₀ x i j‖ ≤ G)
    (hgB : ∀ x ∈ tsupport χ,
      ‖fderiv ℝ (fun y => g y i j - g₀ y i j) x‖ ≤ B)
    (x : CoordinateSpace) :
    ‖fderiv ℝ (localizedMetricEntry g g₀ χ i j) x‖ ≤ A * B + D * G := by
  by_cases hx : x ∈ tsupport χ
  · let f := fun x => g x i j - g₀ x i j
    have hdf : Differentiable ℝ f := ((hg i j).sub (hg₀ i j)).differentiable (by simp)
    change ‖fderiv ℝ (fun y => χ y * f y) x‖ ≤ _
    rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hdf x)]
    calc
      _ ≤ ‖χ x • fderiv ℝ f x‖ + ‖f x • fderiv ℝ χ x‖ := norm_add_le _ _
      _ ≤ A * B + G * D := by
        simp only [norm_smul]
        exact add_le_add
          (mul_le_mul (hχA x hx) (hgB x hx) (norm_nonneg _) hA)
          (mul_le_mul (hgG x hx) (hχD x hx) (norm_nonneg _) hG)
      _ = _ := by ring
  · have hzero : fderiv ℝ (localizedMetricEntry g g₀ χ i j) x = 0 := by
      by_contra hn
      have hsup : Function.support (localizedMetricEntry g g₀ χ i j) ⊆ Function.support χ := by
        intro y hy
        by_contra h
        have hχ0 : χ y = 0 := Function.notMem_support.mp h
        exact hy (by simp [localizedMetricEntry, hχ0])
      exact hx (closure_mono hsup (support_fderiv_subset ℝ hn))
    rw [hzero, norm_zero]
    positivity

/-- The original cutoff field has one Lipschitz constant for all components
and tends to zero uniformly on the whole coordinate space. -/
theorem localizedMetricSchwartz_uniform_inputs
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (B : ℝ≥0) (hDeriv : ∀ n i j x, x ∈ tsupport χ →
      ‖fderiv ℝ (fun y => g n y i j - g₀ y i j) x‖ ≤ (B : ℝ)) :
    let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
    ∃ L : ℝ≥0, (∀ n i j, LipschitzWith L (z n i j : CoordinateSpace → ℂ)) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x i j, ‖z n i j x‖ < ε) := by
  let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
  obtain ⟨a, ha⟩ := hc.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨d, hd⟩ := hc.exists_bound_of_continuousOn
    (hχ.continuous_fderiv (by simp)).continuousOn
  let A := max a 0
  let D := max d 0
  have hA : 0 ≤ A := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  have hχA : ∀ x ∈ tsupport χ, ‖χ x‖ ≤ A := fun x hx => (ha x hx).trans (le_max_left _ _)
  have hχD : ∀ x ∈ tsupport χ, ‖fderiv ℝ χ x‖ ≤ D :=
    fun x hx => (hd x hx).trans (le_max_left _ _)
  have hDiffCont (n : ℕ) : Continuous (fun x => g n x - g₀ x) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      (hg n i j).continuous.sub (hg₀ i j).continuous
  choose C hC using fun n => hc.exists_bound_of_continuousOn (hDiffCont n).continuousOn
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.mp hConv 1 zero_lt_one)
  let G := 1 + ∑ n ∈ Finset.range N, max (C n) 0
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hBound (n : ℕ) (x : CoordinateSpace) (hx : x ∈ tsupport χ) : ‖g n x - g₀ x‖ ≤ G := by
    by_cases hn : N ≤ n
    · have ht := hN n hn x hx
      rw [dist_comm, dist_eq_norm] at ht
      exact ht.le.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => le_max_right _ _))
    · have hn' : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
      exact (hC n x hx).trans ((le_max_left _ _).trans
        ((Finset.single_le_sum (f := fun n => max (C n) 0)
          (fun k _ => le_max_right _ _) hn').trans
          (le_add_of_nonneg_left zero_le_one)))
  let L : ℝ≥0 := ⟨A*(B : ℝ) + D*G, by positivity⟩
  have hL (n : ℕ) (i j : Index) : LipschitzWith L (z n i j : CoordinateSpace → ℂ) := by
    let f := localizedMetricEntry (g n) g₀ χ i j
    have hf : Differentiable ℝ f := (hχ.mul ((hg n i j).sub (hg₀ i j))).differentiable (by simp)
    have hl : LipschitzWith L f := by
      apply lipschitzWith_of_nnnorm_fderiv_le hf
      intro x
      change ‖fderiv ℝ f x‖ ≤ A*(B : ℝ) + D*G
      exact norm_localizedMetricEntry_fderiv_le (g n) g₀ (hg n) hg₀ χ hχ i j A D B G hA hD
        B.coe_nonneg hG hχA hχD (fun y hy => (matrix_entry_norm_le _ i j).trans (hBound n y hy))
        (fun y hy => hDeriv n i j y hy) x
    simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hl
  have hSmall : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x i j, ‖z n i j x‖ < ε := by
    intro ε hε
    let r := ε / (A+1)
    have hA₁ : 0 < A+1 := by positivity
    have hr : 0 < r := div_pos hε hA₁
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv r hr] with n hn x i j
    change ‖(localizedMetricEntry (g n) g₀ χ i j x : ℂ)‖ < ε
    rw [Complex.norm_real, localizedMetricEntry, norm_mul]
    by_cases hx : x ∈ tsupport χ
    · have ht := hn x hx
      rw [dist_comm, dist_eq_norm] at ht
      have he := (matrix_entry_norm_le (g n x - g₀ x) i j).trans_lt ht
      calc
        _ ≤ (A+1) * ‖g n x i j - g₀ x i j‖ :=
          mul_le_mul_of_nonneg_right ((hχA x hx).trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _)
        _ < (A+1) * r := mul_lt_mul_of_pos_left he hA₁
        _ = ε := by dsimp only [r]; field_simp
    · have hz : χ x = 0 := Function.notMem_support.mp fun hy => hx (subset_tsupport χ hy)
      simpa only [hz, norm_zero, zero_mul] using hε
  exact ⟨L, hL, hSmall⟩

/-- All components use the support of the same spatial cutoff. -/
theorem localizedMetricSchwartz_tsupport_subset
    (g g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
    (i j : Index) :
    tsupport (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀ i j : CoordinateSpace → ℂ) ⊆
      tsupport χ := by
  apply closure_mono
  intro x hx
  by_contra h
  have hz : χ x = 0 := Function.notMem_support.mp h
  apply hx
  change (localizedMetricEntry g g₀ χ i j x : ℂ) = 0
  simp [localizedMetricEntry, hz]

end Burnett.P01
