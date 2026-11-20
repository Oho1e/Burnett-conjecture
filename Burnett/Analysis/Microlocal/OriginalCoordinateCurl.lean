import Burnett.Analysis.Microlocal.BesselLocalization
import Burnett.Analysis.LocalWeakDerivative
import Burnett.Analysis.CompactRellich
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Burnett.Analysis.GeometricHminusBoundedForcing
import Burnett.Geometry.OriginalAdmissibleLocalControl

noncomputable section

namespace Burnett.F05.CoordinateCurl

open Set Filter MeasureTheory
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet
open Burnett.Analysis.LocalWeakDerivative hiding Space

abbrev Axis := Fin 4
abbrev TensorPair := Axis × Axis
abbrev JetIndex := Axis × TensorPair

def axis (i : Axis) : Space := EuclideanSpace.single i 1

def localizedGradient (χ : D) (H : Space → ℝ) (i : Axis) (x : Space) : ℝ :=
  (χ : Space → ℝ) x * directional i H x

private theorem directional_smoothOn {U : Set Space} (hU : IsOpen U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (i : Axis) : ContDiffOn ℝ ∞ (directional i H) U :=
  (hH.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem localizedGradient_smooth {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (i : Axis) :
    ContDiff ℝ ∞ (localizedGradient χ H i) :=
  contDiff_test_mul_local hU (test_smooth χ) hχ (directional_smoothOn hU hH i)

theorem localizedGradient_tsupport (χ : D) (H : Space → ℝ) (i : Axis) :
    tsupport (localizedGradient χ H i) ⊆ tsupport (χ : Space → ℝ) :=
  tsupport_mul_subset_left

def localizedGradientTest {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (i : Axis) : D :=
  ⟨localizedGradient χ H i, localizedGradient_smooth hU χ hχ hH i, (test_compactSupport χ).mul_right⟩

def derivativeTest (χ : D) (j : Axis) : D :=
  ⟨directional j χ, ((test_smooth χ).fderiv_right (by simp)).clm_apply contDiff_const,
    directional_compactSupport j χ⟩

theorem derivativeTest_tsupport (χ : D) (j : Axis) :
    tsupport (derivativeTest χ j : Space → ℝ) ⊆ tsupport (χ : Space → ℝ) :=
  tsupport_directional_subset (χ : Space → ℝ) (axis j)

private theorem directional_directional {H : Space → ℝ} {x : Space}
    (hH : ContDiffAt ℝ ∞ H x) (j m : Axis) :
    directional j (directional m H) x = fderiv ℝ (fderiv ℝ H) x (axis j) (axis m) := by
  unfold directional axis
  have h2 : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by
    norm_num
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  rw [fderiv_clm_apply ((hH.fderiv_right h2).differentiableAt le_rfl)
    (differentiableAt_const (EuclideanSpace.single m (1 : ℝ)))]
  simp

private theorem directional_directional_comm {H : Space → ℝ} {x : Space}
    (hH : ContDiffAt ℝ ∞ H x) (j m : Axis) :
    directional j (directional m H) x = directional m (directional j H) x := by
  rw [directional_directional hH, directional_directional hH]
  apply hH.isSymmSndFDerivAt _ (axis j) (axis m)
  norm_num
  change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

/-- The normalized zero extensions of the localized derivatives have the genuine
coordinate curl given by derivatives of the same cutoff. -/
theorem localizedGradient_curl {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (j m : Axis) (x : Space) :
    directional j (localizedGradient χ H m) x - directional m (localizedGradient χ H j) x =
      directional j χ x * directional m H x - directional m χ x * directional j H x := by
  have h1 : directional j (localizedGradient χ H m) x =
      directional j χ x * directional m H x +
        (χ : Space → ℝ) x * directional j (directional m H) x :=
    fderiv_test_mul_local hU (test_smooth χ) hχ (directional_smoothOn hU hH m) (axis j) x
  have h2 : directional m (localizedGradient χ H j) x =
      directional m χ x * directional j H x +
        (χ : Space → ℝ) x * directional m (directional j H) x :=
    fderiv_test_mul_local hU (test_smooth χ) hχ (directional_smoothOn hU hH j) (axis m) x
  rw [h1, h2]
  by_cases hx : x ∈ U
  · rw [directional_directional_comm (hH.contDiffAt (hU.mem_nhds hx)) j m]
    ring
  · have h0 : (χ : Space → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχ h)
    simp [h0]

/-- Compactly supported real curl, as the difference of the two actual cutoff-derivative products. -/
def localizedCurlTest {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (j m : Axis) : D :=
  localizedGradientTest hU (derivativeTest χ j) ((derivativeTest_tsupport χ j).trans hχ) hH m -
    localizedGradientTest hU (derivativeTest χ m) ((derivativeTest_tsupport χ m).trans hχ) hH j

theorem localizedCurlTest_eq_curl {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (j m : Axis) (x : Space) :
    (localizedCurlTest hU χ hχ hH j m : Space → ℝ) x =
      directional j (localizedGradient χ H m) x - directional m (localizedGradient χ H j) x :=
  (localizedGradient_curl hU χ hχ hH j m x).symm

theorem localizedCurlTest_zero_outside {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (j m : Axis) {x : Space}
    (hx : x ∉ tsupport (χ : Space → ℝ)) :
    (localizedCurlTest hU χ hχ hH j m : Space → ℝ) x = 0 := by
  have hj : (derivativeTest χ j : Space → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (derivativeTest_tsupport χ j h)
  have hm : (derivativeTest χ m : Space → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (derivativeTest_tsupport χ m h)
  change (derivativeTest χ j : Space → ℝ) x * directional m H x -
    (derivativeTest χ m : Space → ℝ) x * directional j H x = 0
  rw [hj, hm, zero_mul, zero_mul, sub_self]

theorem exists_outerCutoff_on_tsupport (χ : D) :
    ∃ θ : D, ∀ x ∈ tsupport (χ : Space → ℝ), (θ : Space → ℝ) x = 1 := by
  obtain ⟨R, hR, hχR⟩ := (test_compactSupport χ).isBounded.subset_closedBall_lt 0 (0 : Space)
  let θ : ContDiffBump (0 : Space) := ⟨R, R + 1, hR, by linarith⟩
  exact ⟨⟨θ, θ.contDiff, θ.hasCompactSupport⟩, fun x hx => θ.one_of_mem_closedBall (hχR hx)⟩

end Burnett.F05.CoordinateCurl

noncomputable section

namespace Burnett.F05.CoordinateCurl

open Set Filter MeasureTheory
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet
open Burnett.Analysis.LocalWeakDerivative hiding Space
open Burnett.Analysis.HminusWeightedDual

theorem localizedGradientTest_L2_bound {U : Set Space} (hU : IsOpen U)
    (ψ : D) (hψ : tsupport (ψ : Space → ℝ) ⊆ U)
    {H : Space → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (i : Axis) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ x ∈ tsupport (ψ : Space → ℝ), ‖directional i H x‖ ≤ B) :
    ‖valueLp (localizedGradientTest hU ψ hψ hH i)‖ ≤ B * ‖valueLp ψ‖ := by
  let f := localizedGradientTest hU ψ hψ hH i
  have hscaled := (test_memLp ψ).const_smul B
  have hpoint (x : Space) : ‖(f : Space → ℝ) x‖ ≤ ‖(B • (ψ : Space → ℝ)) x‖ := by
    change ‖(ψ : Space → ℝ) x * directional i H x‖ ≤ ‖B * (ψ : Space → ℝ) x‖
    by_cases hx : x ∈ tsupport (ψ : Space → ℝ)
    · rw [norm_mul, norm_mul, Real.norm_eq_abs B, abs_of_nonneg hB, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hD x hx) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  have hLt : ‖valueLp f‖ ≤ ‖hscaled.toLp (B • (ψ : Space → ℝ))‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(test_memLp f).coeFn_toLp, hscaled.coeFn_toLp] with x hx hy
    change ‖((test_memLp f).toLp (f : Space → ℝ)) x‖ ≤
      ‖(hscaled.toLp (B • (ψ : Space → ℝ))) x‖
    rw [hx, hy]
    exact hpoint x
  change ‖valueLp f‖ ≤ ‖B • valueLp ψ‖ at hLt
  simpa only [norm_smul, Real.norm_eq_abs B, abs_of_nonneg hB] using hLt

theorem localizedGradientTest_test_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (ψ : D) (hψ : tsupport (ψ : Space → ℝ) ⊆ U)
    (H : ℕ → Space → ℝ) (hH : ∀ n, ContDiffOn ℝ ∞ (H n) U)
    (h0 : ∀ K : Set Space, IsCompact K → K ⊆ U → TendstoUniformlyOn H (fun _ => 0) atTop K)
    (i : Axis) (φ : D) :
    Tendsto (fun n => ∫ x, (localizedGradientTest hU ψ hψ (hH n) i : Space → ℝ) x *
      (φ : Space → ℝ) x) atTop (𝓝 0) := by
  have ht := integral_test_directional_tendsto_zero hU ((test_smooth ψ).mul (test_smooth φ))
    (test_compactSupport ψ).mul_right (tsupport_mul_subset_left.trans hψ) hH h0 (axis i)
  exact ht.congr fun n => by
    apply integral_congr_ae
    filter_upwards [] with x
    change ((ψ : Space → ℝ) x * (φ : Space → ℝ) x) * directional i (H n) x =
      ((ψ : Space → ℝ) x * directional i (H n) x) * (φ : Space → ℝ) x
    ring

private theorem valueLp_sub (f g : D) : valueLp (f - g) = valueLp f - valueLp g := by
  change ((test_memLp f).sub (test_memLp g)).toLp ((f : Space → ℝ) - (g : Space → ℝ)) = _
  exact MemLp.toLp_sub (test_memLp f) (test_memLp g)

theorem localizedCurlTest_L2_bound {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    {H : Space → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (j m : Axis) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ i x, x ∈ tsupport (χ : Space → ℝ) → ‖directional i H x‖ ≤ B) :
    ‖valueLp (localizedCurlTest hU χ hχ hH j m)‖ ≤
      B * ‖valueLp (derivativeTest χ j)‖ + B * ‖valueLp (derivativeTest χ m)‖ := by
  unfold localizedCurlTest
  rw [valueLp_sub]
  apply (norm_sub_le _ _).trans
  exact add_le_add
    (localizedGradientTest_L2_bound hU (derivativeTest χ j) _ hH m hB
      (fun x hx => hD m x (derivativeTest_tsupport χ j hx)))
    (localizedGradientTest_L2_bound hU (derivativeTest χ m) _ hH j hB
      (fun x hx => hD j x (derivativeTest_tsupport χ m hx)))

theorem localizedCurlTest_test_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → Space → ℝ) (hH : ∀ n, ContDiffOn ℝ ∞ (H n) U)
    (h0 : ∀ K : Set Space, IsCompact K → K ⊆ U → TendstoUniformlyOn H (fun _ => 0) atTop K)
    (j m : Axis) (φ : D) :
    Tendsto (fun n => ∫ x, (localizedCurlTest hU χ hχ (hH n) j m : Space → ℝ) x *
      (φ : Space → ℝ) x) atTop (𝓝 0) := by
  let f n := localizedGradientTest hU (derivativeTest χ j) ((derivativeTest_tsupport χ j).trans hχ) (hH n) m
  let g n := localizedGradientTest hU (derivativeTest χ m) ((derivativeTest_tsupport χ m).trans hχ) (hH n) j
  have hF : Tendsto (fun n => ∫ x, (f n : Space → ℝ) x * (φ : Space → ℝ) x) atTop (𝓝 0) :=
    localizedGradientTest_test_tendsto_zero hU _ _ H hH h0 m φ
  have hG : Tendsto (fun n => ∫ x, (g n : Space → ℝ) x * (φ : Space → ℝ) x) atTop (𝓝 0) :=
    localizedGradientTest_test_tendsto_zero hU _ _ H hH h0 j φ
  rw [← sub_zero (0 : ℝ)]
  apply (hF.sub hG).congr
  intro n
  have hf : Integrable (fun x => (f n : Space → ℝ) x * (φ : Space → ℝ) x) :=
    ((test_smooth (f n)).continuous.mul (test_smooth φ).continuous).integrable_of_hasCompactSupport
      (test_compactSupport (f n)).mul_right
  have hg : Integrable (fun x => (g n : Space → ℝ) x * (φ : Space → ℝ) x) :=
    ((test_smooth (g n)).continuous.mul (test_smooth φ).continuous).integrable_of_hasCompactSupport
      (test_compactSupport (g n)).mul_right
  rw [← integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [] with x
  change (f n : Space → ℝ) x * (φ : Space → ℝ) x -
      (g n : Space → ℝ) x * (φ : Space → ℝ) x =
    ((f n : Space → ℝ) x - (g n : Space → ℝ) x) * (φ : Space → ℝ) x
  ring

theorem localizedCurlTest_negativeEnergy_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → Space → ℝ) (hH : ∀ n, ContDiffOn ℝ ∞ (H n) U)
    (h0 : ∀ K : Set Space, IsCompact K → K ⊆ U → TendstoUniformlyOn H (fun _ => 0) atTop K)
    (j m : Axis) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n i x, x ∈ tsupport (χ : Space → ℝ) → ‖directional i (H n) x‖ ≤ B) :
    Tendsto (fun n => negativeEnergy (complexTest (localizedCurlTest hU χ hχ (hH n) j m)))
      atTop (𝓝 0) := by
  let F n := localizedCurlTest hU χ hχ (hH n) j m
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport χ
  have hθ' : ∀ n x, (F n : Space → ℝ) x ≠ 0 → (θ : Space → ℝ) x = 1 := by
    intro n x hx
    exact hθ x (by
      by_contra h
      exact hx (localizedCurlTest_zero_outside hU χ hχ (hH n) j m h))
  have ht := Burnett.Analysis.CompactRellich.negativeEnergy_tendsto_zero_of_commonCutoff
    (fun n => test_smooth (F n)) (fun n => test_memLp (F n)) θ hθ'
    (fun n => localizedCurlTest_L2_bound hU χ hχ (hH n) j m hB (hD n))
    (localizedCurlTest_test_tendsto_zero hU χ hχ H hH h0 j m)
  apply ht.congr
  intro n
  congr 1

end Burnett.F05.CoordinateCurl

noncomputable section

namespace Burnett.F05.CoordinateCurl

open Set Filter MeasureTheory Burnett.Fourier
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet
open Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.BesselLocalization

/-- The actual Schwartz complexification of the localized real coordinate gradient. -/
def gradientSchwartz {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (i : Axis) : SchwartzMap Space ℂ :=
  complexTest (localizedGradientTest hU χ hχ hH i)

theorem gradientSchwartz_apply {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (i : Axis) (x : Space) :
    gradientSchwartz hU χ hχ hH i x = (localizedGradient χ H i x : ℂ) := rfl

theorem angularDirection_axis (i : Axis) (ξ : Space) :
    angularDirection (axis i) ξ = Complex.I * ((ξ i / ‖ξ‖ : ℝ) : ℂ) := by
  simp [angularDirection, axis, EuclideanSpace.inner_single_right]

theorem curlSchwartz_eq_directional_sub {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U) {H : Space → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (j m : Axis) :
    complexTest (localizedCurlTest hU χ hχ hH j m) =
      SchwartzMap.pderivCLM ℂ (axis j) (gradientSchwartz hU χ hχ hH m) -
        SchwartzMap.pderivCLM ℂ (axis m) (gradientSchwartz hU χ hχ hH j) := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.sub_apply]
  change ((localizedCurlTest hU χ hχ hH j m : Space → ℝ) x : ℂ) =
    SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1)
      (complexTest (localizedGradientTest hU χ hχ hH m)) x -
    SchwartzMap.pderivCLM ℂ (EuclideanSpace.single m 1)
      (complexTest (localizedGradientTest hU χ hχ hH j)) x
  rw [complexTest_pderiv, complexTest_pderiv, ← Complex.ofReal_sub]
  exact congrArg Complex.ofReal (localizedCurlTest_eq_curl hU χ hχ hH j m x)

theorem bessel_gradient_pderiv_minus_angular_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → Space → ℝ) (hH : ∀ n, ContDiffOn ℝ ∞ (H n) U)
    (h0 : ∀ K : Set Space, IsCompact K → K ⊆ U → TendstoUniformlyOn H (fun _ => 0) atTop K)
    (m : Axis) (v : Space) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n x, x ∈ tsupport (χ : Space → ℝ) → ‖directional m (H n) x‖ ≤ B) :
    Tendsto (fun n =>
      fourierMultiplier besselSymbol
        ((SchwartzMap.pderivCLM ℂ v (gradientSchwartz hU χ hχ (hH n) m)).toLp 2 volume) -
      fourierMultiplier (angularDirectionSymbol v) ((gradientSchwartz hU χ hχ (hH n) m).toLp 2 volume))
      atTop (𝓝 0) := by
  let f n := localizedGradientTest hU χ hχ (hH n) m
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport χ
  have hloc : ∀ n x, (f n : Space → ℝ) x ≠ 0 → (θ : Space → ℝ) x = 1 := by
    intro n x hx
    exact hθ x (localizedGradient_tsupport χ (H n) m (subset_tsupport (f n : Space → ℝ) hx))
  have hS (n : ℕ) : Burnett.Analysis.LocalHminusFourier.sourceSchwartz (test_smooth (f n)) θ (hloc n) =
        gradientSchwartz hU χ hχ (hH n) m :=
    SchwartzMap.ext fun _ => rfl
  have ht := bessel_pderiv_minus_angular_tendsto_zero v (fun n => (f n : Space → ℝ))
    (fun n => test_smooth (f n)) (fun n => test_memLp (f n)) θ hloc
    (B * ‖valueLp χ‖)
    (fun n => localizedGradientTest_L2_bound hU χ hχ (hH n) m hB (hD n))
    (localizedGradientTest_test_tendsto_zero hU χ hχ H hH h0 m)
  simpa only [hS] using ht

def angularCurl (j m : Axis) (u : Axis → SchwartzMap Space ℂ) : ComplexL2 Space :=
  fourierMultiplier (angularDirectionSymbol (axis j)) ((u m).toLp 2 volume) -
    fourierMultiplier (angularDirectionSymbol (axis m)) ((u j).toLp 2 volume)

/-- The Euclidean angular principal curl vanishes strongly on the actual
localized gradient, for every fixed pair of directions. -/
theorem angularCurl_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → Space → ℝ) (hH : ∀ n, ContDiffOn ℝ ∞ (H n) U)
    (h0 : ∀ K : Set Space, IsCompact K → K ⊆ U → TendstoUniformlyOn H (fun _ => 0) atTop K)
    (j m : Axis) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n i x, x ∈ tsupport (χ : Space → ℝ) → ‖directional i (H n) x‖ ≤ B) :
    Tendsto (fun n => angularCurl j m (gradientSchwartz hU χ hχ (hH n))) atTop (𝓝 0) := by
  let T := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
  let u n := gradientSchwartz hU χ hχ (hH n)
  let F n := complexTest (localizedCurlTest hU χ hχ (hH n) j m)
  let r n i k := T (SchwartzMap.pderivCLM ℂ (axis i) (u n k))
  let a n i k := fourierMultiplier (angularDirectionSymbol (axis i)) ((u n k).toLp 2 volume)
  have hF := localizedCurlTest_negativeEnergy_tendsto_zero hU χ hχ H hH h0 j m hB hD
  have hBess : Tendsto (fun n => T (F n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have he (n : ℕ) : ‖T (F n)‖ = Real.sqrt (negativeEnergy (F n)) := by
      change ‖fourierMultiplier besselSymbol ((F n).toLp 2 volume)‖ = _
      rw [← besselLp_norm_sq_eq_negativeEnergy, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [he]
    simpa only [Real.sqrt_zero] using hF.sqrt
  have hsplit (n : ℕ) : T (F n) = r n j m - r n m j := by
    change T (complexTest (localizedCurlTest hU χ hχ (hH n) j m)) = _
    rw [curlSchwartz_eq_directional_sub, map_sub]
  have hJ : Tendsto (fun n => r n j m - a n j m) atTop (𝓝 0) :=
    bessel_gradient_pderiv_minus_angular_tendsto_zero hU χ hχ H hH h0 m (axis j) hB
      (fun n x hx => hD n m x hx)
  have hM : Tendsto (fun n => r n m j - a n m j) atTop (𝓝 0) :=
    bessel_gradient_pderiv_minus_angular_tendsto_zero hU χ hχ H hH h0 j (axis m) hB
      (fun n x hx => hD n j x hx)
  have he := (hBess.sub (hJ.sub hM))
  simp only [sub_zero] at he
  apply he.congr
  intro n
  rw [hsplit]
  change (r n j m - r n m j) - (r n j m - a n j m - (r n m j - a n m j)) =
    a n j m - a n m j
  abel

def localizedTensorGradient (χ : D) (H : ℕ → TensorPair → Space → ℝ)
    (n : ℕ) (k : JetIndex) : Space → ℝ := localizedGradient χ (H n k.2) k.1

theorem angularCurl_tensor_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (h0 : ∀ p (K : Set Space), IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => H n p) (fun _ => 0) atTop K)
    (j m : Axis) (p : TensorPair) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n (q : TensorPair) i x, x ∈ tsupport (χ : Space → ℝ) →
      ‖directional i (H n q) x‖ ≤ B) :
    Tendsto (fun n => angularCurl j m (gradientSchwartz hU χ hχ (hH n p))) atTop (𝓝 0) :=
  angularCurl_tendsto_zero hU χ hχ (fun n => H n p) (fun n => hH n p) (h0 p) j m hB
    (fun n i x hx => hD n p i x hx)

end Burnett.F05.CoordinateCurl

noncomputable section

namespace Burnett.F05.CoordinateCurl

open Set Filter MeasureTheory Burnett.Fourier
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet
open Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.BesselLocalization

def tensorGradientSchwartz {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (n : ℕ) (k : JetIndex) : SchwartzMap Space ℂ :=
  gradientSchwartz hU χ hχ (hH n k.2) k.1

theorem tensorGradientSchwartz_apply {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (n : ℕ) (k : JetIndex) (x : Space) :
    tensorGradientSchwartz hU χ hχ H hH n k x = (localizedTensorGradient χ H n k x : ℂ) := rfl

theorem tensorGradient_angularCurl_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (h0 : ∀ p (K : Set Space), IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => H n p) (fun _ => 0) atTop K)
    (j m : Axis) (p : TensorPair) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n (q : TensorPair) i x, x ∈ tsupport (χ : Space → ℝ) →
      ‖directional i (H n q) x‖ ≤ B) :
    Tendsto (fun n => angularCurl j m (fun k => tensorGradientSchwartz hU χ hχ H hH n (k, p)))
      atTop (𝓝 0) :=
  angularCurl_tensor_tendsto_zero hU χ hχ H hH h0 j m p hB hD

def curlRowCoefficients (θ : D) : Fin 2 → D :=
  Fin.cases θ fun _ => -θ

def curlRowDirections (j m : Axis) : Fin 2 → Space :=
  Fin.cases (axis j) fun _ => axis m

def curlRowInputs (j m : Axis) (p : TensorPair) : Fin 2 → JetIndex :=
  Fin.cases (m, p) fun _ => (j, p)

theorem coordinateCurl_firstOrderRow_eq {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : Space → ℝ), (θ : Space → ℝ) x = 1)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (j m : Axis) (p : TensorPair) (n : ℕ) :
    firstOrderRow (curlRowCoefficients θ) (curlRowDirections j m) (curlRowInputs j m p)
      (Fin.elim0 : Fin 0 → D) (Fin.elim0 : Fin 0 → JetIndex)
      (tensorGradientSchwartz hU χ hχ H hH n) = complexTest (localizedCurlTest hU χ hχ (hH n p) j m) := by
  let P := SchwartzMap.pderivCLM ℂ (axis j) (gradientSchwartz hU χ hχ (hH n p) m)
  let Q := SchwartzMap.pderivCLM ℂ (axis m) (gradientSchwartz hU χ hχ (hH n p) j)
  rw [curlSchwartz_eq_directional_sub, firstOrderRow, Fin.sum_univ_two, Fin.sum_univ_zero, add_zero]
  change coeffMul θ P + coeffMul (-θ) Q = P - Q
  apply SchwartzMap.ext
  intro x
  change ((θ : Space → ℝ) x : ℂ) * P x +
    ((-(θ : Space → ℝ) x : ℝ) : ℂ) * Q x = P x - Q x
  by_cases hx : x ∈ tsupport (χ : Space → ℝ)
  · simp [hθ x hx, sub_eq_add_neg]
  · have hzero (i k : Axis) : directional i (localizedGradient χ (H n p) k) x = 0 := by
      unfold directional
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (localizedGradient_tsupport χ (H n p) k h))]
      rfl
    have hp : P x = 0 := by
      change SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1)
        (complexTest (localizedGradientTest hU χ hχ (hH n p) m)) x = 0
      rw [complexTest_pderiv]
      exact_mod_cast hzero j m
    have hq : Q x = 0 := by
      change SchwartzMap.pderivCLM ℂ (EuclideanSpace.single m 1)
        (complexTest (localizedGradientTest hU χ hχ (hH n p) j)) x = 0
      rw [complexTest_pderiv]
      exact_mod_cast hzero m j
    simp [hp, hq]

theorem coordinateCurl_firstOrderRow_negativeEnergy_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : Space → ℝ), (θ : Space → ℝ) x = 1)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (h0 : ∀ p (K : Set Space), IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => H n p) (fun _ => 0) atTop K)
    (j m : Axis) (p : TensorPair) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n (q : TensorPair) i x, x ∈ tsupport (χ : Space → ℝ) →
      ‖directional i (H n q) x‖ ≤ B) :
    Tendsto (fun n => negativeEnergy
      (firstOrderRow (curlRowCoefficients θ) (curlRowDirections j m) (curlRowInputs j m p)
        (Fin.elim0 : Fin 0 → D) (Fin.elim0 : Fin 0 → JetIndex)
        (tensorGradientSchwartz hU χ hχ H hH n))) atTop (𝓝 0) := by
  simp_rw [coordinateCurl_firstOrderRow_eq hU χ hχ θ hθ H hH j m p]
  exact localizedCurlTest_negativeEnergy_tendsto_zero hU χ hχ (fun n => H n p)
    (fun n => hH n p) (h0 p) j m hB (fun n i x hx => hD n p i x hx)

theorem coordinateCurl_rowPrincipal_tendsto_zero {U : Set Space} (hU : IsOpen U)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ U)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : Space → ℝ), (θ : Space → ℝ) x = 1)
    (H : ℕ → TensorPair → Space → ℝ) (hH : ∀ n p, ContDiffOn ℝ ∞ (H n p) U)
    (h0 : ∀ p (K : Set Space), IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => H n p) (fun _ => 0) atTop K)
    (j m : Axis) (p : TensorPair) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ n (q : TensorPair) i x, x ∈ tsupport (χ : Space → ℝ) →
      ‖directional i (H n q) x‖ ≤ B) :
    Tendsto (fun n => rowPrincipal (curlRowCoefficients θ) (curlRowDirections j m) (curlRowInputs j m p)
      (tensorGradientSchwartz hU χ hχ H hH n)) atTop (𝓝 0) := by
  let F (n : ℕ) (k : JetIndex) := localizedGradientTest hU χ hχ (hH n k.2) k.1
  let f (n : ℕ) (k : JetIndex) := (F n k : Space → ℝ)
  let hs (n : ℕ) (k : JetIndex) := test_smooth (F n k)
  have hloc (n : ℕ) (k : JetIndex) (x : Space) (hx : f n k x ≠ 0) : (θ : Space → ℝ) x = 1 :=
    hθ x (localizedGradient_tsupport χ (H n k.2) k.1 (subset_tsupport (f n k) hx))
  have hu (n : ℕ) :
      (fun k => Burnett.Analysis.LocalHminusFourier.sourceSchwartz (hs n k) θ (hloc n k)) =
        tensorGradientSchwartz hU χ hχ H hH n := by
    funext k
    exact SchwartzMap.ext fun _ => rfl
  have he := coordinateCurl_firstOrderRow_negativeEnergy_tendsto_zero hU χ hχ θ hθ H hH h0 j m p hB hD
  have hb (n : ℕ) (k : JetIndex) : ‖(test_memLp (F n k)).toLp (f n k)‖ ≤ B * ‖valueLp χ‖ :=
    localizedGradientTest_L2_bound hU χ hχ (hH n k.2) k.1 hB (fun x hx => hD n k.2 k.1 x hx)
  have ht (k : JetIndex) (φ : D) :
      Tendsto (fun n => ∫ x, f n k x * (φ : Space → ℝ) x) atTop (𝓝 0) :=
    localizedGradientTest_test_tendsto_zero hU χ hχ (fun n => H n k.2) (fun n => hH n k.2)
      (h0 k.2) k.1 φ
  have h := rowPrincipal_tendsto_zero_of_negativeEnergy_tendsto_zero
    (curlRowCoefficients θ) (curlRowDirections j m) (curlRowInputs j m p)
    (Fin.elim0 : Fin 0 → D) (Fin.elim0 : Fin 0 → JetIndex)
    f hs (fun n k => test_memLp (F n k)) θ hloc (B * ‖valueLp χ‖) hb ht
    (by simp only [hu]; exact he)
  simpa only [hu] using h

end Burnett.F05.CoordinateCurl

set_option autoImplicit false
noncomputable section

namespace Burnett.F05.OriginalCoordinateCurl

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.F05.CoordinateCurl Burnett.X02.SobolevTestJet
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.BesselLocalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

def originalComponent (g₀ : Field (M := M)) (g : ℕ → Field (M := M)) (c : M)
    (n : ℕ) (p : TensorPair) (x : CoordinateSpace) : ℝ :=
  metricComponents (coordinateBilinear (g n) c) x p.1 p.2 -
    metricComponents (coordinateBilinear g₀ c) x p.1 p.2

theorem originalComponent_smoothOn (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (c : M) (n : ℕ) (p : TensorPair) :
    ContDiffOn ℝ ∞ (originalComponent g₀ g c n p) (chartAt CoordinateSpace c).target :=
  Burnett.Analysis.LocalWeakDerivative.component_difference_smoothOn g g₀ h₀ hg c p.1 p.2 n

theorem originalComponent_localUniform (r : Metric (M := M))
    (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (hconv : LocallyUniformlyConverges r g g₀) (c : M) (p : TensorPair) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n => originalComponent g₀ g c n p) (fun _ => 0) atTop K :=
  Burnett.Analysis.LocalWeakDerivative.component_difference_uniform_of_physical_C0loc
    r g g₀ hconv c p.1 p.2 K hK hKt

def originalGradientSchwartz (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (k : JetIndex) : SchwartzMap CoordinateSpace ℂ :=
  tensorGradientSchwartz (chartAt CoordinateSpace c).open_target χ hχ (originalComponent g₀ g c)
    (originalComponent_smoothOn g₀ g h₀ hg c) n k

theorem originalGradientSchwartz_apply (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (k : JetIndex) (x : CoordinateSpace) :
    originalGradientSchwartz g₀ g h₀ hg c χ hχ n k x =
      (((χ : CoordinateSpace → ℝ) x *
        directional k.1 (originalComponent g₀ g c n k.2) x : ℝ) : ℂ) := rfl

theorem originalGradientSchwartz_apply_rawJet (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (k : JetIndex) (x : CoordinateSpace) :
    originalGradientSchwartz g₀ g h₀ hg c χ hχ n k x =
      (((χ : CoordinateSpace → ℝ) x * coordinateJet
        (fun y => metricComponents (coordinateBilinear (g n) c) y -
          metricComponents (coordinateBilinear g₀ c) y) x k.1 k.2.1 k.2.2 : ℝ) : ℂ) := rfl

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

set_option maxHeartbeats 1000000 in
theorem exists_rawComponentDerivative_bound_of_original (r : Metric (M := M))
    (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀)
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n (p : TensorPair) (j : Axis) x, x ∈ K →
      ‖directional j (originalComponent g₀ g c n p) x‖ ≤ B := by
  let A (n : ℕ) (x : CoordinateSpace) :=
    metricComponents (coordinateBilinear (g n) c) x - metricComponents (coordinateBilinear g₀ c) x
  let L (n : ℕ) := coordinateJet (A n)
  obtain ⟨B, hB, htail⟩ :=
    Burnett.Geometry.OriginalAdmissibleLocalControl.exists_eventual_rawJet_bound_of_original
      r g₀ g h₀ hg hn₀ hconv hb c K hK hKt
  have hL (n : ℕ) : ContinuousOn (L n) K := by
    apply (Burnett.Geometry.BackgroundConnection.continuousOn_coordinateJet (A n)
      (chartAt CoordinateSpace c).target (chartAt CoordinateSpace c).open_target ?_).mono hKt
    intro a b
    have h := originalComponent_smoothOn g₀ g h₀ hg c n (a,b)
    exact h.of_le (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC, hAll⟩ := Burnett.Analysis.GeometricHminusBoundedForcing.all_bound_of_eventual_on_compact
    L K hK hL hB htail
  refine ⟨C, hC, ?_⟩
  intro n p j x hx
  change ‖L n x j p.1 p.2‖ ≤ C
  exact (norm_le_pi_norm (L n x j p.1) p.2).trans
    ((norm_le_pi_norm (L n x j) p.1).trans ((norm_le_pi_norm (L n x) j).trans (hAll n x hx)))

theorem originalGradient_angularCurl_tendsto_zero (r : Metric (M := M))
    (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀)
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (j m : Axis) (p : TensorPair) :
    Tendsto (fun n => angularCurl j m (fun k => originalGradientSchwartz g₀ g h₀ hg c χ hχ n (k,p)))
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hD⟩ := exists_rawComponentDerivative_bound_of_original r g₀ g h₀ hg hn₀ hconv hb c
    (tsupport (χ : CoordinateSpace → ℝ)) (test_compactSupport χ) hχ
  exact tensorGradient_angularCurl_tendsto_zero (chartAt CoordinateSpace c).open_target χ hχ
    (originalComponent g₀ g c) (originalComponent_smoothOn g₀ g h₀ hg c)
    (originalComponent_localUniform r g₀ g hconv c) j m p hB hD

theorem originalGradient_curlRow_tendsto_zero (r : Metric (M := M))
    (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀)
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (j m : Axis) (p : TensorPair) :
    Tendsto (fun n => rowPrincipal (curlRowCoefficients θ) (curlRowDirections j m) (curlRowInputs j m p)
      (originalGradientSchwartz g₀ g h₀ hg c χ hχ n)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hD⟩ := exists_rawComponentDerivative_bound_of_original r g₀ g h₀ hg hn₀ hconv hb c
    (tsupport (χ : CoordinateSpace → ℝ)) (test_compactSupport χ) hχ
  exact coordinateCurl_rowPrincipal_tendsto_zero (chartAt CoordinateSpace c).open_target χ hχ θ hθ
    (originalComponent g₀ g c) (originalComponent_smoothOn g₀ g h₀ hg c)
    (originalComponent_localUniform r g₀ g hconv c) j m p hB hD

end Burnett.F05.OriginalCoordinateCurl
