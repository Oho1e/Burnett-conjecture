import Burnett.Analysis.GeometricHminusPrincipalClosure
import Burnett.Analysis.Microlocal.CoordinateRicciPrincipalRow
import Burnett.Analysis.WeakTestCalculus

/-!
# The localized Ricci row and its strong graph-dual source
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace Burnett.Microlocal.GeometricNegativeEnergy

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open ManifoldMetricSequence CurvatureDifference
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.X02.SobolevTestJet Burnett.X02.GraphDual
open Burnett.Analysis.HminusWeightedDual Burnett.Analysis.GeometricPrincipalIdentity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def localizedLinearizedRicci (g0 g1 : Field (M := M)) (c : M) (b d : Index) (χ : D)
    (y : CoordinateSpace) : ℝ :=
  (χ : CoordinateSpace → ℝ) y *
    linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear g1 c) y b d

theorem localizedLinearizedRicci_compact (g0 g1 : Field (M := M)) (c : M)
    (b d : Index) (χ : D) : HasCompactSupport (localizedLinearizedRicci g0 g1 c b d χ) :=
  (test_compactSupport χ).mul_right

theorem localizedLinearizedRicci_smooth (g0 g1 : Field (M := M)) (h0 : IsSmooth g0)
    (h1 : IsSmooth g1) (hs0 : IsSymmetric g0) (hs1 : IsSymmetric g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (b d : Index) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hVac : ∀ y ∈ (chartAt CoordinateSpace c).target, ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear g1 c)) y b d = 0) :
    ContDiff ℝ ∞ (localizedLinearizedRicci g0 g1 c b d χ) := by
  let U := (chartAt CoordinateSpace c).target
  let A := Burnett.Analysis.GeometricHminusBoundedForcing.boundedForcing
    (coordinateBilinear g0 c) (coordinateBilinear g1 c)
  let E := ConnectionErrorLInfinity.computedError
    (coordinateBilinear g0 c) (coordinateBilinear g1 c)
  let L := fun y => covariantDivergenceDifference
    (computedConnection (coordinateBilinear g0 c) y) (E y) (coordinateConnectionJet E y) b d
  have hA : ContDiffOn ℝ ∞ (fun y => A y b d) U :=
    Burnett.Analysis.GeometricHminusBoundedForcing.boundedForcing_component_smoothOn
      g0 g1 h0 h1 hn0 hn1 c b d
  have hL : ContDiffOn ℝ ∞ L U := by
    unfold L covariantDivergenceDifference
    exact ContDiffOn.sum (fun a _ =>
      (Burnett.Analysis.GeometricHminusRemainders.covariant_error_component_smoothOn
        g0 g1 h0 h1 hn0 hn1 c a a b d).sub
      (Burnett.Analysis.GeometricHminusRemainders.covariant_error_component_smoothOn
        g0 g1 h0 h1 hn0 hn1 c d a b a))
  have hEq : localizedLinearizedRicci g0 g1 c b d χ =
      fun y => (χ : CoordinateSpace → ℝ) y * (A y b d - L y) := by
    funext y
    unfold localizedLinearizedRicci
    by_cases hy : y ∈ U
    · rw [linearizedRicci_eq_source_sub_error_of_coordinateVacuum
        g0 g1 h0 h1 hs0 hs1 hn0 hn1 c y hy (hVac y hy) b d]
      rfl
    · have hzero : (χ : CoordinateSpace → ℝ) y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy (hχ h))
      simp only [hzero, zero_mul]
  rw [hEq]
  exact contDiff_test_mul_local (chartAt CoordinateSpace c).open_target (test_smooth χ) hχ (hA.sub hL)

theorem tendsto_sourceFunctional_of_realization {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (F : ℕ → (Graph J →L[ℝ] ℝ)) (ht : Tendsto F atTop (𝓝 0))
    (hF : ∀ n (φ : D), F n (testMap J φ) = ∫ y, (φ : Space → ℝ) y * f n y) :
    Tendsto (fun n => sourceFunctional (f n) (hs n) (hc n)) atTop (𝓝 0) := by
  refine ht.congr (fun n => ?_)
  apply testRestriction_injective J
  ext φ
  change F n (testMap J φ) = sourceFunctional (f n) (hs n) (hc n) (testMap J φ)
  rw [hF n φ, sourceFunctional_test]
  simp only [mul_comm]

end Burnett.Microlocal.GeometricNegativeEnergy

namespace Burnett.Microlocal.RicciRemainder

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open Burnett.X02.SobolevTestJet
open Burnett.Analysis.WeakTestCalculus Burnett.Analysis.HminusWeightedDual
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)

structure LocallyBoundedWeakZero (U : Set Space) (f : ℕ → Space → ℝ) : Prop where
  weakZero : SmoothWeakZero U f
  bound (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖f n x‖ ≤ C

theorem LocallyBoundedWeakZero.zero (U : Set Space) :
    LocallyBoundedWeakZero U (fun _ _ => 0) :=
  ⟨SmoothWeakZero.zero U, fun _ _ _ => ⟨0, le_rfl, fun _ _ _ => by simp⟩⟩

theorem LocallyBoundedWeakZero.congr {U : Set Space} {f g : ℕ → Space → ℝ}
    (hf : LocallyBoundedWeakZero U f) (heq : ∀ n x, g n x = f n x) :
    LocallyBoundedWeakZero U g := by
  refine ⟨hf.weakZero.congr heq, fun K hK hKU => ?_⟩
  obtain ⟨C, hC, h⟩ := hf.bound K hK hKU
  exact ⟨C, hC, fun n x hx => (heq n x).symm ▸ h n x hx⟩

theorem LocallyBoundedWeakZero.mul_fixed {U : Set Space} (hU : IsOpen U)
    {f : ℕ → Space → ℝ} (hf : LocallyBoundedWeakZero U f)
    {A : Space → ℝ} (hA : ContDiffOn ℝ ∞ A U) :
    LocallyBoundedWeakZero U (fun n x => A x * f n x) := by
  refine ⟨hf.weakZero.mul_fixed hU hA, fun K hK hKU => ?_⟩
  obtain ⟨C, hC, hCbound⟩ := hf.bound K hK hKU
  obtain ⟨D, hD, hDimage⟩ := (hK.image_of_continuousOn (hA.continuousOn.mono hKU)).isBounded.exists_pos_norm_le
  refine ⟨D * C, mul_nonneg hD.le hC, fun n x hx => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hDimage _ (mem_image_of_mem _ hx)) (hCbound n x hx) (norm_nonneg _) hD.le

theorem LocallyBoundedWeakZero.add {U : Set Space} (hU : IsOpen U)
    {f g : ℕ → Space → ℝ} (hf : LocallyBoundedWeakZero U f) (hg : LocallyBoundedWeakZero U g) :
    LocallyBoundedWeakZero U (fun n x => f n x + g n x) := by
  refine ⟨hf.weakZero.add hU hg.weakZero, fun K hK hKU => ?_⟩
  obtain ⟨A, hA, hAb⟩ := hf.bound K hK hKU
  obtain ⟨B, hB, hBb⟩ := hg.bound K hK hKU
  exact ⟨A+B, add_nonneg hA hB, fun n x hx =>
    (norm_add_le _ _).trans (add_le_add (hAb n x hx) (hBb n x hx))⟩

theorem LocallyBoundedWeakZero.sub {U : Set Space} (hU : IsOpen U)
    {f g : ℕ → Space → ℝ} (hf : LocallyBoundedWeakZero U f) (hg : LocallyBoundedWeakZero U g) :
    LocallyBoundedWeakZero U (fun n x => f n x - g n x) := by
  refine ⟨hf.weakZero.sub hU hg.weakZero, fun K hK hKU => ?_⟩
  obtain ⟨A, hA, hAb⟩ := hf.bound K hK hKU
  obtain ⟨B, hB, hBb⟩ := hg.bound K hK hKU
  exact ⟨A+B, add_nonneg hA hB, fun n x hx =>
    (norm_sub_le _ _).trans (add_le_add (hAb n x hx) (hBb n x hx))⟩

theorem LocallyBoundedWeakZero.sum {ι : Type*} [Fintype ι] {U : Set Space} (hU : IsOpen U)
    {f : ι → ℕ → Space → ℝ} (hf : ∀ i, LocallyBoundedWeakZero U (f i)) :
    LocallyBoundedWeakZero U (fun n x => ∑ i, f i n x) := by
  refine ⟨SmoothWeakZero.finset_sum hU Finset.univ (fun i _ => (hf i).weakZero), fun K hK hKU => ?_⟩
  choose C hC hB using fun i => (hf i).bound K hK hKU
  exact ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun n x hx =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hB i n x hx))⟩

theorem LocallyBoundedWeakZero.of_uniform {U : Set Space} (hU : IsOpen U) {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U → TendstoUniformlyOn f (fun _ => 0) atTop K) :
    LocallyBoundedWeakZero U f := by
  refine ⟨SmoothWeakZero.of_uniform hU hs hu, fun K hK hKU => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp (hu K hK hKU) 1 zero_lt_one)
  choose B hB hBimage using fun n =>
    (hK.image_of_continuousOn ((hs n).continuousOn.mono hKU)).isBounded.exists_pos_norm_le
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨1 + ∑ i ∈ Finset.range N, B i, add_nonneg zero_le_one hsum, fun n x hx => ?_⟩
  by_cases hn : N ≤ n
  · have hb : ‖f n x‖ < 1 := by simpa only [dist_zero_left] using hN n hn x hx
    exact hb.le.trans (le_add_of_nonneg_right hsum)
  · have hnB : B n ≤ ∑ i ∈ Finset.range N, B i :=
      Finset.single_le_sum (fun i _ => (hB i).le) (Finset.mem_range.mpr (not_le.mp hn))
    exact (hBimage n _ (mem_image_of_mem _ hx)).trans (hnB.trans (le_add_of_nonneg_left zero_le_one))

def localizedSource (χ : D) (f : ℕ → Space → ℝ) (n : ℕ) (x : Space) : ℝ := (χ : Space → ℝ) x * f n x

theorem localizedSource_smooth {U : Set Space} (hU : IsOpen U) (χ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ U) {f : ℕ → Space → ℝ}
    (hf : LocallyBoundedWeakZero U f) (n : ℕ) : ContDiff ℝ ∞ (localizedSource χ f n) :=
  contDiff_test_mul_local hU (test_smooth χ) hχ (hf.weakZero.1 n)

theorem localizedSource_compact (χ : D) (f : ℕ → Space → ℝ) (n : ℕ) :
    HasCompactSupport (localizedSource χ f n) := (test_compactSupport χ).mul_right

/-- Actual compactly supported scalar coefficients and locally bounded sequences
with weakly vanishing tests give strong convergence in the existing real dual. -/
theorem localizedSource_functional_tendsto_zero {U : Set Space} (hU : IsOpen U) (χ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ U) {f : ℕ → Space → ℝ}
    (hf : LocallyBoundedWeakZero U f) :
    Tendsto (fun n => sourceFunctional (localizedSource χ f n)
      (localizedSource_smooth hU χ hχ hf n) (localizedSource_compact χ f n)) atTop (𝓝 0) := by
  obtain ⟨θ, hθ⟩ := Burnett.Analysis.GeometricHminusBoundedForcing.exists_global_outer_cutoff χ
  obtain ⟨B, hB, hb⟩ := hf.bound _ (test_compactSupport χ) hχ
  let F := localizedSource χ f
  have hs := localizedSource_smooth hU χ hχ hf
  have hc := localizedSource_compact χ f
  have hχF (n : ℕ) (x : Space) : F n x ≠ 0 → (θ : Space → ℝ) x = 1 := by
    intro hx
    apply hθ
    intro hzero
    exact hx ((show F n x = (χ : Space → ℝ) x * f n x from rfl).trans (by simp only [hzero, zero_mul]))
  have hfLp (n : ℕ) : MemLp (F n) 2 volume :=
    (hs n).continuous.memLp_of_hasCompactSupport (hc n)
  have hbLp (n : ℕ) : ‖(hfLp n).toLp (F n)‖ ≤ B * ‖(test_memLp χ).toLp (χ : Space → ℝ)‖ := by
    apply Burnett.X02.L2Bounds.norm_toLp_le_of_abs_le (hfLp n) (test_memLp χ) hB
    intro x
    change |(χ : Space → ℝ) x * f n x| ≤ B * |(χ : Space → ℝ) x|
    by_cases hx : x ∈ tsupport (χ : Space → ℝ)
    · rw [abs_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb n x hx) (abs_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, abs_zero, mul_zero, le_refl]
  have ht (φ : D) : Tendsto (fun n => ∫ x, F n x * (φ : Space → ℝ) x) atTop (𝓝 0) := by
    have h := hf.weakZero.2 (fun x => (χ : Space → ℝ) x * (φ : Space → ℝ) x)
      ((test_smooth χ).mul (test_smooth φ)) (test_compactSupport χ).mul_right
      (tsupport_mul_subset_left.trans hχ)
    refine h.congr (fun n => integral_congr_ae (Eventually.of_forall (fun x => ?_)))
    change ((χ : Space → ℝ) x * (φ : Space → ℝ) x) * f n x = ((χ : Space → ℝ) x * f n x) * (φ : Space → ℝ) x
    ring
  exact Burnett.Analysis.CompactRellich.sourceFunctional_tendsto_zero_of_commonCutoff hs hfLp θ hχF hbLp ht

end Burnett.Microlocal.RicciRemainder


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace Burnett.Microlocal.RicciRemainder

open MeasureTheory Filter Set
open scoped ContDiff Topology Manifold ENNReal BigOperators
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.AuxiliaryConnection Burnett.Geometry.InverseField Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.Analysis.GeometricPrincipalIdentity Burnett.Microlocal.RicciRow
open Burnett.F05.OriginalCoordinateCurl
open Burnett.X02.SobolevTestJet (D)

def lowerOrder (G : Tensor2) (dG : FirstJet) (Γ : Connection) (dΓ : ConnectionJet)
    (H : Tensor2) (dH : FirstJet) (b d : Index) : ℝ :=
  let W := covariantJet Γ H dH
  let L := fun q => covariantJet (dΓ q) H 0 + covariantJet Γ (dH q) 0
  divergencePrincipal G L b d +
    (∑ a, (christoffel (dG a) W a b d - christoffel (dG d) W a b a)) +
    covariantDivergenceDifference Γ (christoffel G W) 0 b d

private theorem boundedWeakZero_covariantJet {U : Set CoordinateSpace} (hU : IsOpen U)
    (Γ : CoordinateSpace → Connection) (H : ℕ → CoordinateSpace → Tensor2)
    (W : ℕ → CoordinateSpace → FirstJet)
    (hΓ : ∀ a b d, ContDiffOn ℝ ∞ (fun x => Γ x a b d) U)
    (hH : ∀ b d, LocallyBoundedWeakZero U (fun n x => H n x b d))
    (hW : ∀ q b d, LocallyBoundedWeakZero U (fun n x => W n x q b d)) (q b d : Index) :
    LocallyBoundedWeakZero U (fun n x => covariantJet (Γ x) (H n x) (W n x) q b d) := by
  exact ((hW q b d).sub hU (LocallyBoundedWeakZero.sum hU (fun e =>
    (hH e d).mul_fixed hU (hΓ e q b)))).sub hU (LocallyBoundedWeakZero.sum hU (fun e =>
      (hH b e).mul_fixed hU (hΓ e q d)))

private theorem boundedWeakZero_christoffel {U : Set CoordinateSpace} (hU : IsOpen U)
    (G : CoordinateSpace → Tensor2) (W : ℕ → CoordinateSpace → FirstJet)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U)
    (hW : ∀ q b d, LocallyBoundedWeakZero U (fun n x => W n x q b d)) (a b d : Index) :
    LocallyBoundedWeakZero U (fun n x => christoffel (G x) (W n x) a b d) := by
  apply (LocallyBoundedWeakZero.sum hU (fun e =>
    (((hW b d e).add hU (hW d b e)).sub hU (hW e b d)).mul_fixed hU ((hG a e).div_const 2))).congr
  intro n x
  unfold christoffel koszul
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem boundedWeakZero_connectionCorrection {U : Set CoordinateSpace} (hU : IsOpen U)
    (Γ : CoordinateSpace → Connection) (C : ℕ → CoordinateSpace → Connection)
    (hΓ : ∀ a b d, ContDiffOn ℝ ∞ (fun x => Γ x a b d) U)
    (hC : ∀ a b d, LocallyBoundedWeakZero U (fun n x => C n x a b d)) (q a b d : Index) :
    LocallyBoundedWeakZero U (fun n x => covariantDerivative (Γ x) (C n x) 0 q a b d) := by
  apply (LocallyBoundedWeakZero.sum hU (fun e =>
    (((hC e b d).mul_fixed hU (hΓ a q e)).sub hU
      ((hC a e d).mul_fixed hU (hΓ e q b))).sub hU
        ((hC a b e).mul_fixed hU (hΓ e q d)))).congr
  intro n x
  simp only [covariantDerivative, Pi.zero_apply, zero_add]

theorem lowerOrder_boundedWeakZero {U : Set CoordinateSpace} (hU : IsOpen U)
    (G : CoordinateSpace → Tensor2) (dG : CoordinateSpace → FirstJet)
    (Γ : CoordinateSpace → Connection) (dΓ : CoordinateSpace → ConnectionJet)
    (H : ℕ → CoordinateSpace → Tensor2) (dH : ℕ → CoordinateSpace → FirstJet)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U)
    (hdG : ∀ q a e, ContDiffOn ℝ ∞ (fun x => dG x q a e) U)
    (hΓ : ∀ a b d, ContDiffOn ℝ ∞ (fun x => Γ x a b d) U)
    (hdΓ : ∀ q a b d, ContDiffOn ℝ ∞ (fun x => dΓ x q a b d) U)
    (hH : ∀ b d, LocallyBoundedWeakZero U (fun n x => H n x b d))
    (hdH : ∀ q b d, LocallyBoundedWeakZero U (fun n x => dH n x q b d)) (b d : Index) :
    LocallyBoundedWeakZero U (fun n x => lowerOrder (G x) (dG x) (Γ x) (dΓ x) (H n x) (dH n x) b d) := by
  let W (n : ℕ) (x : CoordinateSpace) := covariantJet (Γ x) (H n x) (dH n x)
  let L (q : Index) (n : ℕ) (x : CoordinateSpace) :=
    covariantJet (dΓ x q) (H n x) 0 + covariantJet (Γ x) (dH n x q) 0
  have hW : ∀ q a e, LocallyBoundedWeakZero U (fun n x => W n x q a e) :=
    boundedWeakZero_covariantJet hU Γ H dH hΓ hH hdH
  have hL (q j a e : Index) : LocallyBoundedWeakZero U (fun n x => L q n x j a e) :=
    (boundedWeakZero_covariantJet hU (fun x => dΓ x q) H (fun _ _ => 0) (hdΓ q) hH
      (fun _ _ _ => LocallyBoundedWeakZero.zero U) j a e).add hU
      (boundedWeakZero_covariantJet hU Γ (fun n x => dH n x q) (fun _ _ => 0) hΓ (hdH q)
        (fun _ _ _ => LocallyBoundedWeakZero.zero U) j a e)
  have hA (q a b d : Index) := boundedWeakZero_christoffel hU G (L q) hG (hL q) a b d
  have hB (q a b d : Index) :=
    boundedWeakZero_christoffel hU (fun x => dG x q) W (hdG q) hW a b d
  have hC := boundedWeakZero_connectionCorrection hU Γ (fun n x => christoffel (G x) (W n x)) hΓ
    (boundedWeakZero_christoffel hU G W hG hW)
  exact ((LocallyBoundedWeakZero.sum hU (fun a => (hA a a b d).sub hU (hA d a b a))).add hU
    (LocallyBoundedWeakZero.sum hU (fun a => (hB a a b d).sub hU (hB d a b a)))).add hU
    (LocallyBoundedWeakZero.sum hU (fun a => (hC a a b d).sub hU (hC d a b a)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def chartBackgroundInverse (g0 : Field (M := M)) (c : M) (x : CoordinateSpace) : Tensor2 :=
  matrixInverse (metricComponents (coordinateBilinear g0 c) x)

def rawPerturbation (g0 g1 : Field (M := M)) (c : M) (x : CoordinateSpace) : Tensor2 :=
  metricComponents (coordinateBilinear g1 c) x - metricComponents (coordinateBilinear g0 c) x

def chartLowerOrder (g0 g1 : Field (M := M)) (c : M) (x : CoordinateSpace) (b d : Index) : ℝ :=
  let G := chartBackgroundInverse g0 c
  let Γ := computedConnection (coordinateBilinear g0 c)
  let H := rawPerturbation g0 g1 c
  lowerOrder (G x) (coordinateJet G x) (Γ x) (coordinateConnectionJet Γ x)
    (H x) (coordinateJet H x) b d

theorem chart_linearizedRicci_eq_rawPrincipal_add_chartLowerOrder (g0 g1 : Field (M := M))
    (h0 : IsSmooth g0) (h1 : IsSmooth g1) (hn0 : IsNondegenerate g0) (c : M)
    (x : CoordinateSpace) (hx : x ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear g1 c) x b d =
      divergencePrincipal (chartBackgroundInverse g0 c x)
        (directionalJet (coordinateJet (rawPerturbation g0 g1 c)) x) b d +
      chartLowerOrder g0 g1 c x b d := by
  rw [chart_linearizedRicci_eq_rawPrincipal_add_lower g0 g1 h0 h1 hn0 c x hx b d]
  simp only [chartLowerOrder, lowerOrder, rawPerturbation, chartBackgroundInverse,
    auxiliaryPerturbationJet, ← add_assoc]
  rfl

theorem chart_rawPerturbation_boundedWeakZero (r : Metric (M := M)) (g0 : Field (M := M))
    (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hconv : LocallyUniformlyConverges r g g0) (c : M) (b d : Index) :
    LocallyBoundedWeakZero (chartAt CoordinateSpace c).target
      (fun n x => rawPerturbation g0 (g n) c x b d) :=
  LocallyBoundedWeakZero.of_uniform (chartAt CoordinateSpace c).open_target
    (fun n => originalComponent_smoothOn g0 g h0 hg c n (b,d))
    (originalComponent_localUniform r g0 g hconv c (b,d))

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem chart_rawJet_boundedWeakZero (r : Metric (M := M)) (g0 : Field (M := M))
    (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (q b d : Index) :
    LocallyBoundedWeakZero (chartAt CoordinateSpace c).target
      (fun n x => coordinateJet (rawPerturbation g0 (g n) c) x q b d) := by
  refine ⟨(chart_rawPerturbation_boundedWeakZero r g0 g h0 hg hconv c b d).weakZero.directional
    (chartAt CoordinateSpace c).open_target (EuclideanSpace.single q 1), fun K hK hKU => ?_⟩
  obtain ⟨B, hB, hbound⟩ :=
    exists_rawComponentDerivative_bound_of_original r g0 g h0 hg hn0 hconv hb c K hK hKU
  exact ⟨B, hB, fun n x hx => hbound n (b,d) q x hx⟩

theorem chartLowerOrder_boundedWeakZero_of_original (r : Metric (M := M)) (g0 : Field (M := M))
    (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (b d : Index) : LocallyBoundedWeakZero (chartAt CoordinateSpace c).target
      (fun n x => chartLowerOrder g0 (g n) c x b d) := by
  let U := (chartAt CoordinateSpace c).target
  let G := chartBackgroundInverse g0 c
  let Γ := computedConnection (coordinateBilinear g0 c)
  let H (n : ℕ) := rawPerturbation g0 (g n) c
  have hU := (chartAt CoordinateSpace c).open_target
  have hG (a e : Index) : ContDiffOn ℝ ∞ (fun x => G x a e) U :=
    coordinateInverse_component_smoothOn g0 h0 hn0 c a e
  have hΓ (a i j : Index) : ContDiffOn ℝ ∞ (fun x => Γ x a i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp
      (Burnett.Geometry.SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c) a) i) j
  have hdG (q a e : Index) : ContDiffOn ℝ ∞ (fun x => coordinateJet G x q a e) U :=
    Burnett.Geometry.SmoothMetricConnection.contDiffOn_coordinateJet G U hU hG q a e
  have hdΓ (q a i j : Index) : ContDiffOn ℝ ∞ (fun x => coordinateConnectionJet Γ x q a i j) U :=
    (((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (hΓ a i j)).2).clm_apply contDiffOn_const
  exact lowerOrder_boundedWeakZero hU G (coordinateJet G) Γ (coordinateConnectionJet Γ) H
    (fun n => coordinateJet (H n)) hG hdG hΓ hdΓ
    (chart_rawPerturbation_boundedWeakZero r g0 g h0 hg hconv c)
    (chart_rawJet_boundedWeakZero r g0 g h0 hg hn0 hconv hb c) b d

end Burnett.Microlocal.RicciRemainder


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace Burnett.Microlocal.RicciRemainder

open MeasureTheory Filter Set
open scoped ContDiff Topology Manifold ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.Analysis.GeometricPrincipalIdentity Burnett.Microlocal.RicciRow
open Burnett.X02.SobolevTestJet (D test_smooth)
open Burnett.Analysis.HminusWeightedDual

def cutoffError (G : Tensor2) (W : FirstJet) (χ : D) (x : CoordinateSpace) (b d : Index) : ℝ :=
  ∑ s : PrincipalTerm, termCoefficient G s *
    fderiv ℝ (χ : CoordinateSpace → ℝ) x (EuclideanSpace.single (termDirection d s) 1) *
    W (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2

theorem cutoffError_boundedWeakZero {U : Set CoordinateSpace} (hU : IsOpen U)
    (G : CoordinateSpace → Tensor2) (W : ℕ → CoordinateSpace → FirstJet) (χ : D)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U)
    (hW : ∀ q b d, LocallyBoundedWeakZero U (fun n x => W n x q b d)) (b d : Index) :
    LocallyBoundedWeakZero U (fun n x => cutoffError (G x) (W n x) χ x b d) := by
  apply LocallyBoundedWeakZero.sum hU
  intro s
  have hcoef : ContDiffOn ℝ ∞ (fun x => termCoefficient (G x) s) U :=
    contDiffOn_const.mul ((hG s.1 s.2.1).div_const 2)
  have hDχ : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (χ : CoordinateSpace → ℝ) x (EuclideanSpace.single (termDirection d s) 1)) U :=
    (((test_smooth χ).fderiv_right (by simp)).clm_apply contDiff_const).contDiffOn
  exact (hW (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2).mul_fixed hU
    (hcoef.mul hDχ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def chartRowErrorCore (g0 g1 : Field (M := M)) (c : M) (χ : D)
    (x : CoordinateSpace) (b d : Index) : ℝ :=
  cutoffError (chartBackgroundInverse g0 c x) (coordinateJet (rawPerturbation g0 g1 c) x) χ x b d -
    (χ : CoordinateSpace → ℝ) x * chartLowerOrder g0 g1 c x b d

def chartRowError (g0 g1 : Field (M := M)) (c : M) (χ θ : D) (b d : Index)
    (x : CoordinateSpace) : ℝ :=
  (θ : CoordinateSpace → ℝ) x * chartRowErrorCore g0 g1 c χ x b d

/-- On the very same cutoff raw derivative sequence, the real first-order
Ricci row equals the localized original operator plus the actual error. -/
theorem chartLocalizedSum_eq_linearizedRicci_add_error (g0 g1 : Field (M := M))
    (h0 : IsSmooth g0) (h1 : IsSmooth g1) (hn0 : IsNondegenerate g0) (c : M) (χ θ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (x : CoordinateSpace) (b d : Index) :
    let G := chartBackgroundInverse g0 c
    let W := coordinateJet (rawPerturbation g0 g1 c)
    let A := fun s : PrincipalTerm => (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s
    let v := fun s : PrincipalTerm => EuclideanSpace.single (termDirection d s) (1 : ℝ)
    let w := fun s : PrincipalTerm => fun y => W y (termInput b d s).1
      (termInput b d s).2.1 (termInput b d s).2.2
    (∑ s, A s * fderiv ℝ (fun y => (χ : CoordinateSpace → ℝ) y * w s y) x (v s)) =
      (χ : CoordinateSpace → ℝ) x *
        linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear g1 c) x b d +
      chartRowError g0 g1 c χ θ b d x := by
  let G := chartBackgroundInverse g0 c
  let W := coordinateJet (rawPerturbation g0 g1 c)
  let U := (chartAt CoordinateSpace c).target
  have hU := (chartAt CoordinateSpace c).open_target
  have hH (j k : Index) : ContDiffOn ℝ ∞ (fun y => rawPerturbation g0 g1 c y j k) U :=
    (contDiffOn_metricComponents g1 h1 c j k).sub
      (contDiffOn_metricComponents g0 h0 c j k)
  have hW (q j k : Index) : ContDiffOn ℝ ∞ (fun y => W y q j k) U :=
    Burnett.Geometry.SmoothMetricConnection.contDiffOn_coordinateJet (rawPerturbation g0 g1 c) U hU hH q j k
  dsimp only
  rw [show (∑ s : PrincipalTerm, _) = (χ : CoordinateSpace → ℝ) x *
      divergencePrincipal (G x) (directionalJet W x) b d +
      ∑ s : PrincipalTerm, (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s *
        fderiv ℝ (χ : CoordinateSpace → ℝ) x (EuclideanSpace.single (termDirection d s) 1) *
        W x (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2
      from localizedSum_eq_principal_add_cutoff G W χ θ hU hχ hθ hW x b d]
  have hsum : (∑ s : PrincipalTerm, (θ : CoordinateSpace → ℝ) x * termCoefficient (G x) s *
      fderiv ℝ (χ : CoordinateSpace → ℝ) x (EuclideanSpace.single (termDirection d s) 1) *
      W x (termInput b d s).1 (termInput b d s).2.1 (termInput b d s).2.2) =
      (θ : CoordinateSpace → ℝ) x * cutoffError (G x) (W x) χ x b d := by
    rw [cutoffError, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum]
  by_cases hx : x ∈ tsupport (χ : CoordinateSpace → ℝ)
  · rw [chart_linearizedRicci_eq_rawPrincipal_add_chartLowerOrder g0 g1 h0 h1 hn0 c x (hχ hx),
      chartRowError, chartRowErrorCore, hθ x hx]
    change (χ : CoordinateSpace → ℝ) x * divergencePrincipal (G x) (directionalJet W x) b d +
        1 * cutoffError (G x) (W x) χ x b d =
        (χ : CoordinateSpace → ℝ) x * (divergencePrincipal (G x) (directionalJet W x) b d +
          chartLowerOrder g0 g1 c x b d) +
        1 * (cutoffError (G x) (W x) χ x b d -
          (χ : CoordinateSpace → ℝ) x * chartLowerOrder g0 g1 c x b d)
    ring
  · simp only [chartRowError, chartRowErrorCore, image_eq_zero_of_notMem_tsupport hx, zero_mul,
      zero_add, sub_zero, G, W]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem chartRowErrorCore_boundedWeakZero_of_original (r : Metric (M := M)) (g0 : Field (M := M))
    (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (χ : D) (b d : Index) : LocallyBoundedWeakZero (chartAt CoordinateSpace c).target
      (fun n x => chartRowErrorCore g0 (g n) c χ x b d) := by
  have hU := (chartAt CoordinateSpace c).open_target
  exact (cutoffError_boundedWeakZero hU (chartBackgroundInverse g0 c)
    (fun n => coordinateJet (rawPerturbation g0 (g n) c)) χ
    (coordinateInverse_component_smoothOn g0 h0 hn0 c)
    (chart_rawJet_boundedWeakZero r g0 g h0 hg hn0 hconv hb c) b d).sub hU
      ((chartLowerOrder_boundedWeakZero_of_original r g0 g h0 hg hn0 hconv hb c b d).mul_fixed hU
        (test_smooth χ).contDiffOn)

/-- The combined true cutoff and lower-order error vanishes in the real
Sobolev graph dual under the original first derivative hypotheses. -/
theorem chartRowError_sourceFunctional_tendsto_zero_of_original (r : Metric (M := M))
    (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (χ θ : D) (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (b d : Index) :
    let hW := chartRowErrorCore_boundedWeakZero_of_original r g0 g h0 hg hn0 hconv hb c χ b d
    let F := fun n x => chartRowErrorCore g0 (g n) c χ x b d
    Tendsto (fun n => sourceFunctional (chartRowError g0 (g n) c χ θ b d)
      (localizedSource_smooth (chartAt CoordinateSpace c).open_target θ hθ hW n)
      (localizedSource_compact θ F n)) atTop (𝓝 0) :=
  localizedSource_functional_tendsto_zero (chartAt CoordinateSpace c).open_target θ hθ
    (chartRowErrorCore_boundedWeakZero_of_original r g0 g h0 hg hn0 hconv hb c χ b d)

end Burnett.Microlocal.RicciRemainder


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace Burnett.Microlocal.RicciRemainder

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldMetricSequence
open Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.GeometricNegativeEnergy
open Burnett.X02.SobolevTestJet (D Space J test_smooth)
open Burnett.X02.GraphDual

theorem sourceFunctional_add_sources (f g : Space → ℝ) (hsf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (hsg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    sourceFunctional (fun x => f x + g x) (hsf.add hsg) (hcf.add hcg) =
      sourceFunctional f hsf hcf + sourceFunctional g hsg hcg := by
  apply testRestriction_injective J
  ext φ
  change sourceFunctional (fun x => f x + g x) (hsf.add hsg) (hcf.add hcg) (testMap J φ) =
    sourceFunctional f hsf hcf (testMap J φ) + sourceFunctional g hsg hcg (testMap J φ)
  rw [sourceFunctional_test, sourceFunctional_test, sourceFunctional_test]
  simp only [add_mul]
  exact integral_add
    ((hsf.mul (test_smooth φ)).continuous.integrable_of_hasCompactSupport hcf.mul_right)
    ((hsg.mul (test_smooth φ)).continuous.integrable_of_hasCompactSupport hcg.mul_right)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def chartRowSource (g0 g1 : Field (M := M)) (c : M) (χ θ : D) (b d : Index)
    (x : CoordinateSpace) : ℝ :=
  localizedLinearizedRicci g0 g1 c b d χ x + chartRowError g0 g1 c χ θ b d x

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The exact cutoff Ricci row in physical space has a strongly vanishing
real graph-dual source. Its definition includes the actual cutoff error. -/
theorem exists_chartRowSource_strong_zero_of_original (r : Metric (M := M)) (g0 : Field (M := M))
    (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
    (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (χ θ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) (b d : Index) :
    ∃ hS : ∀ n, ContDiff ℝ ∞ (chartRowSource g0 (g n) c χ θ b d),
    ∃ hC : ∀ n, HasCompactSupport (chartRowSource g0 (g n) c χ θ b d),
      Tendsto (fun n => sourceFunctional (chartRowSource g0 (g n) c χ θ b d) (hS n) (hC n)) atTop (𝓝 0) := by
  let F (n : ℕ) := localizedLinearizedRicci g0 (g n) c b d χ
  let E (n : ℕ) := chartRowError g0 (g n) c χ θ b d
  let hF (n : ℕ) := localizedLinearizedRicci_smooth g0 (g n) h0 (hg n) hs0 (hs n) hn0 (hn n)
    c b d χ hχ (hVac n)
  let hFc (n : ℕ) := localizedLinearizedRicci_compact g0 (g n) c b d χ
  let hW := chartRowErrorCore_boundedWeakZero_of_original r g0 g h0 hg hn0 hconv hb c χ b d
  let hE (n : ℕ) := localizedSource_smooth (chartAt CoordinateSpace c).open_target θ hθ hW n
  let hEc (n : ℕ) := localizedSource_compact θ (fun n x => chartRowErrorCore g0 (g n) c χ x b d) n
  obtain ⟨H, hH, hH0, _⟩ :=
    Burnett.Analysis.GeometricHminusPrincipalClosure.linearizedRicci_has_strong_realization_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac b d χ hχ
  have hFt : Tendsto (fun n => sourceFunctional (F n) (hF n) (hFc n)) atTop (𝓝 0) :=
    tendsto_sourceFunctional_of_realization hF hFc H hH0 (fun n φ => (hH n φ).2)
  have hEt : Tendsto (fun n => sourceFunctional (E n) (hE n) (hEc n)) atTop (𝓝 0) :=
    chartRowError_sourceFunctional_tendsto_zero_of_original r g0 g h0 hg hn0 hconv hb c χ θ hθ b d
  refine ⟨fun n => (hF n).add (hE n), fun n => (hFc n).add (hEc n), ?_⟩
  have hT := hFt.add hEt
  simp only [add_zero] at hT
  exact hT.congr (fun n => (sourceFunctional_add_sources (F n) (E n) (hF n) (hFc n) (hE n) (hEc n)).symm)

end Burnett.Microlocal.RicciRemainder
