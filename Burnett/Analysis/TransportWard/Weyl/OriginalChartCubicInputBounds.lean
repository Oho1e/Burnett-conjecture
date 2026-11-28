import Burnett.Analysis.TransportWard.Weyl.CubicPatchSchwartzBinding
import Burnett.Analysis.TransportWard.Weyl.OrderedWeylInputEuclideanL3
import Burnett.Analysis.TransportWard.Weyl.WeylPatchInputBinding
import Burnett.Analysis.TransportWard.Weyl.CompactMetricSegment
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedEnergyFields

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol Burnett.A02.FrequencySplit
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- The exact C03 pointwise modulus for the original metric components on
any compact part of the receiving chart. -/
theorem exists_originalChart_component_error_modulus
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hconv : LocallyUniformlyConverges r g B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ c.chart.target) :
    ∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ n x, x ∈ K →
        ‖metricComponents (fixedForm (g n) c) x - metricComponents (fixedForm B c) x‖ ≤ e n := by
  let H (n : ℕ) := fixedPerturbation B (g n) c
  have hH (n : ℕ) : ContinuousOn (H n) K := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (fixedComponent_smooth B g hB hg c n (i,j)).continuousOn.mono hKU
  have hLim : TendstoUniformlyOn H (fun _ => 0) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro d hd
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (fixed_components_uniform_of_physical_C0loc r g B hconv c K hK hKU) d hd] with n h
    intro x hx
    simpa only [dist_eq_norm, sub_zero, H, fixedPerturbation, norm_sub_rev] using h x hx
  exact exists_compact_uniform_zero_norm_modulus hK H hH hLim

omit [MeasurableSpace M] [BorelSpace M] in
theorem exists_originalWeylCutoff_value_uniform_modulus
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hconv : LocallyUniformlyConverges r g B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    ∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ n (i : OrderedPair) x, ‖fixedWeylPerturbationSchwartz B g hB hg c χ hχ n i x‖ ≤ e n := by
  obtain ⟨e, he, ht, hBound⟩ :=
    exists_originalChart_component_error_modulus r B g hB hg hconv c _ (test_compactSupport χ) hχ
  let χs : SchwartzMap E ℝ := (test_compactSupport χ).toSchwartzMap (test_smooth χ)
  let C := SchwartzMap.seminorm ℝ 0 0 χs
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨fun n => C * e n, fun n => mul_nonneg hC (he n), ?_, ?_⟩
  · simpa only [mul_zero] using ht.const_mul C
  · intro n i x
    let H := fixedPerturbation B (g n) c x
    change ‖Complex.ofReal ((χ : E → ℝ) x * H i.1 i.2)‖ ≤ C * e n
    by_cases hx : x ∈ tsupport (χ : E → ℝ)
    · have hχs : ‖(χ : E → ℝ) x‖ ≤ C := SchwartzMap.norm_le_seminorm ℝ χs x
      have hH := ((norm_le_pi_norm (H i.1) i.2).trans (norm_le_pi_norm H i.1)).trans (hBound n x hx)
      rw [Complex.norm_real, norm_mul]
      exact mul_le_mul hχs hH (norm_nonneg _) hC
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, Complex.ofReal_zero, norm_zero]
      exact mul_nonneg hC (he n)

private theorem originalWeylCutoff_component_L3
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    let Z := fixedWeylPerturbationSchwartz B g hB hg c χ hχ
    ∃ (e : ℕ → ℝ) (V : ℝ≥0∞), (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧ V < ⊤ ∧
      (∀ n i, eLpNorm (Z n i : E → ℂ) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (e n)) ∧
      (∀ n a i, eLpNorm (energyPartial a (Z n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ V) := by
  intro Z
  let K := tsupport (χ : E → ℝ)
  have hK : IsCompact K := test_compactSupport χ
  obtain ⟨e, C, he, hC, ht, _, hLp⟩ := exists_originalOrderedWeylCutoff_euclidean_patchL3
    r B g hB hg hn hconv hb c χ hχ K hK (Subset.rfl)
  let D := volume K ^ (1 / 3 : ℝ)
  have hD : D < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.measure_lt_top.ne
  let u n := e n * D.toReal
  let V := ENNReal.ofReal C * D
  refine ⟨u, V, fun n => mul_nonneg (he n) ENNReal.toReal_nonneg, ?_,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD, ?_, ?_⟩
  · simpa only [u, zero_mul] using ht.mul_const D.toReal
  · intro n i
    refine ((separated_field_component_L3_bounds (Z n)).1 i).trans ((hLp n).1.trans_eq ?_)
    rw [ENNReal.ofReal_mul (he n), ENNReal.ofReal_toReal hD.ne]
  · intro n a i
    exact ((separated_field_component_L3_bounds (Z n)).2.1 (a,i)).trans (hLp n).2

/-- The raw Weyl perturbation and the localized perturbation supplied to
C03 have simultaneous componentwise L³ moduli along the same subsequence. -/
theorem exists_originalWeylCutoff_and_patch_component_L3
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ d : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (hd : tsupport (d : E → ℝ) ⊆ c.chart.target)
    (hOne : ∀ x ∈ tsupport (d : E → ℝ), (χ : E → ℝ) x = 1)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    let Z n := fixedWeylPerturbationSchwartz B g hB hg c χ hχ (σ n)
    let U n i := energyProduct (Burnett.C01.realTestComplexSchwartz d) (Z n i)
    ∃ (e : ℕ → ℝ) (V : ℝ≥0∞), (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧ V < ⊤ ∧
      (∀ n i, eLpNorm (Z n i : E → ℂ) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (e n)) ∧
      (∀ n i, eLpNorm (U n i : E → ℂ) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (e n)) ∧
      (∀ n a i, eLpNorm (energyPartial a (Z n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ V) ∧
      (∀ n a i, eLpNorm (energyPartial a (U n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ V) := by
  intro Z U
  obtain ⟨e, V, he, ht, hV, hZ, hDZ⟩ :=
    originalWeylCutoff_component_L3 r B g hB hg hn hconv hb c χ hχ
  obtain ⟨δ, W, hδ, hδt, hW, hU, hDU⟩ :=
    originalWeylCutoff_component_L3 r B g hB hg hn hconv hb c d hd
  have hEq (n : ℕ) (i : OrderedPair) : U n i =
      fixedWeylPerturbationSchwartz B g hB hg c d hd (σ n) i := by
    obtain ⟨i, j⟩ := i
    dsimp only [U, Z]
    rw [fixedWeylPerturbationSchwartz_eq_receivingCutoffFluctuation,
      fixedWeylPerturbationSchwartz_eq_receivingCutoffFluctuation]
    exact Burnett.P01.receivingCutoffFluctuation_eq_patch_product_of_plateau
      B g hB hg c χ d hχ hd hOne (σ n) i j
  refine ⟨fun n => e (σ n) + δ (σ n), V + W, fun n => add_nonneg (he _) (hδ _), ?_,
    ENNReal.add_lt_top.mpr ⟨hV, hW⟩, fun n i => (hZ (σ n) i).trans ?_, ?_,
    fun n a i => (hDZ (σ n) a i).trans le_self_add, ?_⟩
  · simpa only [add_zero, Function.comp_apply] using (ht.add hδt).comp hσ.tendsto_atTop
  · exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hδ _))
  · intro n i
    rw [hEq]
    exact (hU (σ n) i).trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (he _)))
  · intro n a i
    rw [hEq]
    exact (hDU (σ n) a i).trans le_add_self

end Burnett.V03
