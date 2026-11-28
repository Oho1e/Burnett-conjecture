import Burnett.Geometry.AuxiliaryAdmissibility
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs
import Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput
import Burnett.Analysis.TransportWard.Weyl.CompactMetricSegment
import Burnett.Analysis.TransportPatches.PatchLpInput

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxRecDepth 3900

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol Burnett.P01
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ContDiff ENNReal Manifold Topology

open private fixedWeylPerturbationSchwartz_partial_apply from Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput
open private projectionMatrixLpNorm_le_of_support coordinateDerivative_zero_outside from
  Burnett.Analysis.GaugeProjection.LocalizedProjectedFiniteLp

local notation "E₀" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- For the original unprojected Weyl input, the C03 support estimate gives
smallness at every finite exponent and bounded coordinate derivatives on the
same window. The constants are fixed before the original sequence index. -/
theorem exists_originalWeylCutoff_matrix_patchLp
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target)
    (K : Set E₀) (hK : IsCompact K) (hχK : tsupport (χ : E₀ → ℝ) ⊆ K) :
    let Z (n : ℕ) : ProjectionSchwartzMatrix :=
      fun i j => fixedWeylPerturbationSchwartz B g hB hg c χ hχ n (i, j)
    ∃ (e : ℕ → ℝ) (C : ℝ), (∀ n, 0 ≤ e n) ∧ 0 ≤ C ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ (p : ℝ), 0 < p →
        Tendsto (fun n => (projectionMatrixLpNorm p (Z n)).toReal) atTop (𝓝 0) ∧
        ∀ n, projectionMatrixLpNorm p (Z n) ≤ ENNReal.ofReal (e n) * volume K ^ (1 / p) ∧
          ∀ a : Index, projectionMatrixLpNorm p (projectionMatrixDerivative a (Z n)) ≤
            ENNReal.ofReal C * volume K ^ (1 / p) := by
  classical
  intro Z
  let L := tsupport (χ : E₀ → ℝ)
  have hL : IsCompact L := test_compactSupport χ
  let f n := fixedPerturbation B (g n) c
  have hFc (n : ℕ) : ContinuousOn (f n) L := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (fixedComponent_smooth B g hB hg c n (i,j)).continuousOn.mono hχ
  have hFu : TendstoUniformlyOn f (fun _ => 0) atTop L := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro d hd
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (fixed_components_uniform_of_physical_C0loc r g B hconv c L hL hχ) d hd] with n h
    intro x hx
    simpa only [dist_eq_norm, sub_zero, f, fixedPerturbation, norm_sub_rev] using h x hx
  obtain ⟨u, hu, huLim, huBound⟩ :=
    exists_compact_uniform_zero_norm_modulus hL f hFc hFu
  obtain ⟨U, hU⟩ := (Metric.isBounded_range_of_tendsto _ huLim).exists_norm_le
  have hU₀ : 0 ≤ U := (norm_nonneg _).trans (hU _ ⟨0,rfl⟩)
  have hU' (n : ℕ) : u n ≤ U := by
    simpa only [Real.norm_of_nonneg (hu n)] using hU _ ⟨n,rfl⟩
  obtain ⟨D, hD₀, hD⟩ := Burnett.Microlocal.AtlasVolumeGradient.fixedJet_uniform_bound_on_compact
    r B g hB hg hn hconv hb c hL hχ
  let ρ : SchwartzMap E₀ ℝ := (test_compactSupport χ).toSchwartzMap (test_smooth χ)
  let A₀ := SchwartzMap.seminorm ℝ 0 0 ρ
  let ρ₁ (a : Index) := SchwartzMap.pderivCLM ℝ (coordinateDirection a) ρ
  let A₁ : ℝ := ∑ a : Index, SchwartzMap.seminorm ℝ 0 0 (ρ₁ a)
  have hA₀ : 0 ≤ A₀ := apply_nonneg _ _
  have hA₁ : 0 ≤ A₁ := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have hχ0 (x : E₀) : ‖(χ : E₀ → ℝ) x‖ ≤ A₀ := SchwartzMap.norm_le_seminorm ℝ ρ x
  have hχ1 (a : Index) (x : E₀) : ‖fderiv ℝ (χ : E₀ → ℝ) x (coordinateDirection a)‖ ≤ A₁ :=
    (SchwartzMap.norm_le_seminorm ℝ (ρ₁ a) x).trans
      (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ a))
  let e (n : ℕ) := A₀ * u n
  let C := A₀ * D + A₁ * U
  have he (n : ℕ) : 0 ≤ e n := mul_nonneg hA₀ (hu n)
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hA₀ hD₀) (mul_nonneg hA₁ hU₀)
  have heLim : Tendsto e atTop (𝓝 0) := by
    simpa only [e, mul_zero] using huLim.const_mul A₀
  have hZ (n : ℕ) (i j : Index) (x : E₀) :
      Z n i j x = (((χ : E₀ → ℝ) x * f n x i j : ℝ) : ℂ) := rfl
  have hZ0 (n : ℕ) (x : E₀) (i j : Index) (hx : x ∉ L) : Z n i j x = 0 := by
    rw [hZ, image_eq_zero_of_notMem_tsupport hx, zero_mul, Complex.ofReal_zero]
  have hSupp (n : ℕ) (i j : Index) : tsupport (Z n i j : E₀ → ℂ) ⊆ L :=
    closure_minimal (fun x hx => by by_contra ho; exact hx (hZ0 n x i j ho)) (isClosed_tsupport _)
  have hVal (n : ℕ) (x : E₀) (i j : Index) (hx : x ∈ L) : ‖f n x i j‖ ≤ u n :=
    ((norm_le_pi_norm (f n x i) j).trans (norm_le_pi_norm (f n x) i)).trans (huBound n x hx)
  have hG (n : ℕ) (a i j : Index) (x : E₀) :
      projectionMatrixDerivative a (Z n) i j x =
        ((((χ : E₀ → ℝ) x * coordinateJet (f n) x a i j) : ℝ) : ℂ) +
        (((fderiv ℝ (χ : E₀ → ℝ) x (coordinateDirection a) * f n x i j : ℝ)) : ℂ) := by
    simpa only [Z, projectionMatrixDerivative, Burnett.A07.coordinateDerivative, coordinateDirection,
      fixedGradientSchwartz_apply] using fixedWeylPerturbationSchwartz_partial_apply
        B g hB hg c χ hχ n (a,(i,j)) x
  have hValue (n : ℕ) (x : E₀) (i j : Index) : ‖Z n i j x‖ ≤ e n := by
    by_cases hx : x ∈ L
    · rw [hZ, Complex.norm_real, norm_mul]
      exact mul_le_mul (hχ0 x) (hVal n x i j hx) (norm_nonneg _) hA₀
    · rw [hZ0 n x i j hx, norm_zero]
      exact he n
  have hGrad (n : ℕ) (a : Index) (x : E₀) (i j : Index) :
      ‖projectionMatrixDerivative a (Z n) i j x‖ ≤ C := by
    by_cases hx : x ∈ L
    · rw [hG]
      refine (norm_add_le _ _).trans ?_
      simp only [Complex.norm_real,norm_mul]
      let J := coordinateJet (f n) x
      have hJ : ‖J a i j‖ ≤ D :=
        (norm_le_pi_norm (J a i) j).trans
          ((norm_le_pi_norm (J a) i).trans ((norm_le_pi_norm J a).trans (hD n x hx)))
      exact add_le_add (mul_le_mul (hχ0 x) hJ (norm_nonneg _) hA₀)
        (mul_le_mul (hχ1 a x) ((hVal n x i j hx).trans (hU' n)) (norm_nonneg _) hA₁)
    · rw [show projectionMatrixDerivative a (Z n) i j x = 0 from
        coordinateDerivative_zero_outside (Z n i j) L (hSupp n i j) a x hx, norm_zero]
      exact hC
  refine ⟨e,C,he,hC,heLim,fun p hp => ?_⟩
  let W : ℝ≥0∞ := volume K ^ (1 / p)
  have hW : W < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  have Hv (n : ℕ) : projectionMatrixLpNorm p (Z n) ≤ ENNReal.ofReal (e n) * W :=
    projectionMatrixLpNorm_le_of_support (Z n) K hK.measurableSet p hp _ (he n)
      (fun x i j hx => hZ0 n x i j (fun hh => hx (hχK hh))) (hValue n)
  have Hd (n : ℕ) (a : Index) : projectionMatrixLpNorm p (projectionMatrixDerivative a (Z n)) ≤
      ENNReal.ofReal C * W :=
    projectionMatrixLpNorm_le_of_support _ K hK.measurableSet p hp _ hC
      (fun x i j hx => coordinateDerivative_zero_outside (Z n i j) K
        ((hSupp n i j).trans hχK) a x hx) (hGrad n a)
  refine ⟨?_,fun n => ⟨Hv n,Hd n⟩⟩
  have hLim : Tendsto (fun n => e n * W.toReal) atTop (𝓝 0) := by
    simpa only [zero_mul] using heLim.mul_const W.toReal
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hLim
  have hm := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW).ne (Hv n)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (he n)] using hm

end Burnett.V03
