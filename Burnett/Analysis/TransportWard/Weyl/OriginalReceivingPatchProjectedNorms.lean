import Burnett.Analysis.TransportPatches.PatchProjectedLpScale
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs
import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge

set_option autoImplicit false
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.A02.FrequencySplit Burnett.P01 Burnett.C03
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Every already chosen C03 cutoff has the original physical and gauge
whole-space bounds before refinement. The exponent constants are chosen
uniformly before the patch scale. -/
theorem exists_originalReceivingPatch_projectedLp_wholeSequence
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ c.chart.target)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (hError : ∀ n x, x ∈ K → ‖metricComponents (fixedForm (g n) c) x -
      metricComponents (fixedForm B c) x‖ ≤ e n)
    (Ccut : ℕ → ℝ) (hCcut : ∀ k, 0 ≤ Ccut k) :
    ∃ Cp : {p : ℝ // 1 < p} → ℝ, (∀ p, 0 ≤ Cp p) ∧
      ∀ ℓ : ℝ, 0 < ℓ → ∀ (x₀ : E) (d : D) (hd : tsupport (d : E → ℝ) ⊆ c.chart.target),
      tsupport (d : E → ℝ) ⊆ closedBall x₀ (4 * ℓ) →
      closedBall x₀ (6 * ℓ) ⊆ K →
      (∀ k x, ‖iteratedFDeriv ℝ k (d : E → ℝ) x‖ ≤ Ccut k * ℓ⁻¹ ^ k) →
      ∀ n p, ProjectedPatchLpBounds p.val (receivingCutoffFluctuation B g hB hg c d hd n)
        (closedBall x₀ (6 * ℓ)) (Cp p * e n) (Cp p * (1 + e n / ℓ)) := by
  classical
  let G (n : ℕ) := metricComponents (fixedForm (g n) c)
  let G₀ := metricComponents (fixedForm B c)
  obtain ⟨J, hJ, hJet⟩ := Burnett.Microlocal.AtlasVolumeGradient.fixedJet_uniform_bound_on_compact
    r B g hB hg hn hconv hb c hK hKU
  obtain ⟨H, H₀, hH, hH₀, agrees, agrees₀⟩ := exists_openChartMetricRepresentatives
    hK c.chart.open_target hKU G G₀
    (fun n => fixedForm_components_smooth (g n) (hg n) c) (fixedForm_components_smooth B hB c)
  have hJetEq (f F : E → Tensor2) (x : E) (hf : F =ᶠ[𝓝 x] f) : coordinateJet F x = coordinateJet f x := by
    funext a i j
    change fderiv ℝ (fun y => F y i j) x (EuclideanSpace.single a 1) =
      fderiv ℝ (fun y => f y i j) x (EuclideanSpace.single a 1)
    have h : (fun y => F y i j) =ᶠ[𝓝 x] fun y => f y i j :=
      hf.mono fun _ hy => congrArg (fun t : Tensor2 => t i j) hy
    rw [h.fderiv_eq]
  have hData (n : ℕ) (x : E) (hx : x ∈ K) :
      ‖H n x - H₀ x‖ ≤ e n ∧ ‖coordinateJet (H n) x - coordinateJet H₀ x‖ ≤ J := by
    have hG := (agrees n).filter_mono (nhds_le_nhdsSet hx)
    have hG₀ := agrees₀.filter_mono (nhds_le_nhdsSet hx)
    refine ⟨by simpa only [hG.eq_of_nhds, hG₀.eq_of_nhds] using hError n x hx, ?_⟩
    rw [hJetEq _ _ x hG, hJetEq _ _ x hG₀,
      ← coordinateJet_sub (G n) G₀ x
        (fun i j => ((fixedForm_components_smooth (g n) (hg n) c i j).differentiableOn
          (by decide) x (hKU hx)).differentiableAt (c.chart.open_target.mem_nhds (hKU hx)))
        (fun i j => ((fixedForm_components_smooth B hB c i j).differentiableOn
          (by decide) x (hKU hx)).differentiableAt (c.chart.open_target.mem_nhds (hKU hx)))]
    exact hJet n x hx
  choose Bp hBp hLp using fun p : {p : ℝ // 1 < p} => exists_projectedPatchLp_scale p.val p.property
  let D₀ := Ccut 0 + Ccut 0 * J + Ccut 1
  have hD₀ : 0 ≤ D₀ := add_nonneg (add_nonneg (hCcut 0) (mul_nonneg (hCcut 0) hJ)) (hCcut 1)
  refine ⟨fun p => Bp p * D₀, fun p => mul_nonneg (hBp p) hD₀, ?_⟩
  intro ℓ hℓ x₀ d hd hdS hIn hCuts n p
  let W := closedBall x₀ (6 * ℓ)
  have hdW : tsupport (d : E → ℝ) ⊆ W := hdS.trans (closedBall_subset_closedBall (by linarith))
  have hχ₀ (x : E) (_ : x ∈ tsupport (d : E → ℝ)) : ‖(d : E → ℝ) x‖ ≤ Ccut 0 := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hCuts 0 x
  have hχ₁ (x : E) (_ : x ∈ tsupport (d : E → ℝ)) :
      ‖iteratedFDeriv ℝ 1 (d : E → ℝ) x‖ ≤ Ccut 1 * ℓ⁻¹ := by
    simpa only [pow_one] using hCuts 1 x
  have hRaw : localizedMetricSchwartz (H n) H₀ d (test_smooth d) (test_compactSupport d) (hH n) hH₀ =
      receivingCutoffFluctuation B g hB hg c d hd n := by
    funext i j
    ext x
    change Complex.ofReal ((d : E → ℝ) x * (H n x i j - H₀ x i j)) =
      Complex.ofReal ((d : E → ℝ) x * (G n x i j - G₀ x i j))
    by_cases hx : x ∈ tsupport (d : E → ℝ)
    · have hxK := hIn (hdW hx)
      rw [((agrees n).filter_mono (nhds_le_nhdsSet hxK)).eq_of_nhds,
        (agrees₀.filter_mono (nhds_le_nhdsSet hxK)).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hBound := hLp p (H n) H₀ (hH n) hH₀ d (test_smooth d) (test_compactSupport d) W
    (isCompact_closedBall _ _) hdW (Ccut 0) (Ccut 1 * ℓ⁻¹) J (e n) (hCcut 0)
    (mul_nonneg (hCcut 1) (inv_nonneg.mpr hℓ.le)) hJ (he n) hχ₀ hχ₁
    (fun x hx => hData n x (hIn (hdW hx)))
  dsimp only at hBound
  rw [hRaw] at hBound
  have hN₀ : Ccut 0 ≤ D₀ := by dsimp only [D₀]; linarith [mul_nonneg (hCcut 0) hJ, hCcut 1]
  have hN₁ : Ccut 0 * J ≤ D₀ := by dsimp only [D₀]; linarith [hCcut 0, hCcut 1]
  have hN₂ : Ccut 1 ≤ D₀ := by dsimp only [D₀]; linarith [hCcut 0, mul_nonneg (hCcut 0) hJ]
  have hSecond : Ccut 0 * J + Ccut 1 * ℓ⁻¹ * e n ≤ D₀ * (1 + e n / ℓ) := by
    have hScale : Ccut 1 * ℓ⁻¹ * e n = Ccut 1 * (e n / ℓ) := by rw [div_eq_mul_inv]; ring
    rw [mul_add, mul_one, hScale]
    exact add_le_add hN₁ (mul_le_mul_of_nonneg_right hN₂ (div_nonneg (he n) hℓ.le))
  apply ProjectedPatchLpBounds.mono hBound
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN₀ (he n)) (hBp p)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hSecond (hBp p)

end Burnett.V03
