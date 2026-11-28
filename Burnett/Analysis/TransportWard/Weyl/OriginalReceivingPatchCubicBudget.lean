import Burnett.Analysis.TransportWard.Weyl.OriginalPatchWeylFreezingSum
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.A02.FrequencySplit Burnett.P01 Burnett.C02
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The unprojected C03 patch data as a real cubic-energy field. -/
def receivingCubicPatchField
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (d : D) (hd : tsupport (d : E → ℝ) ⊆ c.chart.target) (n : ℕ) : RealEnergyField OrderedPair :=
  ⟨fun i => receivingCutoffFluctuation B g hB hg c d hd n i.1 i.2,
    fun _ _ => Complex.conj_ofReal _⟩

/-- Original cutoff value and first-jet bounds provide the uniform patch
volume scale needed for coefficient and test freezing. The constants
are selected before the patch size and the receiving cutoff. -/
theorem exists_receivingCubicPatch_volume_budget
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ c.chart.target)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hLim : Tendsto e atTop (𝓝 0))
    (hError : ∀ n x, x ∈ K → ‖metricComponents (fixedForm (g n) c) x -
      metricComponents (fixedForm B c) x‖ ≤ e n)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (ℓ : ℝ), 0 < ℓ →
      ∀ (x₀ : E) (d : D) (hd : tsupport (d : E → ℝ) ⊆ c.chart.target),
        tsupport (d : E → ℝ) ⊆ closedBall x₀ (4 * ℓ) →
        closedBall x₀ (6 * ℓ) ⊆ K →
        (∀ x ∈ tsupport (d : E → ℝ), ‖(d : E → ℝ) x‖ ≤ C) →
        (∀ x ∈ tsupport (d : E → ℝ), ‖iteratedFDeriv ℝ 1 (d : E → ℝ) x‖ ≤ L * ℓ⁻¹) →
        let z (n : ℕ) := receivingCubicPatchField B g hB hg c d hd (σ n)
        (∀ n, tsupport (fieldValueArray (z n).val) ⊆ closedBall x₀ (4 * ℓ)) ∧
        Tendsto (fun n => euclideanFieldValueL3 (z n).val) atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, euclideanFieldGradientL3 (z n).val ≤
          R * ((volume : Measure E) (closedBall x₀ (6 * ℓ))).toReal ^ (1 / 3 : ℝ) := by
  let G (n : ℕ) := metricComponents (fixedForm (g n) c)
  let G₀ := metricComponents (fixedForm B c)
  obtain ⟨D₀, hD₀, hD⟩ := Burnett.Microlocal.AtlasVolumeGradient.fixedJet_uniform_bound_on_compact
    r B g hB hg hn hconv hb c hK hKU
  have hDiff (n : ℕ) (x : E) (hx : x ∈ K) :
      ‖coordinateJet (G n) x - coordinateJet G₀ x‖ ≤ D₀ := by
    rw [← coordinateJet_sub (G n) G₀ x
      (fun i j => ((fixedForm_components_smooth (g n) (hg n) c i j).differentiableOn
        (by decide) x (hKU hx)).differentiableAt (c.chart.open_target.mem_nhds (hKU hx)))
      (fun i j => ((fixedForm_components_smooth B hB c i j).differentiableOn
        (by decide) x (hKU hx)).differentiableAt (c.chart.open_target.mem_nhds (hKU hx)))]
    exact hD n x hx
  refine ⟨64 * (C * D₀ + L), by positivity, ?_⟩
  intro ℓ hℓ x₀ d hd hSmall hIn hValue hJet z
  let P := closedBall x₀ (6 * ℓ)
  let v (n : ℕ) : ProjectionSchwartzMatrix := receivingCutoffFluctuation B g hB hg c d hd (σ n)
  have hv (n : ℕ) (i j : Index) (x : E) :
      v n i j x = ((d : E → ℝ) x * (G (σ n) x i j - G₀ x i j) : ℝ) := rfl
  have hDP : tsupport (d : E → ℝ) ⊆ P := hSmall.trans (closedBall_subset_closedBall (by linarith))
  let V := ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hBounds (n : ℕ) :
      euclideanFieldValueL3 (z n).val ≤ 16 * (C * e (σ n)) * V ∧
      euclideanFieldGradientL3 (z n).val ≤ 64 * (C * D₀ + L * ℓ⁻¹ * e (σ n)) * V :=
    originalRawPatch_euclideanLp_of_C03 c.chart.open_target (isCompact_closedBall _ _) (hIn.trans hKU)
      (G (σ n)) G₀ (fixedForm_components_smooth (g (σ n)) (hg (σ n)) c) (fixedForm_components_smooth B hB c)
      d (test_smooth d) (test_compactSupport d) hDP (v n) (hv n) C (L * ℓ⁻¹) D₀ (e (σ n))
      hC (mul_nonneg hL (inv_nonneg.mpr hℓ.le)) hD₀ (he (σ n)) hValue hJet
      (fun x hx => ⟨hError (σ n) x (hIn (hDP hx)), hDiff (σ n) x (hIn (hDP hx))⟩)
  refine ⟨fun n => (fieldValueArray_tsupport_of_original_raw_patch (v n) d (G (σ n)) G₀
    (hv n)).trans hSmall, ?_, ?_⟩
  · refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => (hBounds n).1) ?_
    simpa only [Function.comp_apply, mul_zero, zero_mul] using
      ((((hLim.comp hσ.tendsto_atTop).const_mul C).const_mul (16 : ℝ)).mul_const V)
  · filter_upwards [hσ.tendsto_atTop.eventually ((tendsto_order.1 hLim).2 ℓ hℓ)] with n hn'
    have hTail : L * ℓ⁻¹ * e (σ n) ≤ L := calc
      _ ≤ L * ℓ⁻¹ * ℓ := mul_le_mul_of_nonneg_left hn'.le (mul_nonneg hL (inv_nonneg.mpr hℓ.le))
      _ = L := by rw [mul_assoc, inv_mul_cancel₀ hℓ.ne', mul_one]
    exact (hBounds n).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_left hTail _) (by norm_num)) hV)

end Burnett.V03
