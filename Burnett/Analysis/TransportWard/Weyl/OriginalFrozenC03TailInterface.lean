import Burnett.Analysis.TransportWard.Weyl.OriginalChartTransportSymbol
import Burnett.Analysis.TransportWard.Weyl.OriginalReceivingPatchCubicBudget
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFixedTestWindow
import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalCorrectionSuppliedChartPatches

set_option autoImplicit false

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference InverseField ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension Burnett.C01 Burnett.C02 Burnett.C03 Burnett.C04
open Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.P01
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Matrix.Norms.Elementwise Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [SecondCountableTopology M]

def HasOriginalFrozenC03Tail
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (σ : ℕ → ℕ) (c₀ : M) (f : CotangentBundle M → ℝ) : Prop :=
  let c := AtlasChart.atPoint c₀
  let a (x ξ : E) := originalChartTransportSymbol c₀ f x (WithLp.ofLp ξ)
  let β (x ξ : E) := fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ
  ∀ K V : Set E, IsCompact K → IsCompact V → K ⊆ V → Convex ℝ V → V ⊆ c.chart.target →
    ∀ (e : ℕ → ℝ), (∀ n, 0 ≤ e n) → Tendsto e atTop (𝓝 0) →
      (∀ n x, x ∈ K → ‖metricComponents (fixedForm (g n) c) x -
        metricComponents (fixedForm B c) x‖ ≤ e n) →
      ∀ (Msrc Ccoeff : ℝ) (Ccut : ℕ → ℝ) (Cp : {p : ℝ // 1 < p} → ℝ),
        0 ≤ Msrc → 0 ≤ Ccoeff → (∀ k, 0 ≤ Ccut k) → (∀ p, 0 ≤ Cp p) →
        ∃ Cnear α ν δ₀ : ℝ, 0 < α ∧ 0 < ν ∧ 0 < δ₀ ∧
          ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ R G ℓ₀ : ℝ, 0 < ℓ₀ ∧
            ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → ∀ (s : Finset LatticeIndex) (d : LatticeIndex → D)
              (ψ : LatticeIndex → E → ℝ) (hd : ∀ j, tsupport (d j : E → ℝ) ⊆ c.chart.target),
              let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
              let z (n : ℕ) (j : LatticeIndex) := receivingCubicPatchField B g hB hg c (d j) (hd j) (σ n)
              (∀ j ∈ s, ContDiff ℝ ∞ (ψ j) ∧ (∀ x, 0 ≤ (d j : E → ℝ) x ∧ ψ j x ∈ Icc (0 : ℝ) 1) ∧
                tsupport (d j : E → ℝ) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧ tsupport (ψ j) ⊆ P j ∧
                P j ⊆ interior K ∧ (∀ x ∈ thickening ℓ (tsupport (d j : E → ℝ)), ψ j x = 1) ∧
                ∀ k x, ‖iteratedFDeriv ℝ k (d j : E → ℝ) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
                  ‖iteratedFDeriv ℝ k (ψ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k) →
              (∀ j ∈ s, ∀ᶠ n in atTop,
                let m := chartInverseMetric B c (patchCenter ℓ j)
                let u (i k : Index) := (z n j).val (i,k)
                ∃ (a : ProjectedSourceCoefficients) (v : Index → Index → SchwartzMap E ℝ),
                  (∀ i k x, a.entry i k x = ((m i k + v i k x : ℝ) : ℂ)) ∧
                  (∀ i k x, v i k x = correctionCoefficientPart (ψ j)
                    (matrixInverse ∘ metricComponents (fixedForm (g (σ n)) c)) m x i k) ∧
                  (∀ i k, v i k = v k i) ∧
                  (∀ i k x, |v i k x| ≤ Ccoeff * (ℓ + e (σ n))) ∧
                  (∀ i k x, ‖fderiv ℝ (v i k : E → ℝ) x‖ ≤ 4 * Ccoeff * (1 + e (σ n) / ℓ)) ∧
                  ‖projectedSourceDivergenceL2 a (projectionFullSchwartz u)‖ ≤
                    Msrc * (volume (P j) ^ ((1 : ℝ) / 2)).toReal *
                      (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n)) ∧
                  ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val u (P j)
                    (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ))) →
              (∑ j ∈ s, (volume : Measure E) (P j)) ≤ ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume K →
              let frozen (n : ℕ) (j : LatticeIndex) :=
                let x := patchCenter ℓ j
                let G₀ := metricComponents (fixedForm B c) x
                completeCubicEnergy (frozenActionCubicLinear G₀) (frozenActionCubicQuadratic G₀) (β x) (z n j)
              ∀ ε > 0, ∀ᶠ n in atTop, (∑ j ∈ s, |frozen n j|) ≤
                (Cnear * δ ^ ν + R * ℓ ^ α + G * ℓ) * ((17 ^ 4 : ℝ) * (volume K).toReal) + ε

end Burnett.V03.Palatini
