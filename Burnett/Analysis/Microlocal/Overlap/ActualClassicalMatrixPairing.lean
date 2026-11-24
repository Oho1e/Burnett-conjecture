import Burnett.Analysis.Microlocal.Overlap.LocalClassicalPuncturedPrincipal

/-! Actual finite matrix tests of the original receiving-chart gradients. -/

set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 1900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere)
open FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

/-- Insert input `j` and read output `i` of the same bounded matrix operator. -/
def classicalJetOperatorEntry
    (T : (JetSlot → ComplexL2 E) →L[ℂ] (JetSlot → ComplexL2 E)) (i j : JetSlot) :
      ComplexL2 E →L[ℂ] ComplexL2 E :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : JetSlot => ComplexL2 E) i).comp T).comp
    (ContinuousLinearMap.single ℂ (fun _ : JetSlot => ComplexL2 E) j)

theorem classicalJetOperatorEntry_sum
    (T : (JetSlot → ComplexL2 E) →L[ℂ] (JetSlot → ComplexL2 E))
    (u : JetSlot → ComplexL2 E) (i : JetSlot) :
    (∑ j, classicalJetOperatorEntry T i j (u j)) = (T u) i :=
  ContinuousLinearMap.sum_comp_single ℂ (fun _ : JetSlot => ComplexL2 E)
    ((ContinuousLinearMap.proj i).comp T) u

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- The pairing for a matrix of full symbols on the open receiving chart. All entries
use the same refinement, actual operator, two cutoffs, and covariance. -/
theorem tendsto_originalVolume_receivingClassicalFullMatrixPairing
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingPaperPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (T : (JetSlot → ComplexL2 E) →L[ℂ] (JetSlot → ComplexL2 E))
    (b a : JetSlot → JetSlot → E → E → ℂ)
    (hbDiff : ∀ i j, ContDiffOn ℝ ∞ (uncurry (b i j)) (c.chart.target ×ˢ univ))
    (haDiff : ∀ i j, ContDiffOn ℝ ∞ (uncurry (a i j)) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ i j x, x ∈ c.chart.target → ∀ (s : ℝ), 0 < s → ∀ ξ : E,
      ξ ≠ 0 → a i j x (s • ξ) = a i j x ξ)
    (hLarge : ∀ i j (S : Set E), IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => b i j y ξ - a i j y ξ) x‖ ≤ C)
    (hAct : ∀ i j (f v : SchwartzMap E ℂ), tsupport (f : E → ℂ) ⊆ c.chart.target →
      tsupport (v : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) →
      inner ℂ (f.toLp 2 volume) (classicalJetOperatorEntry T i j (v.toLp 2 volume)) =
        classicalLeftPairing (b i j) f v) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeGradientSchwartz B g hB hg hn c η₀ h₀c
    let v := fixedVolumeGradientSchwartz B g hB hg hn c η₁ h₁c
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let G (p : Cosphere r) :=
      let z := fixedChartPhase c p.val
      ∑ i : JetSlot, ∑ j : JetSlot,
        conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a i j z.1 (WithLp.toLp 2 z.2)) *
          atlasOrderedJetEntry c A.density p j i
    Integrable G τ ∧ Tendsto (fun n => ∑ i : JetSlot,
      inner ℂ ((T (fun j => (v (σ n) j).toLp 2 volume)) i) ((u (σ n) i).toLp 2 volume))
      atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro h₀c h₁c u v τ G
  let F (i j : JetSlot) (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a i j z.1 (WithLp.toLp 2 z.2)) *
      atlasOrderedJetEntry c A.density p j i
  have hEntry (i j : JetSlot) : Integrable (F i j) τ ∧
      Tendsto (fun n => inner ℂ (classicalJetOperatorEntry T i j ((v (σ n) j).toLp 2 volume))
        ((u (σ n) i).toLp 2 volume)) atTop (𝓝 (∫ p, F i j p ∂τ)) :=
    tendsto_originalVolume_receivingLocalFullPairing_of_puncturedPrincipal r B g hB hg hn σ A hPair c K hK hKc
      η₀ η₁ h₀ h₁ (classicalJetOperatorEntry T i j) (b i j) (a i j) (hbDiff i j) (haDiff i j)
      (hDegree i j) (hLarge i j) (hAct i j) i j
  have hRow (i : JetSlot) : Integrable (fun p => ∑ j : JetSlot, F i j p) τ :=
    integrable_finset_sum _ (fun j _ => (hEntry i j).1)
  refine ⟨integrable_finset_sum _ (fun i _ => hRow i), ?_⟩
  have hInt : (∫ p, G p ∂τ) = ∑ i : JetSlot, ∑ j : JetSlot, ∫ p, F i j p ∂τ :=
    (integral_finset_sum _ (fun i _ => hRow i)).trans
      (Finset.sum_congr rfl (fun i _ => integral_finset_sum _ (fun j _ => (hEntry i j).1)))
  rw [hInt]
  apply (tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun j _ => (hEntry i j).2))).congr
  intro n
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_inner, classicalJetOperatorEntry_sum T (fun j => (v (σ n) j).toLp 2 volume) i]

end Burnett.Microlocal.Overlap
