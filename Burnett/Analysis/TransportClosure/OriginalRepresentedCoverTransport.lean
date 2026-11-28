import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude
import Burnett.Analysis.TransportClosure.OriginalTransportFromLocalBounds

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option maxRecDepth 3900

noncomputable section

namespace Burnett.C04

open Filter Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitNullCompactness CotangentAngularExtension
open Burnett.Geometry.UnitCosphere (Cosphere projection coe_mem_punctured hamiltonian antipode)
open Burnett.Geometry.CotangentTests (exists_finite_smooth_cutoffs_on_compact)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [T2Space M]

private theorem transport_odd_of_subordinate_chart_cover {ι : Type*}
    (U : ι → Set M) (c : ι → M) (hOpen : ∀ i, IsOpen (U i))
    (hChart : ∀ i, U i ⊆ (chartAt E (c i)).source) (hCover : (⋃ i, U i) = univ)
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (hs : IsSymmetric B) (μ : Measure (Cosphere r))
    (hIntegrable : ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hn a p.val) μ)
    (hLocal : ∀ i a, IsDegreeOneTransportTest a → IsAntipodallyOdd a → HasCompactTransportBaseSupportIn a (U i) →
      ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E (c i)).source},
        chartHamiltonDerivative (c i) B hn a p.val ∂μ = 0) :
    ∀ a, IsDegreeOneTransportTest a → IsAntipodallyOdd a →
      (∫ p : Cosphere r, basePointHamiltonDerivative B hn a p.val ∂μ) = 0 := by
  intro a ha ho
  obtain ⟨K, hK, hzero⟩ := ha.2.2
  have hKC : K ⊆ ⋃ i, U i := by rw [hCover]; exact subset_univ _
  obtain ⟨n, i, ρ, V, _, hKV, hρ, hsum⟩ := exists_finite_smooth_cutoffs_on_compact U hOpen hK hKC
  let aᵢ (k : Fin n) := localizeTransportTest (ρ k) a
  have hTest (k : Fin n) : IsDegreeOneTransportTest (aᵢ k) :=
    ha.localize (hρ k).1 (hρ k).2.1
  have hOne (k : Fin n) : HasCompactTransportBaseSupportIn (aᵢ k) (U (i k)) :=
    hasCompactTransportBaseSupportIn_localize a (hρ k).2.1 (hρ k).2.2.1
  have hE : ∀ p ∈ puncturedCotangent, a p = ∑ k, aᵢ k p := by
    intro p hp
    simp only [aᵢ, localizeTransportTest, ← Finset.sum_mul]
    by_cases h : p.proj ∈ K
    · rw [hsum p.proj (hKV h), one_mul]
    · rw [hzero p hp h, mul_zero]
  have hSum (p : Cosphere r) :
      basePointHamiltonDerivative B hn a p.val = ∑ k, basePointHamiltonDerivative B hn (aᵢ k) p.val :=
    basePointHamiltonDerivative_eq_sum_of_punctured B hn a aᵢ ha.1 (fun k => (hTest k).1)
      hE p.val (coe_mem_punctured r p)
  calc
    _ = ∫ p : Cosphere r, ∑ k, basePointHamiltonDerivative B hn (aᵢ k) p.val ∂μ :=
      integral_congr_ae (ae_of_all μ hSum)
    _ = ∑ k, ∫ p : Cosphere r, basePointHamiltonDerivative B hn (aᵢ k) p.val ∂μ :=
      integral_finset_sum Finset.univ (fun k _ => hIntegrable (aᵢ k) (hTest k))
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      obtain ⟨J, hJ, hJU, hz⟩ := hOne k
      have hSupp : HasCompactTransportBaseSupportIn (aᵢ k) (chartAt E (c (i k))).source :=
        ⟨J, hJ, hJU.trans (hChart (i k)), hz⟩
      rw [integral_basePointHamiltonDerivative_eq_chart_restrict r B hB hn hs μ (c (i k))
        (aᵢ k) (hTest k).1 hSupp]
      exact hLocal (i k) (aᵢ k) (hTest k) (ho.localize (ρ k)) (hOne k)

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The actual original represented cover supplies both the gradient and
projected matrix pairings on the single extracted subsequence. It suffices
to prove the two-scale estimate on that cover for the same physical measure. -/
theorem originalTransport_of_representedCover_twoScale_bounds
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (hNull : μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hBound : ∀ (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
      (hf : ∀ v, IsFiniteMeasure (ν v)),
      RepresentsCompactJetPairings q.ball
        (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)) σ ν hf →
      Burnett.P01.RepresentsVolumeProjectedPairings B g q σ ν hf →
      ∀ a : CotangentBundle M → ℝ, IsDegreeOneTransportTest a → IsAntipodallyOdd a →
      HasCompactTransportBaseSupportIn a (q.cutoffLocusAbove (1 / 2)) →
      let I := ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E q.center).source},
        chartHamiltonDerivative q.center B hSig.isNondegenerate a p.val ∂μ
      ∃ C α β δ₀ : ℝ, 0 < α ∧ 0 < β ∧ 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ D F ℓ₀ : ℝ, 0 < ℓ₀ ∧
          ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → |4 * I| ≤ C * δ ^ β + D * ℓ ^ α + F * ℓ) :
    ∀ a, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative B hSig.isNondegenerate a p.val) μ ∧
        (∫ p : Cosphere r, basePointHamiltonDerivative B hSig.isNondegenerate a p.val ∂μ) = 0 := by
  let hn := hSig.isNondegenerate
  let hs := hSig.isSymmetric
  have hEven := originalIntrinsicPhysicalContraction_antipodal
    r B g hB hg hSig hsG hnG hconv hb hv σ hσ A μ hA hPhysical
  have hInt := integrable_basePointHamiltonDerivative r B hB hn hs μ hNull hFinite
  apply transport_of_oddTests_of_antipodalMeasure r B hn μ hEven ?_ hInt
  by_cases hM : Nonempty M
  · obtain ⟨q, hCover, ν, hf, hRep⟩ := hA.1 hM
    let U (i : ℕ) := (q i).cutoffLocusAbove (1 / 2)
    have hOpen (i : ℕ) : IsOpen (U i) := (q i).isOpen_cutoffLocusAbove (1 / 2)
    have hChart (i : ℕ) : U i ⊆ (chartAt E (q i).center).source := by
      intro x hx
      exact ((q i).cutoffLocusAbove_subset_nonzeroLocus (by norm_num) hx).1
    apply transport_odd_of_subordinate_chart_cover U (fun i => (q i).center) hOpen hChart hCover
      r B hB hn hs μ hInt
    intro i a ha ho hSupp
    have h := hBound (q i) (ν i) (hf i) (hRep i).1 (hRep i).2 a ha ho hSupp
    obtain ⟨C, α, β, δ₀, hα, hβ, hδ, hTail⟩ := h
    exact residual_eq_zero_of_two_scale_bound _ C α β δ₀ hα hβ hδ hTail
  · exact transport_of_chartwise_oddTests r B hB hn hs μ
      (fun c => (hM ⟨c⟩).elim) hInt

end Burnett.C04
