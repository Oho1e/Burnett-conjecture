import Burnett.Analysis.Microlocal.Overlap.RepresentedNormalizedProducts
import Burnett.Analysis.Microlocal.OrderedRicciJet
import Burnett.Analysis.RawConnectionWeakRicci
import Burnett.Geometry.AuxiliaryAdmissibility
import Burnett.Geometry.IntrinsicRicciTrace

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.Analysis.LocalWeakRicciIdentification (coordinateMeasure_test_integrable)
open Burnett.Analysis.PartialJetReplacement
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open ManifoldMetricSequence BackgroundConnection CurvatureDifference InverseField
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.RawCovariance
open Burnett.X02.SobolevTestJet (D Space test_smooth test_compactSupport)
open scoped BigOperators ContDiff Topology Manifold

private theorem contDiffOn_connectionProductCoefficient
    (G : Space → Tensor2) (U : Set Space)
    (hG : ∀ a e, ContDiffOn ℝ ∞ (fun x => G x a e) U)
    (b d : Index) (i j : JetSlot) :
    ContDiffOn ℝ ∞ (fun x => rawJetProductCoefficient (G x) b d i j) U := by
  have hC (J : FirstJet) (a b d : Index) :
      ContDiffOn ℝ ∞ (fun x => christoffel (G x) J a b d) U := by
    unfold christoffel
    exact ContDiffOn.sum (fun e _ => (hG a e).mul contDiffOn_const)
  unfold rawJetProductCoefficient rawJetCross
  exact ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun e _ =>
    ((hC (jetBasis i) a d e).mul (hC (jetBasis j) e b a)).sub
      ((hC (jetBasis i) a a e).mul (hC (jetBasis j) e b d))))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Identify the normalized original jet density tested against the negative
connection product with the weak Ricci limit on the same original subsequence. -/
theorem original_Ricci_eq_normalized_jetContraction
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (ψ : D) (hψ : tsupport (ψ : Space → ℝ) ⊆ {x | (q.cutoff : Space → ℝ) x ≠ 0})
    (b d : Index) :
    let G := fun x => matrixInverse (metricComponents (coordinateBilinear B q.center) x)
    (∫ x, (ψ : Space → ℝ) x * coordinateRicci (computedConnection (coordinateBilinear B q.center)) x b d
        ∂ManifoldVolume.coordinateMeasure B q.center) =
    ∫ z, ∑ i : JetSlot, ∑ j : JetSlot,
      (((ψ : Space → ℝ) z.1 * rawJetProductCoefficient (G z.1) b d i j) *
        ((q.cutoff : Space → ℝ) z.1 ^ 2)⁻¹) * (density ν hf z i j).re ∂traceMeasure ν := by
  intro G
  let U := (chartAt CoordinateSpace q.center).target
  let V := ManifoldVolume.coordinateMeasure B q.center
  let J (n : ℕ) (x : Space) := coordinateJet (fun y =>
    metricComponents (coordinateBilinear (g n) q.center) y -
      metricComponents (coordinateBilinear B q.center) y) x
  have hU : IsOpen U := (chartAt CoordinateSpace q.center).open_target
  have hψU : tsupport (ψ : Space → ℝ) ⊆ U :=
    fun x hx => q.ball_in_chart (q.cutoff_support (subset_tsupport _ (hψ hx)))
  have hG (a e : Index) : ContDiffOn ℝ ∞ (fun x => G x a e) U :=
    SmoothMetricConnection.contDiffOn_matrixInverse
      (metricComponents (coordinateBilinear B q.center)) U
      (ManifoldBilinear.contDiffOn_metricComponents B hB q.center)
      (fun x hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hnB q.center hx) a e
  let W (i j : JetSlot) : D :=
    ⟨fun x => (ψ : Space → ℝ) x * rawJetProductCoefficient (G x) b d i j,
      contDiff_test_mul_local hU (test_smooth ψ) hψU
        (contDiffOn_connectionProductCoefficient G U hG b d i j), (test_compactSupport ψ).mul_right⟩
  have hSupport (i j : JetSlot) : tsupport (W i j : Space → ℝ) ⊆ tsupport (ψ : Space → ℝ) :=
    tsupport_mul_subset_left
  have hJ (n : ℕ) (i : JetSlot) : ContDiffOn ℝ ∞ (fun x => jetEntries (J n x) i) U := by
    have hH (a e : Index) := (ManifoldBilinear.contDiffOn_metricComponents (g n) (hg n) q.center a e).sub
      (ManifoldBilinear.contDiffOn_metricComponents B hB q.center a e)
    exact SmoothMetricConnection.contDiffOn_coordinateJet _ U hU hH i.1 i.2.1 i.2.2
  let baseTerm (n : ℕ) (i j : JetSlot) (x : Space) :=
    (W i j : Space → ℝ) x * (jetEntries (J n x) i * jetEntries (J n x) j)
  let phaseTerm (i j : JetSlot) (z : Chart q.ball) :=
    ((W i j : Space → ℝ) z.1 * ((q.cutoff : Space → ℝ) z.1 ^ 2)⁻¹) * (density ν hf z i j).re
  have hBase (n : ℕ) (i j : JetSlot) : Integrable (baseTerm n i j) V :=
    coordinateMeasure_test_integrable B hB q.center (test_smooth (W i j)) (test_compactSupport (W i j))
      ((hSupport i j).trans hψU) ((hJ n i).mul (hJ n j))
  have hPhase (i j : JetSlot) := original_products_of_represented_on_nonzero_cutoff
    B g hB hg hnB q σ ν hf hRep (W i j) ((hSupport i j).trans hψ) i j
  have hWeak := (vacuum_Ricci_raw_coordinateMeasure_limit_of_original
    r B g hB hg hsB hsG hnB hnG hconv hb q.center
      (IntrinsicRicciTrace.sequence_coordinateVacuum_of_intrinsic g hg hsG hnG hv q.center)
      b d (test_smooth ψ) (test_compactSupport ψ) hψU).2.2.comp hσ.tendsto_atTop
  have hFromProduct : Tendsto (fun n => ∑ i : JetSlot, ∑ j : JetSlot, ∫ x, baseTerm (σ n) i j x ∂V)
      atTop (𝓝 (∑ i : JetSlot, ∑ j : JetSlot, ∫ z, phaseTerm i j z ∂traceMeasure ν)) :=
    tendsto_finset_sum Finset.univ fun i _ =>
      tendsto_finset_sum Finset.univ fun j _ => (hPhase i j).2
  have hBaseEq (n : ℕ) (x : Space) :
      (ψ : Space → ℝ) x * (-quadraticDifference (christoffel (G x) (J n x)) b d) =
        ∑ i : JetSlot, ∑ j : JetSlot, baseTerm n i j x := by
    rw [← rawJetCross_diag, rawJetCross_eq_jet_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [baseTerm, W, mul_assoc]
  have hBaseIntegral (n : ℕ) :
      (∫ x, (ψ : Space → ℝ) x * (-quadraticDifference (christoffel (G x) (J n x)) b d) ∂V) =
        ∑ i : JetSlot, ∑ j : JetSlot, ∫ x, baseTerm n i j x ∂V := by
    simp only [hBaseEq]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hBase n i j)]
    exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ fun j _ => hBase n i j)
  have hPhaseIntegral :
      (∫ z, ∑ i : JetSlot, ∑ j : JetSlot, phaseTerm i j z ∂traceMeasure ν) =
        ∑ i : JetSlot, ∑ j : JetSlot, ∫ z, phaseTerm i j z ∂traceMeasure ν := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => (hPhase i j).1)]
    exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ fun j _ => (hPhase i j).1)
  exact (tendsto_nhds_unique hWeak (hFromProduct.congr fun n => (hBaseIntegral (σ n)).symm)).trans
    hPhaseIntegral.symm

end Burnett.Microlocal.Overlap
