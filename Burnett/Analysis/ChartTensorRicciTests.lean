import Burnett.Geometry.ContravariantTensor
import Burnett.Analysis.MeasureWeakRicci
import Burnett.Analysis.Sobolev.TestJet

/-! Transport coordinate Ricci moments to genuine contravariant tensor tests on a chart. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Burnett.Analysis.ChartTensorRicciTests

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open BackgroundConnection CurvatureDifference ContravariantTensor UnitNullCompactness
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.Analysis.LocalWeakRicciIdentification (coordinateRicci_component_smoothOn)
open Burnett.X02.SobolevTestJet (D Space)
open scoped BigOperators ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private def coordinateTest (c : M) (φ : M → ℝ) : Space → ℝ :=
  (chartAt CoordinateSpace c).target.indicator (φ ∘ (chartAt CoordinateSpace c).symm)

private theorem coordinateTest_properties (c : M) (φ : M → ℝ)
    (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hcφ : HasCompactSupport φ)
    (hφsrc : tsupport φ ⊆ (chartAt CoordinateSpace c).source) :
    ContDiff ℝ ∞ (coordinateTest c φ) ∧ HasCompactSupport (coordinateTest c φ) ∧
      tsupport (coordinateTest c φ) ⊆ chartAt CoordinateSpace c '' tsupport φ := by
  let e := chartAt CoordinateSpace c
  have hK : IsCompact (e '' tsupport φ) := hcφ.image_of_continuousOn (e.continuousOn.mono hφsrc)
  have hsupp : tsupport (coordinateTest c φ) ⊆ e '' tsupport φ := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    have hyt : y ∈ e.target := by
      by_contra hnot
      exact hy (indicator_of_notMem hnot _)
    refine ⟨e.symm y, subset_tsupport φ ?_, e.right_inv hyt⟩
    change coordinateTest c φ y ≠ 0 at hy
    simpa only [coordinateTest, e, indicator_of_mem hyt, Function.comp_apply] using hy
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure hsupp, hsupp⟩
  have hl : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target :=
    (hφ.contMDiffOn.comp contMDiffOn_chart_symm e.symm.mapsTo).contDiffOn
  have ht : ContDiffOn ℝ ∞ (coordinateTest c φ) e.target := hl.congr (fun y hy => indicator_of_mem hy _)
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hyt : y ∈ e.target
  · exact ht.contDiffAt (e.open_target.mem_nhds hyt)
  · have hn : y ∉ tsupport (coordinateTest c φ) := by
      intro hy
      obtain ⟨x, hx, rfl⟩ := hsupp hy
      exact hyt (e.mapsTo (hφsrc hx))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space => (0 : ℝ)) y).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The tested coordinate components give the actual tensor integral on each
preferred-chart window and its cotangent preimage. -/
theorem local_intrinsicTensor_moment_of_coordinateMoments
    (B : Field (M := M)) (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (c : M) (U : Set M) (hU : IsOpen U) (hUsrc : U ⊆ (chartAt CoordinateSpace c).source)
    (μ : Measure (CotangentBundle M))
    (hMom : ∀ ψ : D, tsupport (ψ : Space → ℝ) ⊆ chartAt CoordinateSpace c '' U → ∀ i j : Index,
      let R (y : Space) := (ψ : Space → ℝ) y *
        coordinateRicci (computedConnection (coordinateBilinear B c)) y i j
      let G (p : CotangentBundle M) := (ψ : Space → ℝ) (chartAt CoordinateSpace c p.proj) *
        (cotangentCoords c p i * cotangentCoords c p j)
      let V := ManifoldVolume.coordinateMeasure B c
      let S := (fun p : CotangentBundle M => p.proj) ⁻¹' U
      Integrable R V ∧ IntegrableOn G S μ ∧ (∫ y, R y ∂V) = ∫ p in S, G p ∂μ)
    (Q : ContravariantTwoTensor M) (hQ : IsSmoothContravariant Q)
    (φ : M → ℝ) (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hcφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    let V := ManifoldVolume.geometricMeasure B
    let S := (fun p : CotangentBundle M => p.proj) ⁻¹' U
    let F (x : M) := φ x * intrinsicTensorBase B Q x
    let G (p : CotangentBundle M) := φ p.proj * intrinsicTensorPhase Q p
    IntegrableOn F U V ∧ IntegrableOn G S μ ∧
      (∫ x in U, F x ∂V) = ∫ p in S, G p ∂μ := by
  intro V S F G
  let e := chartAt CoordinateSpace c
  let dVc := ManifoldVolume.coordinateMeasure B c
  obtain ⟨hct, hc, hts⟩ := coordinateTest_properties c φ hφ hcφ (hφU.trans hUsrc)
  have hImageTarget : e '' U ⊆ e.target := fun _ ⟨x, hx, heq⟩ => heq ▸ e.mapsTo (hUsrc hx)
  have hTestSupport : tsupport (coordinateTest c φ) ⊆ e '' U :=
    hts.trans (Set.image_mono hφU)
  let ψ (i j : Index) : D :=
    ⟨fun y => coordinateTest c φ y * contravariantComponents Q c y i j,
      contDiff_test_mul_local e.open_target hct (hTestSupport.trans hImageTarget) (hQ c i j), hc.mul_right⟩
  have hSupport (i j : Index) : tsupport (ψ i j : Space → ℝ) ⊆ e '' U :=
    tsupport_mul_subset_left.trans hTestSupport
  have hψ (i j : Index) (y : Space) (hy : y ∈ e.target) :
      (ψ i j : Space → ℝ) y = φ (e.symm y) * contravariantComponents Q c y i j := by
    change coordinateTest c φ y * contravariantComponents Q c y i j = _
    rw [coordinateTest, indicator_of_mem hy]
    rfl
  let R (i j : Index) (y : Space) := (ψ i j : Space → ℝ) y *
    coordinateRicci (computedConnection (coordinateBilinear B c)) y i j
  let P (i j : Index) (p : CotangentBundle M) := (ψ i j : Space → ℝ) (e p.proj) *
    (cotangentCoords c p i * cotangentCoords c p j)
  have hm (i j : Index) := hMom (ψ i j) (hSupport i j) i j
  have hIntR : Integrable (fun y => ∑ i, ∑ j, R i j y) dVc :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hm i j).1
  have hIntP : IntegrableOn (fun p => ∑ i, ∑ j, P i j p) S μ :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hm i j).2.1
  have hsumR : (∫ y, ∑ i, ∑ j, R i j y ∂dVc) = ∑ i, ∑ j, ∫ y, R i j y ∂dVc := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hm i j).1))]
    exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ fun j _ => (hm i j).1)
  have hsumP : (∫ p in S, ∑ i, ∑ j, P i j p ∂μ) = ∑ i, ∑ j, ∫ p in S, P i j p ∂μ := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hm i j).2.1))]
    exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ fun j _ => (hm i j).2.1)
  have hS : MeasurableSet S := continuous_cotangent_projection.measurable hU.measurableSet
  have hEqP : (fun p => ∑ i, ∑ j, P i j p) =ᵐ[μ.restrict S] G := by
    filter_upwards [ae_restrict_mem (μ := μ) hS] with p hp
    have hx : p.proj ∈ e.source := hUsrc hp
    change _ = φ p.proj * intrinsicTensorPhase Q p
    rw [intrinsicTensorPhase_eq_components Q c p hx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [P, hψ i j (e p.proj) (e.mapsTo hx), e.left_inv hx, mul_assoc]
    rfl
  have hFOn : ContinuousOn F e.source := by
    have hQOn (i j : Index) : ContinuousOn (fun x => contravariantComponents Q c (e x) i j) e.source :=
      (hQ c i j).continuousOn.comp e.continuousOn e.mapsTo
    have hROn (i j : Index) : ContinuousOn (fun x =>
        coordinateRicci (computedConnection (coordinateBilinear B c)) (e x) i j) e.source :=
      (coordinateRicci_component_smoothOn B hB hn c i j).continuousOn.comp e.continuousOn e.mapsTo
    have hBase := continuousOn_finset_sum Finset.univ (fun i _ =>
      continuousOn_finset_sum Finset.univ (fun j _ => (hQOn i j).mul (hROn i j)))
    exact hφ.continuous.continuousOn.mul
      (hBase.congr (fun x hx => intrinsicTensorBase_eq_components B hB hs hn Q c x hx))
  have hEqR : (fun y => ∑ i, ∑ j, R i j y) =ᵐ[dVc.restrict e.target]
      F ∘ ManifoldVolume.inverseChart c := by
    filter_upwards [ae_restrict_mem (μ := dVc) e.open_target.measurableSet] with y hy
    change _ = F (ManifoldVolume.inverseChart c y)
    rw [ManifoldVolume.inverseChart_of_mem c hy]
    change _ = φ (e.symm y) * intrinsicTensorBase B Q (e.symm y)
    rw [intrinsicTensorBase_eq_components B hB hs hn Q c (e.symm y) (e.symm_mapsTo hy),
      show chartAt CoordinateSpace c (e.symm y) = y from e.right_inv hy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [R, hψ i j y hy, mul_assoc]
  have hMap : V.restrict e.source = (dVc.restrict e.target).map (ManifoldVolume.inverseChart c) :=
    ManifoldVolume.geometricMeasure_restrict B c
  have hMeas := hFOn.aestronglyMeasurable (μ := V) e.open_source.measurableSet
  rw [hMap] at hMeas
  have hMeasMap : AEMeasurable (ManifoldVolume.inverseChart c) (dVc.restrict e.target) :=
    (ManifoldVolume.measurable_inverseChart c).aemeasurable
  have hBaseInt : IntegrableOn F e.source V := by
    rw [IntegrableOn, hMap]
    exact (integrable_map_measure hMeas hMeasMap).2 (hIntR.integrableOn.congr hEqR)
  have hFZero (x : M) (hx : x ∉ U) : F x = 0 :=
    mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))) _
  have hRZero (y : Space) (hy : y ∉ e.target) : (∑ i, ∑ j, R i j y) = 0 := by
    have h0 (i j : Index) : (ψ i j : Space → ℝ) y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hImageTarget (hSupport i j h)))
    simp [R, h0]
  refine ⟨hBaseInt.mono_set hUsrc, hIntP.congr hEqP, ?_⟩
  calc
    (∫ x in U, F x ∂V) = ∫ x in e.source, F x ∂V :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hFZero).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hFZero x (fun h => hx (hUsrc h)))).symm
    _ = ∫ y in e.target, F (ManifoldVolume.inverseChart c y) ∂dVc := by
      rw [hMap, integral_map hMeasMap hMeas]
    _ = ∫ y in e.target, ∑ i, ∑ j, R i j y ∂dVc := (integral_congr_ae hEqR).symm
    _ = ∫ y, ∑ i, ∑ j, R i j y ∂dVc := setIntegral_eq_integral_of_forall_compl_eq_zero hRZero
    _ = ∑ i, ∑ j, ∫ y, R i j y ∂dVc := hsumR
    _ = ∑ i, ∑ j, ∫ p in S, P i j p ∂μ :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => (hm i j).2.2))
    _ = ∫ p in S, ∑ i, ∑ j, P i j p ∂μ := hsumP.symm
    _ = ∫ p in S, G p ∂μ := integral_congr_ae hEqP

end Burnett.Analysis.ChartTensorRicciTests
