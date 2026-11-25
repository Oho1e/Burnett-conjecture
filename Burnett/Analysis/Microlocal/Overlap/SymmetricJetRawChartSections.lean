import Burnett.Analysis.Microlocal.Overlap.SymmetricJetPairingKernel
import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderSymmetricProjection

/-! Realize unweighted compact coordinate tests as actual symmetric sections. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity fixedHalfDensity_smooth)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A compact coordinate array has a genuine smooth compact lift with unweighted
components equal to its symmetric part. In overlapping charts these components
are exactly the three-slot transform of that symmetric part. -/
theorem exists_compactSymmetricJet_rawChartTest
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (d : AtlasChart M) (u : JetSlot → E → ℂ) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (K : Set E) (hK : IsCompact K) (hKd : K ⊆ d.chart.target) (hU : ∀ i, support (u i) ⊆ K) :
    ∃ s : smoothCompactSymmetricJet M,
      (∀ y ∈ d.chart.target, ∀ i, symmetricJetComponent d s i (d.chart.symm y) =
        symmetrizeOrderedJet (fun j => u j y) i) ∧
      ∀ (c : AtlasChart M) (y : E), y ∈ (c.transition d).source → ∀ i,
        symmetricJetComponent c s i (c.chart.symm y) =
          rawReceivingJetTransition c d y (symmetrizeOrderedJet (fun j => u j (c.transition d y))) i := by
  let w (i : JetSlot) (y : E) := (fixedHalfDensity B d y : ℂ) * u i y
  have hwSupp (i : JetSlot) : support (w i) ⊆ K := by
    intro y hy
    exact hU i (by
      intro hz
      exact hy (by simp [w, hz]))
  have hw (i : JetSlot) : ContDiff ℝ ∞ (w i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ d.chart.target
    · have hD := (fixedHalfDensity_smooth B hB hn d).contDiffAt (d.chart.open_target.mem_nhds hy)
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y hD).mul (hu i).contDiffAt
    · have hyK : y ∉ K := fun h => hy (hKd h)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with z hz
      exact notMem_support.mp (fun h => hz (hwSupp i h))
  let s := compactSymmetricJetChartTest B hB hn d w hw K hK hKd hwSupp
  have hRight (y : E) (hy : y ∈ d.chart.target) (i : JetSlot) :
      symmetricJetComponent d s i (d.chart.symm y) = symmetrizeOrderedJet (fun j => u j y) i := by
    have hdy : d.chart.symm y ∈ d.chart.source := d.chart.symm_mapsTo hy
    have hδ : (fixedHalfDensity B d y : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (fixedHalfDensity_pos B hn d y hy).ne'
    have hLift (j : JetSlot) : receivingScalarPhysicalLift B d (w j) (d.chart.symm y) = u j y := by
      simp only [receivingScalarPhysicalLift, indicator_of_mem hdy, w, d.chart.right_inv hy]
      rw [← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
    change symmetricJetComponent d (symmetricJetChartLift B d w) i (d.chart.symm y) = _
    rw [symmetricJetComponent_chartLift B d w i _ hdy, hLift, hLift]
    rfl
  refine ⟨s, hRight, ?_⟩
  intro c y hy i
  let x := c.chart.symm y
  have hc : x ∈ c.chart.source := c.chart.symm_mapsTo hy.1
  have hd : x ∈ d.chart.source := hy.2
  have hcy : c.chart x = y := c.chart.right_inv hy.1
  have hdy : d.chart x = c.transition d y := rfl
  have hInput : jetFiberCoordinates (chartTangentBasis d x hd)
      (s.val x : ComplexCovariantJet (TangentSpace Model x)) = symmetrizeOrderedJet (fun j => u j (c.transition d y)) := by
    funext j
    rw [← symmetricJetComponent_of_mem d _ j x hd]
    have h := hRight (d.chart x) (d.chart.mapsTo hd) j
    rwa [d.chart.left_inv hd, hdy] at h
  rw [symmetricJetComponent_of_mem c _ i x hc, ← hInput, ← hcy]
  exact congrFun (rawReceivingJetTransition_jetFiberCoordinates c d x hc hd
    (s.val x : ComplexCovariantJet (TangentSpace Model x))).symm i

end Burnett.Microlocal.Overlap
