import Burnett.Analysis.Microlocal.Overlap.SymmetricJetChartSections
import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderSymmetricProjection
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartHalfDensity

/-! A physical chart lift represents the same actual symmetric section in an overlap. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5700000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity fixedHalfDensity_change)
open Burnett.Microlocal.AtlasOverlapKernel (overlapJacobianWeight overlapJacobianWeight_eq)
open scoped ContDiff Manifold

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private theorem symmetrizeOrderedJet_smul (a : ℂ) (w : JetSlot → ℂ) :
    symmetrizeOrderedJet (a • w) = a • symmetrizeOrderedJet w := by
  funext i
  simp only [symmetrizeOrderedJet, Pi.smul_apply, smul_eq_mul]
  ring

private theorem orderedChartLiftCoordinates (B : Field (M := M)) (c : AtlasChart M)
    (f : JetSlot → E → ℂ) (p : M) (hp : p ∈ c.chart.source) :
    jetFiberCoordinates (chartTangentBasis c p hp) (symmetricJetChartLift B c f p : ComplexCovariantJet _) =
      (fixedHalfDensity B c (c.chart p) : ℂ)⁻¹ • symmetrizeOrderedJet (fun i => f i (c.chart p)) := by
  funext i
  rw [← symmetricJetComponent_of_mem c _ i p hp, symmetricJetComponent_chartLift B c f i p hp]
  simp only [receivingScalarPhysicalLift, indicator_of_mem hp, Pi.smul_apply, smul_eq_mul, symmetrizeOrderedJet]
  ring

/-- Actual bundle half-density transport on a compact window leaves the
manifold section unchanged. It applies the reverse transition to all three
ordered slots, and the actual inverse chart volume on each side. -/
theorem symmetricJetChartLift_eq_of_transport
    (B : Field (M := M)) (hn : IsNondegenerate B)
    (c d : AtlasChart M) (K : Set E) (hK : K ⊆ (c.transition d).source)
    (f w : JetSlot → E → ℂ) (hf : ∀ i, support (f i) ⊆ K)
    (hw : ∀ i, support (w i) ⊆ c.transition d '' K)
    (hTransport : ∀ x ∈ K,
      let y := c.transition d x
      (fun i => w i y) = (overlapJacobianWeight d c y : ℂ) •
        rawReceivingJetTransition d c y (fun i => f i x)) :
    symmetricJetChartLift B c f = symmetricJetChartLift B d w := by
  have hSupport₀ := symmetricJetChartLift_support B c f K hf
  have hSupport₁ := symmetricJetChartLift_support B d w (c.transition d '' K) hw
  have hRange : d.chart.symm '' (c.transition d '' K) ⊆ c.chart.symm '' K := by
    rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    have hd : c.chart.symm x ∈ d.chart.source := (hK hx).2
    change d.chart.symm (d.chart (c.chart.symm x)) ∈ c.chart.symm '' K
    rw [d.chart.left_inv hd]
    exact mem_image_of_mem _ hx
  funext p
  by_cases hp : p ∈ c.chart.symm '' K
  · obtain ⟨x, hx, rfl⟩ := hp
    let p := c.chart.symm x
    have hSrc := hK hx
    have hc : p ∈ c.chart.source := c.chart.symm_mapsTo hSrc.1
    have hd : p ∈ d.chart.source := hSrc.2
    have hcx : c.chart p = x := c.chart.right_inv hSrc.1
    let y := d.chart p
    have hRev : y ∈ (d.transition c).source := by
      refine ⟨d.chart.mapsTo hd, ?_⟩
      change d.chart.symm (d.chart p) ∈ c.chart.source
      rwa [d.chart.left_inv hd]
    have hRevEq : d.transition c y = x := by
      change c.chart (d.chart.symm (d.chart p)) = x
      rw [d.chart.left_inv hd, hcx]
    let L := rawReceivingJetTransition d c y
    let a : ℂ := overlapJacobianWeight d c y
    let δc : ℂ := fixedHalfDensity B c x
    let δd : ℂ := fixedHalfDensity B d y
    have hδ : δd = a * δc := by
      have h := fixedHalfDensity_change B d c hRev
      rw [hRevEq] at h
      change (fixedHalfDensity B d y : ℂ) =
        (overlapJacobianWeight d c y : ℂ) * (fixedHalfDensity B c x : ℂ)
      rw [overlapJacobianWeight_eq d c hRev]
      exact_mod_cast h
    have hδc : δc ≠ 0 := Complex.ofReal_ne_zero.mpr (fixedHalfDensity_pos B hn c x hSrc.1).ne'
    have hδd : δd ≠ 0 := Complex.ofReal_ne_zero.mpr (fixedHalfDensity_pos B hn d y hRev.1).ne'
    have hCancel : δd⁻¹ * a = δc⁻¹ := by
      apply mul_right_cancel₀ hδc
      rw [mul_assoc, ← hδ, inv_mul_cancel₀ hδd, inv_mul_cancel₀ hδc]
    have hL : L (symmetrizeOrderedJet (fun i => f i x)) =
        symmetrizeOrderedJet (L (fun i => f i x)) :=
      rawReceivingJetTransition_symmetrizeOrderedJet d c p hd hc _
    have hw' : (fun i => w i y) = a • L (fun i => f i x) := hTransport x hx
    have hLeft := rawReceivingJetTransition_jetFiberCoordinates d c p hd hc
      (symmetricJetChartLift B c f p : ComplexCovariantJet _)
    have hLeft' : jetFiberCoordinates (chartTangentBasis d p hd)
        (symmetricJetChartLift B c f p : ComplexCovariantJet _) =
        δc⁻¹ • symmetrizeOrderedJet (L (fun i => f i x)) := by
      rw [← hLeft, orderedChartLiftCoordinates B c f p hc, hcx, map_smul]
      exact congrArg (δc⁻¹ • ·) hL
    have hRight' : jetFiberCoordinates (chartTangentBasis d p hd)
        (symmetricJetChartLift B d w p : ComplexCovariantJet _) =
        δc⁻¹ • symmetrizeOrderedJet (L (fun i => f i x)) := by
      rw [orderedChartLiftCoordinates B d w p hd]
      change δd⁻¹ • symmetrizeOrderedJet (fun i => w i y) = _
      rw [hw', symmetrizeOrderedJet_smul, smul_smul, hCancel]
    exact Subtype.ext ((jetFiberCoordinates (chartTangentBasis d p hd)).injective (hLeft'.trans hRight'.symm))
  · have h₀ : symmetricJetChartLift B c f p = 0 := by
      by_contra hz
      exact hp (hSupport₀ hz)
    have h₁ : symmetricJetChartLift B d w p = 0 := by
      by_contra hz
      exact hp (hRange (hSupport₁ hz))
    exact h₀.trans h₁.symm

end Burnett.Microlocal.Overlap
