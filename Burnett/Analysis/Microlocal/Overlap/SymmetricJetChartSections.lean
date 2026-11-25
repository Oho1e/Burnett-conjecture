import Burnett.Analysis.Microlocal.Overlap.ReceivingScalarHalfDensity
import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSymmetricJet

/-! Genuine symmetric jet sections and their compact chart lifts. -/

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedHalfDensity fixedVolumeCovariantGradientSchwartz fixedVolumeCovariantGradientSchwartz_tsupport)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped Manifold ContDiff Topology BigOperators

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A section takes values in the genuine complex symmetric fiber at its base point. -/
abbrev SymmetricJetSection (M : Type*) [TopologicalSpace M] [ChartedSpace E M] :=
  ∀ p : M, complexSymmetricJet (TangentSpace Model p)

def symmetricJetSectionSupport (s : SymmetricJetSection M) : Set M :=
  {p | s p ≠ 0}

/-- A manifold component in one actual tangent frame, extended by zero. -/
def symmetricJetComponent (c : AtlasChart M) (s : SymmetricJetSection M) (i : JetSlot) (p : M) : ℂ :=
  if h : p ∈ c.chart.source then
    jetFiberCoordinates (chartTangentBasis c p h) (s p : ComplexCovariantJet (TangentSpace Model p)) i
  else 0

theorem symmetricJetComponent_of_mem (c : AtlasChart M) (s : SymmetricJetSection M)
    (i : JetSlot) (p : M) (hp : p ∈ c.chart.source) :
    symmetricJetComponent c s i p =
      jetFiberCoordinates (chartTangentBasis c p hp) (s p : ComplexCovariantJet (TangentSpace Model p)) i :=
  dif_pos hp

theorem symmetricJetComponent_eq_zero (c : AtlasChart M) (s : SymmetricJetSection M)
    (i : JetSlot) (p : M) (hp : s p = 0) : symmetricJetComponent c s i p = 0 := by
  unfold symmetricJetComponent
  split <;> simp_all

/-- The physical lift projects the ordered array back to the symmetric fiber,
and lies in that actual fiber also outside the chart, where it is zero. -/
def symmetricJetChartLift (B : Field (M := M)) (c : AtlasChart M) (f : JetSlot → E → ℂ) :
    SymmetricJetSection M := fun p =>
  if h : p ∈ c.chart.source then
    projectComplexSymmetricJet _ ((jetFiberCoordinates (chartTangentBasis c p h)).symm
      (fun i => receivingScalarPhysicalLift B c (f i) p))
  else 0

theorem symmetricJetComponent_chartLift (B : Field (M := M)) (c : AtlasChart M)
    (f : JetSlot → E → ℂ) (i : JetSlot) (p : M) (hp : p ∈ c.chart.source) :
    symmetricJetComponent c (symmetricJetChartLift B c f) i p =
      (2 : ℂ)⁻¹ * (receivingScalarPhysicalLift B c (f i) p +
        receivingScalarPhysicalLift B c (f (jetPairSwap i)) p) := by
  rw [symmetricJetComponent_of_mem c _ i p hp]
  unfold symmetricJetChartLift
  rw [dif_pos hp, jetFiberCoordinates_projectComplexSymmetricJet, LinearEquiv.apply_symm_apply]

theorem symmetricJetChartLift_support (B : Field (M := M)) (c : AtlasChart M) (f : JetSlot → E → ℂ)
    (K : Set E) (hK : ∀ i, support (f i) ⊆ K) :
    symmetricJetSectionSupport (symmetricJetChartLift B c f) ⊆ c.chart.symm '' K := by
  intro p hp
  by_contra hout
  apply hp
  unfold symmetricJetChartLift
  by_cases hpc : p ∈ c.chart.source
  · rw [dif_pos hpc]
    have hzero (i : JetSlot) : receivingScalarPhysicalLift B c (f i) p = 0 := by
      by_contra h
      exact hout (receivingScalarPhysicalLift_support B c (f i) K (hK i) h)
    simp only [hzero]
    change projectComplexSymmetricJet _ ((jetFiberCoordinates (chartTangentBasis c p hpc)).symm 0) = 0
    rw [map_zero, map_zero]
  · exact dif_neg hpc

/-- The chart half-density of an actual component uses the background metric. -/
def symmetricJetHalfDensity (B : Field (M := M)) (c : AtlasChart M) (s : SymmetricJetSection M)
    (i : JetSlot) : E → ℂ :=
  receivingScalarTestHalfDensity B c (symmetricJetComponent c s i)

theorem symmetricJetHalfDensity_chartLift_of_mem (B : Field (M := M)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (f : JetSlot → E → ℂ) (i : JetSlot) (x : E) (hx : x ∈ c.chart.target) :
    symmetricJetHalfDensity B c (symmetricJetChartLift B c f) i x =
      (2 : ℂ)⁻¹ * (f i x + f (jetPairSwap i) x) := by
  have hpc := c.chart.symm_mapsTo hx
  have hδ : (fixedHalfDensity B c x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fixedHalfDensity_pos B hn c x hx).ne'
  unfold symmetricJetHalfDensity receivingScalarTestHalfDensity
  rw [indicator_of_mem hx, symmetricJetComponent_chartLift B c f i _ hpc]
  simp only [receivingScalarPhysicalLift, indicator_of_mem hpc, c.chart.right_inv hx]
  let a := (fixedHalfDensity B c x : ℂ)
  change a * ((2 : ℂ)⁻¹ * (a⁻¹ * f i x + a⁻¹ * f (jetPairSwap i) x)) = _
  calc
    _ = (a * a⁻¹) * ((2 : ℂ)⁻¹ * (f i x + f (jetPairSwap i) x)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hδ, one_mul]

theorem symmetricJetHalfDensity_chartLift_of_pairSwap (B : Field (M := M)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (f : JetSlot → E → ℂ) (hfc : ∀ i, support (f i) ⊆ c.chart.target)
    (hs : ∀ i, f (jetPairSwap i) = f i) (i : JetSlot) :
    symmetricJetHalfDensity B c (symmetricJetChartLift B c f) i = f i := by
  funext x
  by_cases hx : x ∈ c.chart.target
  · rw [symmetricJetHalfDensity_chartLift_of_mem B hn c f i x hx, hs]
    ring
  · have hz : f i x = 0 := by
      by_contra hn0
      exact hx (hfc i hn0)
    rw [hz]
    unfold symmetricJetHalfDensity receivingScalarTestHalfDensity
    rw [indicator_of_notMem hx]

variable [SecondCountableTopology M]

/-- The actual original localized covariant jet reads back without change,
including its full coordinate zero extension. -/
theorem symmetricJetHalfDensity_originalCovariantChartLift (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (n : ℕ) (i : JetSlot) :
    let f (j : JetSlot) := (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n j : E → ℂ)
    symmetricJetHalfDensity B c (symmetricJetChartLift B c f) i = f i := by
  intro f
  apply symmetricJetHalfDensity_chartLift_of_pairSwap B hn c f
  · intro j
    exact (subset_tsupport _).trans
      ((fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hχ n j).trans hχ)
  · intro j
    exact congrArg (fun z : SchwartzMap E ℂ => (z : E → ℂ))
      (fixedVolumeCovariantGradientSchwartz_pairSwap r B g hB hg hn hsB hsG c χ hχ n j)

end Burnett.Microlocal.Overlap
