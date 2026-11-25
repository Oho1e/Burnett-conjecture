import Burnett.Analysis.Microlocal.Overlap.SmoothCompactSymmetricJetTests

/-! A distribution-kernel pairing on actual tests, read in finite ordered coordinates. -/

set_option autoImplicit false
set_option maxHeartbeats 5900000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical Matrix MeasureTheory Burnett.Fourier Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped Manifold ContDiff Topology BigOperators Matrix ComplexConjugate

local notation "E" => CoordinateSpace
abbrev SymmetricJetFiber (M : Type*) [TopologicalSpace M] [ChartedSpace E M] (p : M) :=
  ↥(complexSymmetricJet (TangentSpace Model p))

section Fiber

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A full ordered coordinate column followed by the genuine symmetric projection. -/
def projectedJetColumn (b : Module.Basis Index ℝ V) (i : JetSlot) : complexSymmetricJet V :=
  projectComplexSymmetricJet V ((jetFiberCoordinates b).symm (Pi.single i 1))

/-- The ordered columns reconstruct exactly the actual symmetric jet. -/
theorem sum_projectedJetColumn (b : Module.Basis Index ℝ V) (f : complexSymmetricJet V) :
    (∑ i, (jetFiberCoordinates b (f : ComplexCovariantJet V) i) • projectedJetColumn b i) = f := by
  let W := jetFiberCoordinates b
  let e (i : JetSlot) : JetSlot → ℂ := Pi.single i 1
  have hCoords : (∑ i, (W (f : ComplexCovariantJet V) i) • e i) =
      W (f : ComplexCovariantJet V) := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp [e]
    · intro i _ hij
      simp [e, Pi.single_eq_of_ne hij.symm]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  calc
    _ = projectComplexSymmetricJet V (W.symm (∑ i, (W (f : ComplexCovariantJet V) i) • e i)) := by
      simp only [projectedJetColumn, W, e, map_sum, map_smul]
    _ = f := by
      rw [hCoords, LinearEquiv.symm_apply_apply]
      exact Subtype.ext (coe_projectComplexSymmetricJet_of_mem _ f.property)

end Fiber

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Paired kernel values act in the two actual fibers. The target fiber is
the conjugate-linear test slot. For an endomorphism kernel this is the
kernel paired against the intrinsic auxiliary fiber metric. -/
abbrev SymmetricJetPairingKernel (M : Type*) [TopologicalSpace M] [ChartedSpace E M] :=
  ∀ p q : M, SymmetricJetFiber M p →ₛₗ[starRingEnd ℂ] SymmetricJetFiber M q →ₗ[ℂ] ℂ

abbrev SymmetricJetGlobalForm (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] :=
  (smoothCompactSymmetricJet M) →ₛₗ[starRingEnd ℂ] (smoothCompactSymmetricJet M) →ₗ[ℂ] ℂ

/-- The localized kernel identity takes place on actual compact sections and
agrees with the one global sesquilinear form. -/
def HasSeparatedSymmetricJetKernel [MeasurableSpace M] (μ : Measure M) (form : SymmetricJetGlobalForm M)
    (K : SymmetricJetPairingKernel M) : Prop :=
  ∀ (S T : Set M), IsCompact S → IsCompact T → Disjoint S T →
    ∀ (v u : smoothCompactSymmetricJet M),
      symmetricJetSectionSupport (v : SymmetricJetSection M) ⊆ S →
      symmetricJetSectionSupport (u : SymmetricJetSection M) ⊆ T →
      form v u = ∫ p in S, ∫ q in T, K p q (v.val p) (u.val q) ∂μ ∂μ

/-- The chart column is a genuinely symmetric section at each point of the chart. -/
def symmetricJetChartColumn (c : AtlasChart M) (i : JetSlot) (p : M) : SymmetricJetFiber M p :=
  if h : p ∈ c.chart.source then projectedJetColumn (chartTangentBasis c p h) i else 0

theorem sum_symmetricJetChartColumn (c : AtlasChart M) (s : SymmetricJetSection M)
    (p : M) (hp : p ∈ c.chart.source) :
    (∑ i, symmetricJetComponent c s i p • symmetricJetChartColumn c i p) = s p := by
  simp only [symmetricJetComponent, symmetricJetChartColumn, dif_pos hp]
  exact sum_projectedJetColumn (chartTangentBasis c p hp) (s p)

/-- The entries are tests of the single actual paired kernel on projected
basis columns. No coordinate-independent scalarization is selected. -/
def symmetricJetKernelEntry (K : SymmetricJetPairingKernel M) (c d : AtlasChart M)
    (i j : JetSlot) (p q : M) : ℂ :=
  K p q (symmetricJetChartColumn c i p) (symmetricJetChartColumn d j q)

theorem symmetricJetPairingKernel_eq_sum_entries (K : SymmetricJetPairingKernel M)
    (c d : AtlasChart M) (v u : SymmetricJetSection M)
    (p q : M) (hp : p ∈ c.chart.source) (hq : q ∈ d.chart.source) :
    K p q (v p) (u q) =
      ∑ i, ∑ j, conj (symmetricJetComponent c v i p) * symmetricJetKernelEntry K c d i j p q *
        symmetricJetComponent d u j q := by
  rw [← sum_symmetricJetChartColumn c v p hp, ← sum_symmetricJetChartColumn d u q hq]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, RingHom.id_apply, symmetricJetKernelEntry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Burnett.Microlocal.Overlap
