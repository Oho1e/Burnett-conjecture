import Burnett.Analysis.GaugeProjection.StrongCompactness.StrongOpenSet
import Burnett.Analysis.GaugeProjection.StrongCompactness.IntrinsicVacuumFromAngularMoments
import Burnett.Analysis.BaseMarginal.IntrinsicVacuumMarginal

/-! Vacuum limits and strong physical compactness on every open region. -/
set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 5100000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol Burnett.Fourier
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient Burnett.Microlocal.Overlap
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F08.IntrinsicBaseMarginal (auxiliaryEinsteinDensity_baseMarginal physicalMeasure_zero_over_vacuumOpen)
open Burnett.X02.SobolevTestJet (D)
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

/-- The original vacuum perturbations satisfy the homogeneous strong
criterion for every receiving chart, every interior cutoff, and the full
sequence exactly on the open regions with pointwise vacuum background. -/
theorem vacuumOpen_iff_hasStrongProjectedGradientOn
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (U : Set M) (hU : IsOpen U) :
    (∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) ↔
      HasStrongProjectedGradientOn B g hB hg U := by
  constructor
  · intro hRic
    apply hasStrongProjectedGradientOn_of_null_physical_subsequence_refinements r B g hB hg hSig hconv U
    intro s hs
    obtain ⟨t, ht, A, μ, hA, hPair, _, _, hPhys, _, _, hFin, _, hMom, hScal, _⟩ :=
      exists_originalVacuum_symmetricJetMeasure_localClassicalPairings_and_EinsteinMoments r B g hB hg hSig
        hsG hnG hconv hb hv s hs
    have hMarg := auxiliaryEinsteinDensity_baseMarginal r B hB hSig.isSymmetric hSig.isNondegenerate μ hFin hMom
    exact ⟨t, ht, A, μ, hA, hPair, hPhys,
      physicalMeasure_zero_over_vacuumOpen r B hSig.isNondegenerate μ hMarg hScal U hU hRic⟩
  · intro hStrong
    have hid : StrictMono (id : ℕ → ℕ) := strictMono_id
    obtain ⟨t, ht, A, μ, hA, hPair, _, _, hPhys, _, _, hFin, hNull, hMom, hScal, _⟩ :=
      exists_originalVacuum_symmetricJetMeasure_localClassicalPairings_and_EinsteinMoments r B g hB hg hSig
        hsG hnG hconv hb hv id hid
    have hZero := physicalMeasure_zero_over_open_of_hasStrongProjectedGradientOn r B g hB hg hSig hconv
      (id ∘ t) (hid.comp ht) A hA hPair μ hPhys U hU hStrong
    exact intrinsicRicci_eq_zero_on_open_of_originalEinsteinMoments r B g hB hg hSig hsG hnG hconv hb hv
      μ hFin hNull hMom hScal U hU hZero

/-- Local strong convergence of every component of the original covariant
derivative. The receiving test uses ordinary chart volume on the
half-density representative and compact support in the specified region. -/
def HasStrongOriginalCovariantGradientOn (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (U : Set M) : Prop :=
  ∀ (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target),
    c.chart.symm '' tsupport (χ : E → ℝ) ⊆ U → ∀ i : JetSlot,
      Tendsto (fun n => (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i).toLp 2 volume)
        atTop (𝓝 0)

open private tendsto_sum_sq_norm_zero_iff from Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- Strong local convergence of the original derivative gives the whole
sequence homogeneous projected convergence, including its full-space tails. -/
theorem hasStrongProjectedGradientOn_of_strongOriginalCovariantGradient
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (U : Set M)
    (hStrong : HasStrongOriginalCovariantGradientOn r B g hB hg hn U) :
    HasStrongProjectedGradientOn B g hB hg U := by
  intro c χ hχ hU
  let η := inverseHalfDensityCutoff B hB hn c χ hχ
  have hηs : tsupport (η : E → ℝ) ⊆ tsupport (χ : E → ℝ) := inverseHalfDensityCutoff_tsupport B hB hn c χ hχ
  have hηc := hηs.trans hχ
  have hηU : c.chart.symm '' tsupport (η : E → ℝ) ⊆ U := (image_mono hηs).trans hU
  let z := receivingCutoffFluctuation B g hB hg c χ hχ
  obtain ⟨z', hz, _, hErr⟩ := exists_receiving_cutoff_metric_and_derivative_error r B g hB hg hconv c χ hχ
  have he : z' = z := by
    funext n i j
    ext x
    exact hz n x i j
  subst z'
  have hχeq : fixedWeightedCutoff B hB hn c η hηc = χ := fixedWeightedCutoff_inverseHalfDensityCutoff B hB hn c χ hχ
  have hRaw (n : ℕ) (d i j : Index) :
      fixedVolumeGradientSchwartz B g hB hg hn c η hηc n (d, i, j) =
        fixedGradientSchwartz B g hB hg c χ hχ n (d, i, j) := by
    ext x
    rw [fixedVolumeGradientSchwartz_apply, fixedGradientSchwartz_apply]
    have hMul := congrFun (congrArg Subtype.val hχeq) x
    change (η : E → ℝ) x * fixedHalfDensity B c x = (χ : E → ℝ) x at hMul
    rw [hMul]
  have hDeriv (d i j : Index) : Tendsto (fun n => (coordinateDerivative d (z n i j)).toLp 2 volume) atTop (𝓝 0) := by
    have hCov := fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c η hηc (d, i, j)
    simp only [hRaw] at hCov
    have hPartial := (hStrong c η hηc hηU (d, i, j)).sub hCov
    simp only [sub_sub_cancel, sub_zero] at hPartial
    simpa only [sub_add_cancel, zero_add] using (hErr d i j).add hPartial
  let F (n : ℕ) (a : Index × OrderedPair) := homogeneousProjectedCoordinateDerivative (z n) a.1 a.2
  have hF (a : Index × OrderedPair) : Tendsto (fun n => F n a) atTop (𝓝 0) := by
    have hSlot (i : OrderedPair) := ((fourierMultiplier
      (principalProjectionComponentSymbol a.2.1 a.2.2 i.1 i.2)).continuous.tendsto 0).comp
        (hDeriv a.1 i.1 i.2)
    simp only [map_zero] at hSlot
    simpa only [F, homogeneousProjectedCoordinateDerivative, Finset.sum_const_zero, Function.comp_apply] using
      tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun i _ => hSlot i)
  have hFin := (tendsto_sum_sq_norm_zero_iff F).mpr hF
  have hSum (n : ℕ) : (∑ a : Index × OrderedPair, ‖F n a‖^2) =
      receivingStrongProjectionEnergy B g hB hg c χ hχ n :=
    Fintype.sum_prod_type (fun a : Index × OrderedPair => ‖F n a‖^2)
  exact hFin.congr hSum

end Burnett.P01
