import Burnett.Analysis.TransportPatches.FrozenChartPhase
import Burnett.Analysis.GaugeProjection.ProjectedAmplitudeCovariance
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude
import Burnett.Analysis.Microlocal.Overlap.AtlasChartAmplitudeIntegrability

/-! The thin-cone complement annihilates the original projected covariance. -/

set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Module Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components_apply)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector)
open Burnett.P01 (principalGaugeProjectionMatrix tensorOfVector_principalGaugeProjectionMatrix
  principalGaugeProjection_eq_zero_off_null)
open Burnett.Analysis.ProjectiveNullCaps (quadratic thinConeProfile)
open scoped BigOperators ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The actual intrinsic Ricci constraint supplies the coordinate kernel
and symmetry of every original ordered covariance column. -/
theorem atlasAmplitudeColumn_ricciKernel {r : Metric (M := M)}
    (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (D : AmplitudeCovarianceDensity r) (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) (h : HasIntrinsicAmplitudeRicciKernel r B hn D p) (j : OrderedPair) :
    let G := chartInverseMetric B c (c.chart (projection p))
    let ξ := atlasChartUnitCovector c p
    let k := tensorOfVector ((atlasAmplitudeMatrix c D p).col j)
    IsSymmetricComplexTensor k ∧ ∀ a b, complexRicciSymbol G ξ k a b = 0 := by
  intro G ξ k
  let b := chartTangentBasis c (projection p) hp
  letI : FiniteDimensional ℝ (TangentSpace Model (projection p)) := Module.Finite.of_basis b
  let f := amplitudeSlice (D p) (b j.1) (b j.2)
  have hk : k = fun i l => f (b i) (b l) := by
    funext i l
    change atlasAmplitudeMatrix c D p (i, l) j = f (b i) (b l)
    rw [atlasAmplitudeMatrix_of_mem c D p hp]
    change F07.IntrinsicAmplitudeCoordinates.components b (D p) (i, l) j = f (b i) (b l)
    rw [components_apply, amplitudeSlice_apply]
  have hf := h (b j.1) (b j.2)
  refine ⟨fun i l => ?_, fun a d => ?_⟩
  · rw [hk]
    exact hf.1 (b i) (b l)
  · have hBasis := complexFiberRicciSymbol_eq_basis (covariantForm B (projection p)) (hn (projection p))
      p.val.2.toLinearMap f b a d
    have hRic := hf.2
    change complexFiberRicciSymbol (covariantForm B (projection p)) (hn (projection p))
      p.val.2.toLinearMap f = 0 at hRic
    rw [hRic, LinearMap.zero_apply, LinearMap.zero_apply, ← chartInverseMetric_in_basis B hs hn c (projection p) hp,
      ← atlasCovector_eq_fiberCoordinates c p hp, ← hk] at hBasis
    exact hBasis.symm

/-- The gauge projection annihilates the full original covariance at every
off-null point where the intrinsic Ricci constraint holds. -/
theorem projectedAtlasAmplitude_eq_zero_off_null {r : Metric (M := M)}
    (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (D : AmplitudeCovarianceDensity r) (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) (h : HasIntrinsicAmplitudeRicciKernel r B hn D p)
    (hNull : hamiltonian B hn p ≠ 0) :
    principalGaugeProjectionMatrix (WithLp.toLp 2 (atlasChartUnitCovector c p)) *
      atlasAmplitudeMatrix c D p = 0 := by
  let q := atlasChartUnitCovector c p
  let ξ : E := WithLp.toLp 2 q
  let G := chartInverseMetric B c (c.chart (projection p))
  have hq : (fun i : Index => ξ i) ≠ 0 := atlasChartUnitCovector_ne_zero c p hp
  have hG : symbolNorm G (fun i => ξ i) ≠ 0 := by
    intro hzero
    have he := chartQuadratic_eq_two_hamiltonian B hs hn c p hp
    rw [quadratic_eq_symbolNorm] at he
    change symbolNorm G (fun i => ξ i) = _ at he
    rw [hzero] at he
    exact hNull (by linarith only [he])
  ext i j
  let v := (atlasAmplitudeMatrix c D p).col j
  have hR := (atlasAmplitudeColumn_ricciKernel B hs hn D c p hp h j).2
  have hZero := principalGaugeProjection_eq_zero_off_null G ξ (tensorOfVector v) hq hG hR
  have he := tensorOfVector_principalGaugeProjectionMatrix ξ v
  rw [hZero] at he
  exact congrFun (congrFun he i.1) i.2

/-- The exact thin-cone complementary symbol of the original physical projection. -/
def thinConeComplementMatrix (m : Tensor2) (η inner outer : ℝ) (ξ : E) :
    Matrix OrderedPair OrderedPair ℂ :=
  ((1 - thinConeProfile m η inner outer ξ : ℝ) : ℂ) • principalGaugeProjectionMatrix ξ

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The actual smooth-background phase makes the specified complementary
defect exactly zero on the original trace of the entire patch. -/
theorem exists_thinConeComplement_annihilates_originalAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x₀ ∈ K, ∀ ℓ : ℝ, (∀ x ∈ K, ‖x - x₀‖ ≤ ℓ) →
      ∀ η inner outer : ℝ, 0 < η → 0 ≤ inner → inner < outer → L * ℓ ≤ inner * η →
      let m := chartInverseMetric B c x₀
      let τ := A.control.restrict (amplitudeCosphereWindow r (c.chart.symm '' K))
      ∀ᵐ p ∂τ, thinConeComplementMatrix m η inner outer (WithLp.toLp 2 (atlasChartUnitCovector c p)) *
        atlasAmplitudeMatrix c A.density p = 0 := by
  obtain ⟨L, hL, hPhase⟩ := exists_actualNull_frozenPhaseAndThinCone (r := r) B hB hs hn c K hK hConv hKU
  refine ⟨L, hL, ?_⟩
  intro x₀ hx₀ ℓ hℓ η inner outer hη hIn hIO hSmall m τ
  have hImage : IsCompact (c.chart.symm '' K) := hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKU)
  have hS := measurableSet_amplitudeCosphereWindow r hImage.isClosed.measurableSet
  filter_upwards [ae_restrict_mem (μ := A.control) hS, ae_restrict_of_ae hA.2.2.2.2.2] with p hp hData
  change projection p ∈ c.chart.symm '' K at hp
  obtain ⟨x, hx, hxEq⟩ := hp
  have hpC : projection p ∈ c.chart.source := hxEq ▸ c.chart.symm_mapsTo (hKU hx)
  have hpx : c.chart (projection p) ∈ K := by
    rw [← hxEq, c.chart.right_inv (hKU hx)]
    exact hx
  by_cases hNull : hamiltonian B hn p = 0
  · have hOne : thinConeProfile m η inner outer (WithLp.toLp 2 (atlasChartUnitCovector c p)) = 1 :=
      (hPhase x₀ hx₀ p hpC hpx hNull ℓ (hℓ _ hpx)).2 η inner outer hη hIn hIO hSmall
    simp [thinConeComplementMatrix, hOne]
  · rw [thinConeComplementMatrix, smul_mul_assoc,
      projectedAtlasAmplitude_eq_zero_off_null B hs hn A.density c p hpC hData.2.2 hNull, smul_zero]

end Burnett.C02
