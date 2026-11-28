import Burnett.Analysis.TransportWard.Weyl.CanonicalWeylOrderedKernel
import Burnett.Analysis.TransportWard.Weyl.WeylCovarianceContraction
import Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput
import Burnett.Analysis.TransportWard.Weyl.CanonicalWeylHomogeneousTail
import Burnett.Analysis.TransportWard.Weyl.OriginalChartCovarianceKernel
import Burnett.Analysis.TransportWard.Weyl.LebesgueGradientInput

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2800

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence ManifoldMetricTransition MaximalChart UnitNullCompactness
open Burnett.RicciSymbol Burnett.V02 Burnett.Microlocal.Overlap
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.Microlocal.PhysicalDensity (physicalContraction tensorOfVector)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open scoped ContDiff Topology Manifold BigOperators Matrix ComplexConjugate

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

private theorem canonicalBracket_eq_zero_off_base {L : Set E₀} (hL : IsClosed L)
    (a A : E₀ → Covector → ℝ) (hA : ∀ x ∉ L, ∀ ζ, a x ζ = 0)
    (x : E₀) (hx : x ∉ L) (ξ : Covector) : canonicalBracket A a x ξ = 0 := by
  have hBase : (fun y => a y ξ) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hL.isOpen_compl.mem_nhds hx] with y hy
    exact hA y hy ξ
  have hFiber : a x = fun _ => 0 := funext (hA x hx)
  simp only [canonicalBracket,basePartial,momentumPartial,hBase.fderiv_eq,hFiber,
    fderiv_const_apply,ContinuousLinearMap.zero_apply,mul_zero,sub_zero,Finset.sum_const_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The complete canonical Weyl matrix tested by the four Lebesgue
gradient slots has the physical weight of the original F05 covariance.
The reciprocal volume and the squared length of the unit-cosphere chart
coordinates both cancel inside that same a.e. density. -/
theorem ae_preferredWeyl_gradientContraction_samePhysicalWeight
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hSig.isNondegenerate σ A)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (a : E₀ → Covector → ℝ) (χ : E₀ → ℝ) (L : Set E₀) (hL : IsClosed L)
    (hSupp : ∀ x ∉ L, ∀ ξ, a x ξ = 0) (hχ : ∀ x ∈ L, χ x = 1) :
    let c := AtlasChart.atPoint q.center
    let G := chartLowerMetric B q.center
    ∀ᵐ p ∂(A.control.restrict (amplitudeCosphereWindow r K)),
      let x := c.chart (projection p)
      let ξ := atlasChartUnitCovector c p
      let d : ℂ := ((‖(WithLp.toLp 2 ξ : E₀)‖^2 : ℝ) : ℂ)
      let H (i j : I) :=
        (canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j)
          a x ξ : ℂ)
      let w := fixedCoordinateVolumeDensity B c x
      (∑ i : I, ∑ j : I, ∑ l : Fin 4,
        (((χ x)^2 * w⁻¹ : ℝ) : ℂ) *
          (H i j * ((symmetricMetricScale j : ℂ) * (symmetricMetricScale i : ℂ)) * d⁻¹ *
            atlasOrderedJetEntry c A.density p (l,i.val) (l,j.val))) =
        if hamiltonian B hSig.isNondegenerate p = 0 then
          4 * (intrinsicPhysicalWeight B hSig.isNondegenerate A.density p : ℂ) *
            (canonicalBracket (coordinateHamiltonian G) a x ξ : ℂ) else 0 := by
  intro c G
  have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hData := ae_original_preferredAtlasAmplitude_kernel_and_weight r B g hB hg hSig.isSymmetric
    hsG hSig.isNondegenerate hnG hconv hb hv σ hσ A hA q ν hf hRep K hK hSub
  filter_upwards [hData, ae_restrict_mem (μ := A.control) hW] with p hp hproj
  let x := c.chart (projection p)
  let ξ := atlasChartUnitCovector c p
  let C := atlasAmplitudeMatrix c A.density p
  let z : Phase := (x,ξ)
  let w := fixedCoordinateVolumeDensity B c x
  let H (i j : I) : ℂ :=
    canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j) a x ξ
  let P := canonicalBracket (coordinateHamiltonian G) a x ξ
  let W := intrinsicPhysicalWeight B hSig.isNondegenerate A.density p
  let d : ℂ := ((‖(WithLp.toLp 2 ξ : E₀)‖^2 : ℝ) : ℂ)
  have hpc : p.val.proj ∈ (chartAt E₀ q.center).source := (hSub hproj).1
  have hx : x ∈ (chartAt E₀ q.center).target := (chartAt E₀ q.center).mapsTo hpc
  have hξPref : ξ = cotangentCoords q.center p.val := atlasChartUnitCovector_eq_preferred q.center p hpc
  have hw : w = phaseDensity G z := by
    change Real.sqrt |Matrix.det (metricComponents (fixedForm B c) x)| =
      Real.sqrt |Matrix.det (metricComponents (coordinateBilinear B q.center) x)|
    rw [fixedForm_eq_preferred_components B q.center hx]
  have hwn : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    rw [hw]
    change Real.sqrt |Matrix.det (metricComponents (coordinateBilinear B q.center) x)| ≠ 0
    exact (Real.sqrt_pos.mpr (abs_pos.mpr (ManifoldVolumeRegularity.coordinate_det_ne_zero
      B hSig.isNondegenerate q.center hx))).ne')
  obtain ⟨hξ,hC,hInv,hKernel,hWeight⟩ := hp
  have hQuarter : (1 / 4 : ℂ) * physicalContraction (phaseInverse G z) C = (W : ℂ) := by
    change (1 / 4 : ℂ) * physicalContraction (backgroundInverse B q.center x) C = (W : ℂ)
    rw [physicalContraction_quarter_eq_real_of_posSemidef _ hInv C hC, ← hWeight]
  have hComp :
      scaledOrderedCovarianceContraction H Subtype.val symmetricMetricScale C =
        if dualEnergy B hSig.isNondegenerate p.val = 0 then
          4 * (w : ℂ) * (P : ℂ) * (W : ℂ) else 0 := by
    rw [← hQuarter]
    apply scaledOrderedCovarianceContraction_of_kernel_compression H Subtype.val symmetricMetricScale
      C hC (phaseInverse G z) w P
    intro v hv
    obtain ⟨u,rfl⟩ := hv
    obtain ⟨hSym,hR⟩ := hKernel u
    have hξ' : cotangentCoords q.center p.val ≠ 0 := hξPref ▸ hξ
    have hR' : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B q.center) (chartAt E₀ q.center p.val.proj,cotangentCoords q.center p.val))
      (cotangentCoords q.center p.val) (tensorOfVector (C *ᵥ u)) i j = 0 := by
      rw [← hξPref]
      exact hR
    have hRank := canonicalBracket_actualDensityWeyl_rankOne_orderedKernel B hB hSig q.center p.val
      hpc hξ' (C *ᵥ u) hSym hR' a
    rw [← hξPref] at hRank
    rw [hw]
    exact hRank
  change (∑ i : I, ∑ j : I, ∑ l : Fin 4, (((χ x)^2 * w⁻¹ : ℝ) : ℂ) *
    (H i j * ((symmetricMetricScale j : ℂ) * (symmetricMetricScale i : ℂ)) * d⁻¹ *
      atlasOrderedJetEntry c A.density p (l,i.val) (l,j.val))) =
    if hamiltonian B hSig.isNondegenerate p = 0 then 4 * (W : ℂ) * (P : ℂ) else 0
  have hFact :
      (∑ i : I, ∑ j : I, ∑ l : Fin 4, (((χ x)^2 * w⁻¹ : ℝ) : ℂ) *
        (H i j * ((symmetricMetricScale j : ℂ) * (symmetricMetricScale i : ℂ)) * d⁻¹ *
          atlasOrderedJetEntry c A.density p (l,i.val) (l,j.val))) =
        ((((χ x)^2 * w⁻¹ : ℝ) : ℂ) * scaledOrderedCovarianceContraction H Subtype.val symmetricMetricScale C) := by
    rw [← atlasOrderedJetEntry_diagonal_contraction c A.density p hξ H Subtype.val symmetricMetricScale]
    simp only [Finset.mul_sum]
    rfl
  rw [hFact,hComp]
  by_cases hNull : dualEnergy B hSig.isNondegenerate p.val = 0
  · have hHam : hamiltonian B hSig.isNondegenerate p = 0 := by simp only [hamiltonian,hNull,zero_div]
    rw [if_pos hNull,if_pos hHam]
    by_cases hX : x ∈ L
    · rw [hχ x hX,one_pow,one_mul,Complex.ofReal_inv]
      calc
        _ = (w : ℂ)⁻¹ * (w : ℂ) * (4 * (W : ℂ) * (P : ℂ)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hwn,one_mul]
    · have hP : P = 0 := canonicalBracket_eq_zero_off_base hL a _ hSupp x hX ξ
      rw [hP]
      simp only [Complex.ofReal_zero,mul_zero,zero_mul]
  · have hHam : hamiltonian B hSig.isNondegenerate p ≠ 0 := div_ne_zero hNull (by norm_num)
    rw [if_neg hNull,if_neg hHam,mul_zero]

end Burnett.V03.Palatini
