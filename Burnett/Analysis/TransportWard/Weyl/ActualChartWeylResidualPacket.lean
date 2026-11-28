import Burnett.Analysis.TransportWard.Weyl.ChartDensitySchwartz
import Burnett.Analysis.TransportWard.Weyl.DensityWeylRemainderPair
import Burnett.Geometry.ManifoldLorentzSignature
import Burnett.Geometry.ManifoldVolumeRegularity

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03.Palatini

open Function Set MeasureTheory Burnett.Geometry Burnett.A03 Burnett.A02.FrequencySplit
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ContDiff Manifold Topology ComplexConjugate InnerProductSpace BigOperators Matrix.Norms.Elementwise

local notation "E₀" => CoordinateSpace
local notation "J" => Fin 4 × Fin 4

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

/-- A single extension of the actual ΓΓ Euler chart coefficients provides
both the exact Poisson bracket and the vanishing order-one energy error. -/
theorem exists_actualChart_densityWeylResidualPacket {ι : Type*} [Fintype ι]
    (S : ι → Mat) (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B) (chart : M)
    (θ : E₀ → ℝ) (β : E₀ → E₀ → ℝ) (R : ℝ) (hθ : HasCompactSupport θ)
    (hθChart : tsupport θ ⊆ (chartAt E₀ chart).target)
    (hs : ContDiff ℝ ∞ (uncurry β))
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol (fun x ξ => (β x ξ : ℂ)))) :
    let G := metricComponents (coordinateBilinear B chart)
    let a := windowedWeylLeftSymbol θ (fun y ζ => (β y ζ : ℂ)) R h
    let b := normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))
    ∃ c : ι → ι → J → SchwartzMap E₀ ℂ,
      (∀ (u : ι → SchwartzMap E₀ ℂ) (i : ι) (x : E₀),
        variableDensityWeylCommutator c a u i x = ∑ j,
          (firstOrderAction (fun y ξ => (canonicalBracket
            (fun z q => frozenDensityPrincipalPhase S (G z) q i j)
            (fun z q => β z (WithLp.toLp 2 q)) y (physicalRadianCovector ξ) : ℂ)) (u j) x +
            firstOrderAction (densityWeylResidualSymbol c a b i j) (u j) x)) ∧
      (∀ i j, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : SchwartzMap E₀ ℂ,
        ‖∫ x, conj (v x) * firstOrderAction (densityWeylResidualSymbol c a b i j) u x‖ ≤
          C * Real.sqrt (schwartzH1Energy u) * ‖v.toLp 2 volume‖) := by
  intro G a b
  let e := chartAt E₀ chart
  have hG : ContDiffOn ℝ ∞ G e.target :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j => contDiffOn_metricComponents B hB chart i j))
  have hDet : MapsTo G e.target nonsingularMetricDomain :=
    fun _ hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate chart hx
  obtain ⟨V,_,hWin,_,c,hc⟩ := exists_densityPrincipalCoefficients_schwartz_near
    S G hθ e.open_target hθChart hG hDet
  have hp (y ν : E₀) : (β y ν : ℂ) ≠ 0 → θ y = 1 :=
    fun hn => hPlateau y ν (fun he => hn (by rw [he,Complex.ofReal_zero]))
  refine ⟨c,fun u i x => ?_,fun i j => ?_⟩
  · exact variableDensityCompactWeylCommutator_eq_canonical_add_residual
      S G c θ β R hs h hAmp hPlateau hβ u i x
      (fun y hy j d => (hc i j d y (hWin hy)).1)
      (fun y hy j d => (hc i j d y (hWin hy)).2)
  · exact exists_densityWeylResidual_pair_bound c i j θ (fun y ν => (β y ν : ℂ)) R hθ h hAmp hp hβ

end Burnett.V03.Palatini
