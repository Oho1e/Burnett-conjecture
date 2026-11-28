import Burnett.Analysis.TransportWard.Weyl.EulerLowerSchwartzCoefficients
import Burnett.Analysis.TransportWard.Weyl.ChartDensitySchwartz
import Burnett.Analysis.TransportWard.Weyl.SymmetricFieldNormalization

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2200

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricTransition Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped ContDiff Topology Manifold BigOperators Matrix.Norms.Elementwise

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "J" => Fin 4 × Fin 4

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

/-- The full real Euler density variation in the paper's orthonormal
coordinates has actual Schwartz coefficients of all three orders on one
neighborhood of the original outer cutoff. -/
theorem exists_actualNormalizedEulerWeylCoefficientPacket
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B) (chart : M)
    (K : Set E₀) (hK : IsCompact K) (hKU : K ⊆ (chartAt E₀ chart).target) :
    let U := (chartAt E₀ chart).target
    let S := orthonormalMetricDirection
    let g := normalizeMetricComponents ∘ symmetricChartMetricComponents B chart
    let G := metricComponents (coordinateBilinear B chart)
    ∃ V : Set E₀, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∃ c₀ : I → I → SchwartzMap E₀ ℂ, ∃ c₁ : I → ActionSlot I → SchwartzMap E₀ ℂ,
      ∃ c₂ : I → I → J → SchwartzMap E₀ ℂ,
        (∀ x ∈ V, ∀ i j d,
          DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x ∧
          (fun y => c₂ i j d y) =ᶠ[𝓝 x]
            fun y => (metricActionCoefficient S (d.1,i) (d.2,j) (G y) : ℂ)) ∧
        (∀ (h : E₀ → I → ℝ), ContDiffOn ℝ ∞ h U → ∀ x ∈ V, ∀ i : I,
          (linearizedCoordinateDensityEuler S g h x i : ℂ) =
            ((∑ j, (h x j : ℂ) * c₀ i j x) + ∑ s : ActionSlot I,
              (coordinateMetricFirstJet h x s : ℂ) * c₁ i s x) -
            ∑ a, ∑ s : ActionSlot I, c₂ i s.2 (a,s.1) x * (coordinateMetricSecondJet h x a s : ℂ)) := by
  intro U S g G
  let e := chartAt E₀ chart
  have hAssem : assembledCoordinateMetric S g = G :=
    assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric chart
  have hg : ContDiffOn ℝ ∞ g U := by
    apply contDiffOn_pi.mpr
    intro i
    change ContDiffOn ℝ ∞ (fun x => symmetricMetricScale i *
      metricComponents (coordinateBilinear B chart) x i.val.1 i.val.2) U
    exact contDiffOn_const.mul (contDiffOn_metricComponents B hB chart i.val.1 i.val.2)
  have hG : ContDiffOn ℝ ∞ G U :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j => contDiffOn_metricComponents B hB chart i j))
  have hnd : MapsTo G U nonsingularMetricDomain :=
    fun _ hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate chart hx
  have hDet (x : E₀) (hx : x ∈ U) : Matrix.det (assembleMetricComponents S (g x)) ≠ 0 := by
    change Matrix.det (assembledCoordinateMetric S g x) ≠ 0
    rw [hAssem]
    exact hnd hx
  obtain ⟨V₁,hV₁,hK₁,hU₁,c₀,c₁,h₀,h₁⟩ :=
    exists_actualEulerLowerCoefficients_schwartz_near S g hK e.open_target hKU hg hDet
  obtain ⟨V₂,hV₂,hK₂,hU₂,c₂,h₂⟩ :=
    exists_densityPrincipalCoefficients_schwartz_near S G hK e.open_target hKU hG hnd
  refine ⟨V₁ ∩ V₂,hV₁.inter hV₂,subset_inter hK₁ hK₂,inter_subset_left.trans hU₁,c₀,c₁,c₂,
    fun x hx i j d => h₂ i j d x hx.2,?_⟩
  intro h hh x hx i
  have hxU := hU₁ hx.1
  have he := linearizedCoordinateDensityEuler_eq_explicit_lower_coefficients S g h
    e.open_target hg hh x hxU (hDet x hxU) i
  rw [he]
  let p := coordinateEulerBackgroundJet S g x
  have hz (j : I) : c₀ i j x = (actualEulerZeroOrderCoefficient S i j p : ℂ) :=
    (h₀ i j x hx.1).self_of_nhds
  have hf (s : ActionSlot I) : c₁ i s x = (actualEulerFirstOrderCoefficient S i s p : ℂ) :=
    (h₁ i s x hx.1).self_of_nhds
  have ht (a : Fin 4) (s : ActionSlot I) :
      c₂ i s.2 (a,s.1) x = (metricActionCoefficient S (a,i) s p.1 : ℂ) := by
    change _ = (metricActionCoefficient S (a,i) s (assembledCoordinateMetric S g x) : ℂ)
    rw [hAssem]
    exact (h₂ i s.2 (a,s.1) x hx.2).2.self_of_nhds
  simp only [hz,hf,ht,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_mul,p]

end Burnett.V03.Palatini
