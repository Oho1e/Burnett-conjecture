import Burnett.Analysis.TransportWard.Weyl.WeylGradientLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalLocalizedWeylInputBounds
import Burnett.Analysis.TransportWard.Weyl.OriginalLocalizedWeylPrincipalLimit
import Burnett.Analysis.TransportWard.Weyl.CanonicalPoissonSymbolRegularity
import Burnett.Analysis.TransportWard.Weyl.ActualWeylSameMeasureContraction

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2200

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricTransition Burnett.RicciSymbol Burnett.V02
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.A02.FrequencySplit (tau)
open scoped ContDiff Topology Manifold BigOperators Matrix.Norms.Elementwise

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "P" => E₀ × Covector

open private canonicalBracket_eq_zero_off_base from Burnett.Analysis.TransportWard.Weyl.ActualWeylSameMeasureContraction

private theorem canonicalBracket_global_fiber_of_baseWindow
    {U L : Set E₀} (hU : IsOpen U) (hL : IsClosed L) (hLU : L ⊆ U)
    {V : Set Covector} (hV : IsOpen V) (A a : E₀ → Covector → ℝ)
    (hAD : ContDiffOn ℝ ∞ (uncurry A) (U ×ˢ V))
    (haD : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ V))
    (haS : ∀ x ∉ L, ∀ ξ, a x ξ = 0) :
    ContDiffOn ℝ ∞ (uncurry (canonicalBracket A a)) (univ ×ˢ V) := by
  have hD := canonicalBracket_contDiffOn (hU.prod hV) hAD haD
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hX : z.1 ∈ L
  · exact hD.contDiffAt ((hU.prod hV).mem_nhds ⟨hLU hX,hz.2⟩)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually (hL.isOpen_compl.mem_nhds hX)] with w hw
    exact canonicalBracket_eq_zero_off_base hL a A haS w.1 hw w.2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

private theorem contDiffOn_actualFrozenDensityPrincipalPhase {ι : Type*} (S : ι → Mat)
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (i j : ι) :
    let E := (chartAt E₀ c).target
    ContDiffOn ℝ ∞ (uncurry (fun x ξ =>
      frozenDensityPrincipalPhase S (chartLowerMetric B c x) ξ i j)) (E ×ˢ univ) := by
  intro E
  let G := chartLowerMetric B c
  obtain ⟨hG,hDet,_⟩ := chartLowerMetric_phase_inputs B hB hSig.isNondegenerate hSig.isSymmetric c
  have hM : ContDiffOn ℝ ∞ G E := contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hG a b))
  have hC (a b : Fin 4) : ContDiffOn ℝ ∞ (fun x => metricActionCoefficient S (a,i) (b,j) (G x)) E :=
    (contDiffOn_metricActionCoefficient S (a,i) (b,j)).comp hM (fun x hx => hDet x hx)
  have hP (k : Fin 4) : ContDiff ℝ ∞ (fun z : P => z.2 k) :=
    (ContinuousLinearMap.proj k : Covector →L[ℝ] ℝ).contDiff.comp contDiff_snd
  change ContDiffOn ℝ ∞ (fun z : P => ∑ a, ∑ b,
    metricActionCoefficient S (a,i) (b,j) (G z.1) * (z.2 a * z.2 b)) (E ×ˢ univ)
  exact ContDiffOn.sum (fun a _ => ContDiffOn.sum fun b _ =>
    ((hC a b).comp contDiff_fst.contDiffOn (fun _ hz => hz.1)).mul
      (((hP a).mul (hP b)).contDiffOn))

/-- The full infrared test uses the actual chart metric on its closed
base support. Its canonical quadratic symbol is smooth on all frequencies. -/
theorem contDiff_actualCanonicalWeyl_fullSymbol
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B) (c : M)
    (β : E₀ → Covector → ℝ) (hβ : ContDiff ℝ ∞ (uncurry β))
    (L : Set E₀) (hL : IsClosed L) (hLU : L ⊆ (chartAt E₀ c).target)
    (hSupp : ∀ x ∉ L, ∀ ξ, β x ξ = 0) (i j : I) :
    ContDiff ℝ ∞ (fun p : E₀ × E₀ =>
      (canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection
        (chartLowerMetric B c y) ζ i j) β p.1 (fun k => (tau • p.2) k) : ℂ)) := by
  let G := chartLowerMetric B c
  let A (y : E₀) (ζ : Covector) := frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j
  have hD := canonicalBracket_global_fiber_of_baseWindow (chartAt E₀ c).open_target hL hLU isOpen_univ
    A β (contDiffOn_actualFrozenDensityPrincipalPhase orthonormalMetricDirection B hB hSig c i j)
    hβ.contDiffOn hSupp
  rw [univ_prod_univ] at hD
  let Q : E₀ ≃L[ℝ] Covector := PiLp.continuousLinearEquiv 2 ℝ _
  have hQ : ContDiff ℝ ∞ (fun p : E₀ × E₀ => (p.1,Q (tau • p.2))) :=
    contDiff_fst.prodMk (Q.contDiff.comp (contDiff_const.smul contDiff_snd))
  exact Complex.ofRealCLM.contDiff.comp ((contDiffOn_univ.mp hD).comp hQ)

/-- The actual unregularized Poisson test is jointly smooth on the
punctured frequency domain, including its zero region off the chart. -/
theorem contDiffOn_actualCanonicalWeyl_homogeneousSymbol
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B) (c : M)
    (a : E₀ → Covector → ℝ)
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)))
    (L : Set E₀) (hL : IsClosed L) (hLU : L ⊆ (chartAt E₀ c).target)
    (hSupp : ∀ x ∉ L, ∀ ξ, a x ξ = 0) (i j : I) :
    ContDiffOn ℝ ∞ (fun p : E₀ × E₀ =>
      (canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection
        (chartLowerMetric B c y) ζ i j) a p.1 (WithLp.ofLp p.2) : ℂ)) (univ ×ˢ ({0}ᶜ : Set E₀)) := by
  let G := chartLowerMetric B c
  let A (y : E₀) (ζ : Covector) := frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j
  have hD := canonicalBracket_global_fiber_of_baseWindow (chartAt E₀ c).open_target hL hLU
    isOpen_compl_singleton A a
    ((contDiffOn_actualFrozenDensityPrincipalPhase orthonormalMetricDirection B hB hSig c i j).mono
      (prod_mono_right (subset_univ _))) (ha.mono (prod_mono_left (subset_univ _))) hSupp
  let Q : E₀ ≃L[ℝ] Covector := PiLp.continuousLinearEquiv 2 ℝ _
  have hQ : ContDiff ℝ ∞ (fun p : E₀ × E₀ => (p.1,Q p.2)) :=
    contDiff_fst.prodMk (Q.contDiff.comp contDiff_snd)
  have hInto : MapsTo (fun p : E₀ × E₀ => (p.1,Q p.2)) (univ ×ˢ ({0}ᶜ : Set E₀))
      (univ ×ˢ ({0}ᶜ : Set Covector)) := fun _ hp => ⟨mem_univ _,
        fun h => hp.2 (Q.injective (h.trans Q.map_zero.symm))⟩
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hD.comp hQ.contDiffOn hInto)

end Burnett.V03.Palatini
