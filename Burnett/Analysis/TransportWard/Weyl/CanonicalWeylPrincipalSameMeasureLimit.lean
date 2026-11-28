import Burnett.Analysis.TransportWard.Weyl.ActualCanonicalWeylRegularity
import Burnett.Analysis.TransportWard.Weyl.QuadraticClassicalProfile
import Burnett.Analysis.TransportWard.Weyl.SameMeasureNullIntegral

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 3000

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.RicciSymbol Burnett.V02
open Burnett.A02.FrequencySplit (tau)
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket canonicalBracket_radial)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.Overlap
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Topology Manifold BigOperators FourierTransform ComplexConjugate

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

open private canonicalBracket_eq_zero_off_base from Burnett.Analysis.TransportWard.Weyl.ActualWeylSameMeasureContraction

private theorem classicalLeftPairing_real_smul (p : E₀ → E₀ → ℂ) (s t : ℝ)
    (u v : SchwartzMap E₀ ℂ) :
    classicalLeftPairing p ((s : ℂ) • u) ((t : ℂ) • v) =
      ((t : ℂ) * (s : ℂ)) * classicalLeftPairing p u v := by
  have hAct (x : E₀) : firstOrderAction p (((t : ℂ) • v : SchwartzMap E₀ ℂ) : E₀ → ℂ) x =
      (t : ℂ) * firstOrderAction p v x := by
    rw [firstOrderAction_eq_leftActionIntegrand p ((t : ℂ) • v) x,
      firstOrderAction_eq_leftActionIntegrand p v x,← integral_const_mul]
    apply integral_congr_ae
    refine .of_forall fun ξ => ?_
    have hF : 𝓕 (((t : ℂ) • v : SchwartzMap E₀ ℂ) : E₀ → ℂ) ξ =
        (t : ℂ) * 𝓕 (v : E₀ → ℂ) ξ :=
      congrArg (fun w : SchwartzMap E₀ ℂ => w ξ)
        ((SchwartzMap.fourierTransformCLM ℂ).map_smul (t : ℂ) v)
    unfold leftActionIntegrand
    rw [hF]
    ring
  unfold classicalLeftPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  change conj (((s : ℂ) • u) x) *
    firstOrderAction p (((t : ℂ) • v : SchwartzMap E₀ ℂ) : E₀ → ℂ) x =
      ((t : ℂ) * (s : ℂ)) * (conj (u x) * firstOrderAction p v x)
  rw [hAct x]
  simp only [SchwartzMap.smul_apply,smul_eq_mul,map_mul,Complex.conj_ofReal]
  ring

private theorem frozenDensityPrincipalPhase_radial (G : E₀ → Burnett.Analysis.TransportWardSymbol.Mat)
    (i j : I) (y : E₀) (s : ℝ) (ξ : Covector) :
    frozenDensityPrincipalPhase orthonormalMetricDirection (G y) (s • ξ) i j =
      s^2 * frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ξ i j := by
  unfold frozenDensityPrincipalPhase
  simp only [Finset.mul_sum,Pi.smul_apply,smul_eq_mul]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The actual second-order canonical Weyl pairing for the original
compact perturbation has the factor-four limit on the same physical
measure as the Einstein moment, on a represented preferred chart. -/
theorem tendsto_preferredLocalizedCanonicalWeylPrincipalPair_sameMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ (AtlasChart.atPoint q.center).chart '' K)
    (a β : E₀ → Covector → ℝ) (L : Set E₀) (hL : IsCompact L)
    (hLU : L ⊆ (chartAt E₀ q.center).target)
    (haS : ∀ x ∉ L, ∀ ξ, a x ξ = 0) (hβS : ∀ x ∉ L, ∀ ξ, β x ξ = 0)
    (hχL : ∀ x ∈ L, (χ : E₀ → ℝ) x = 1)
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)))
    (hβDiff : ContDiff ℝ ∞ (uncurry β))
    (haD : ∀ x (s : ℝ), 0 < s → ∀ ξ : Covector, ξ ≠ 0 → a x (s • ξ) = s * a x ξ)
    (R : ℝ) (hMatch : ∀ y ξ, R ≤ ‖(WithLp.toLp 2 ξ : E₀)‖ → β y ξ = a y ξ) :
    let c := AtlasChart.atPoint q.center
    let G := chartLowerMetric B q.center
    let P (i j : I) (x ξ : E₀) : ℂ :=
      canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j)
        β x (fun k => (tau • ξ) k)
    let hχc : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target :=
      hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left (fun _ hy => (hSub hy).1)))
    let U := fixedWeylPerturbationSchwartz B g hB hg c χ hχc
    let F (p : Cosphere r) :=
      canonicalBracket (coordinateHamiltonian G) a (c.chart (projection p)) (atlasChartUnitCovector c p)
    Tendsto (fun n => ∑ i : I, ∑ j : I,
      classicalLeftPairing (P i j) ((symmetricMetricScale i : ℂ) • U (σ n) i.val)
        ((symmetricMetricScale j : ℂ) • U (σ n) j.val)) atTop
      (𝓝 (4 * ∫ p, (F p : ℂ) ∂(μ.restrict (amplitudeCosphereWindow r K)))) := by
  intro c G P hχc U F
  let PHom (i j : I) (x ξ : E₀) : ℂ :=
    canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j)
      a x (WithLp.ofLp ξ)
  let τ := A.control.restrict (amplitudeCosphereWindow r K)
  let hKc : K ⊆ c.chart.source := fun y hy => (hSub hy).1
  let scale (i j : I) := (symmetricMetricScale j : ℂ) * (symmetricMetricScale i : ℂ)
  let J (i j : I) (p : Cosphere r) :=
    let x := c.chart (projection p)
    ∑ l : Fin 4, ((((χ : E₀ → ℝ) x)^2 * (fixedCoordinateVolumeDensity B c x)⁻¹ : ℝ) : ℂ) *
      homogeneousGradientTest (PHom i j) x (WithLp.toLp 2 (atlasChartUnitCovector c p)) *
        atlasOrderedJetEntry c A.density p (l,i.val) (l,j.val)
  have hPoisson (i j : I) (x : E₀) (s : ℝ) (hs : 0 < s) (ξ : Covector) (hξ : ξ ≠ 0) :
      canonicalBracket (fun y ζ => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j)
          a x (s • ξ) =
        s^2 * canonicalBracket (fun y ζ =>
          frozenDensityPrincipalPhase orthonormalMetricDirection (G y) ζ i j) a x ξ :=
    canonicalBracket_radial univ isOpen_univ _ a x (mem_univ x) ξ hξ s hs
      (fun y _ ζ _ => frozenDensityPrincipalPhase_radial G i j y s ζ) (fun y _ ζ hζ => haD y s hs ζ hζ)
  have hD (i j : I) : ∀ x (s : ℝ), 0 < s → ∀ ξ ≠ 0, PHom i j x (s • ξ) = (s : ℂ)^2 * PHom i j x ξ := by
    intro x s hs ξ hξ
    have he : WithLp.ofLp ξ ≠ 0 := by
      intro h
      apply hξ
      exact congrArg (WithLp.toLp 2) h
    change (canonicalBracket _ a x (s • WithLp.ofLp ξ) : ℂ) =
      (s : ℂ)^2 * (canonicalBracket _ a x (WithLp.ofLp ξ) : ℂ)
    rw [hPoisson i j x s hs (WithLp.ofLp ξ) he]
    push_cast
    rfl
  have hLarge (i j : I) (x ξ : E₀) (hξ : max 1 (R+1) ≤ ‖ξ‖) :
      P i j x ξ = (tau : ℂ)^2 * PHom i j x ξ :=
    canonicalBracket_radian_high_eq _ a β R hMatch
      (fun y s _ ζ _ => frozenDensityPrincipalPhase_radial G i j y s ζ) haD x ξ hξ
  have hPSupp (i j : I) (x : E₀) (hx : x ∉ L) (ξ : E₀) : P i j x ξ = 0 := by
    simp only [P,canonicalBracket_eq_zero_off_base hL.isClosed β _ hβS x hx,Complex.ofReal_zero]
  have hHomSupp (i j : I) (x : E₀) (hx : x ∉ L) (ξ : E₀) : PHom i j x ξ = 0 := by
    simp only [PHom,canonicalBracket_eq_zero_off_base hL.isClosed a _ haS x hx,Complex.ofReal_zero]
  have hPS (i j : I) : ContDiff ℝ ∞ (uncurry (P i j)) :=
    contDiff_actualCanonicalWeyl_fullSymbol B hB hSig q.center β hβDiff L hL.isClosed hLU hβS i j
  have hHomS (i j : I) : ContDiffOn ℝ ∞ (uncurry (PHom i j)) (univ ×ˢ ({0}ᶜ : Set E₀)) :=
    contDiffOn_actualCanonicalWeyl_homogeneousSymbol B hB hSig q.center a haDiff L hL.isClosed hLU haS i j
  have hPB (i j : I) : BaseDerivativeBounds (P i j) (fun ξ => (1 + ‖ξ‖)^2) :=
    BaseDerivativeBounds.of_quadratic_classical_tail hL (hPSupp i j) (hHomSupp i j) (hPS i j)
      (hHomS i j) (hD i j) (max 1 (R+1)) (hLarge i j)
  have hEntry (i j : I) : Integrable (J i j) τ ∧ Tendsto
      (fun n => classicalLeftPairing (P i j) (U (σ n) i.val) (U (σ n) j.val))
      atTop (𝓝 (∫ p, J i j p ∂τ)) := by
    exact tendsto_originalLocalizedWeylPrincipalPair r B g hB hg hSig.isSymmetric hsG
      hSig.isNondegenerate hnG hconv hb hv σ hσ A hA c K hK hKc χ hχ (P i j) (PHom i j) L hL
      (hPSupp i j) (hHomSupp i j) (hPS i j) (hPB i j) (hHomS i j) (hD i j)
      (max 1 (R+1)) (hLarge i j) i.val j.val
  let E (i j : I) (p : Cosphere r) := scale i j * J i j p
  let ESum (p : Cosphere r) := ∑ i : I, ∑ j : I, E i j p
  have hE (i j : I) : Integrable (E i j) τ :=
    (hEntry i j).1.const_mul (scale i j)
  have hRow (i : I) : Integrable (fun p => ∑ j, E i j p) τ :=
    integrable_finset_sum _ (fun j _ => hE i j)
  have hEntryLim (i j : I) : Tendsto (fun n => scale i j *
      classicalLeftPairing (P i j) (U (σ n) i.val) (U (σ n) j.val)) atTop (𝓝 (∫ p, E i j p ∂τ)) := by
    rw [integral_const_mul]
    exact ((hEntry i j).2).const_mul (scale i j)
  have hTot := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun j _ => hEntryLim i j))
  have hInt : (∫ p, ESum p ∂τ) = ∑ i : I, ∑ j : I, ∫ p, E i j p ∂τ :=
    (integral_finset_sum _ (fun i _ => hRow i)).trans
      (Finset.sum_congr rfl (fun i _ => integral_finset_sum _ (fun j _ => hE i j)))
  have hKernel := ae_preferredWeyl_gradientContraction_samePhysicalWeight r B g hB hSig hg hsG hnG
    hconv hb hv σ hσ A hA.2.2.2.2.1 q ν hf hRep K hK hSub a χ L hL.isClosed haS hχL
  have hAE : ESum =ᵐ[τ] (fun p =>
      if hamiltonian B hSig.isNondegenerate p = 0 then
        4 * (intrinsicPhysicalWeight B hSig.isNondegenerate A.density p : ℂ) * (F p : ℂ) else 0) := by
    filter_upwards [hKernel] with p hp
    rw [← hp]
    simp only [ESum,E,J,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => ?_)))
    simp only [scale,homogeneousGradientTest,PHom,WithLp.ofLp_toLp]
    ring
  rw [← hInt,integral_congr_ae hAE,
    integral_nullCompression_samePhysicalMeasure r B hSig.isNondegenerate A μ hμ K hK.isClosed.measurableSet F] at hTot
  simpa only [classicalLeftPairing_real_smul,scale] using hTot

end Burnett.V03.Palatini
