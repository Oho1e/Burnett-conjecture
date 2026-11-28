import Burnett.Analysis.TransportWard.Weyl.OriginalLebesgueClassicalLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalLocalizedWeylInputBounds
import Burnett.Analysis.TransportWard.Weyl.WeylGradientLimit
import Burnett.Analysis.Microlocal.Overlap.PairingReplacement

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2700

noncomputable section

namespace Burnett.V03

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.Fourier
open Burnett.A02.FrequencySplit (tau)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedGradientSchwartz)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology InnerProduct BigOperators

local notation "E₀" => CoordinateSpace
local notation "D₁" => frozenSchwartzCoordinatePartial

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- For the actual cutoff perturbation fields, a quadratic principal
Weyl test reads the four diagonal raw gradient entries of the same F05
amplitude. It uses the true Lebesgue normalization. -/
theorem tendsto_originalLocalizedWeylPrincipalPair
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart '' K)
    (b bHom : E₀ → E₀ → ℂ) (S : Set E₀) (hS : IsCompact S)
    (hbS : ∀ x ∉ S, ∀ ξ, b x ξ = 0) (hHomS : ∀ x ∉ S, ∀ ξ, bHom x ξ = 0)
    (hbDiff : ContDiff ℝ ∞ (uncurry b)) (hbB : BaseDerivativeBounds b (fun ξ => (1 + ‖ξ‖)^2))
    (hHomDiff : ContDiffOn ℝ ∞ (uncurry bHom) (univ ×ˢ ({0}ᶜ : Set E₀)))
    (hHomDegree : ∀ x (s : ℝ), 0 < s → ∀ ξ ≠ 0, bHom x (s • ξ) = (s : ℂ)^2 * bHom x ξ)
    (R : ℝ) (hTail : ∀ x ξ, R ≤ ‖ξ‖ → b x ξ = (tau : ℂ)^2 * bHom x ξ)
    (i j : Pair) :
    let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let U := fixedWeylPerturbationSchwartz B g hB hg c χ hχc
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let F (p : Cosphere r) :=
      let x := c.chart (projection p)
      ∑ l : Fin 4, ((((χ : E₀ → ℝ) x)^2 * (fixedCoordinateVolumeDensity B c x)⁻¹ : ℝ) : ℂ) *
        homogeneousGradientTest bHom x (WithLp.toLp 2 (atlasChartUnitCovector c p)) *
          atlasOrderedJetEntry c A.density p (l,i) (l,j)
    Integrable F τ ∧
      Tendsto (fun n => classicalLeftPairing b (U (σ n) i) (U (σ n) j))
        atTop (𝓝 (∫ p, F p ∂τ)) := by
  intro hχc U τ F
  let q := regularizedGradientSymbol b
  let a := homogeneousGradientTest bHom
  let W := fixedGradientSchwartz B g hB hg c χ hχc
  have hqDiff := regularizedGradientSymbol_smooth hbDiff
  have haDiff := homogeneousGradientTest_smooth hHomDiff
  have haDegree := homogeneousGradientTest_degreeZero hHomDegree
  have haZero : ContDiff ℝ ∞ (fun x => a x 0) := by
    rw [show (fun x => a x 0) = fun _ => 0 from funext (homogeneousGradientTest_zero bHom)]
    exact contDiff_const
  have hqZero (x : E₀) (hx : x ∉ S) (ξ : E₀) : q x ξ = 0 := by
    simp only [q,regularizedGradientSymbol,hbS x hx,mul_zero]
  have hqSupport (ξ : E₀) : tsupport (fun x => q x ξ) ⊆ S :=
    closure_minimal (fun x hx => by by_contra h; exact hx (hqZero x h ξ)) hS.isClosed
  have haSupport := homogeneousGradientTest_support hS hHomS
  have hLarge := regularizedGradientSymbol_classical_tail hS hHomS hHomDiff hHomDegree R hTail
  obtain ⟨T,hAct,_⟩ := exists_classicalFullSymbolOperator q a S hS hqSupport haSupport
    hqDiff haDiff haZero haDegree (max 1 R) hLarge
  obtain ⟨hU0,⟨C,_,hRawBound⟩,hBounds⟩ := exists_original_fixedWeylPerturbationSchwartz_bounds
    r B g hB hg hnB hconv hb c χ hχc
  obtain ⟨M,_,hUB,hDB⟩ := hBounds j
  have hUS : Tendsto (fun n => ‖(U (σ n) i).toLp 2 volume‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using ((hU0 i).comp hσ.tendsto_atTop).norm
  have hP := tendsto_classicalLeftPairing_sub_regularizedGradientPair_zero hbDiff hbB hS hbS
    (fun n => U (σ n) j) (fun n => U (σ n) i) M (fun n => hUB (σ n))
    (fun l n => hDB l (σ n)) hUS
  let W₀ (l : Fin 4) (p : Cosphere r) :=
    let x := c.chart (projection p)
    ((((χ : E₀ → ℝ) x)^2 * (fixedCoordinateVolumeDensity B c x)⁻¹ : ℝ) : ℂ) *
      a x (WithLp.toLp 2 (atlasChartUnitCovector c p)) * atlasOrderedJetEntry c A.density p (l,i) (l,j)
  have hRaw (l : Fin 4) : Integrable (W₀ l) τ ∧ Tendsto
      (fun n => classicalLeftPairing q (W (σ n) (l,i)) (W (σ n) (l,j)))
        atTop (𝓝 (∫ p, W₀ l p ∂τ)) :=
    tendsto_originalLebesgue_receivingFullClassicalPairing r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ
      A hA c K hK hKc χ hχ q a S hS hqSupport haSupport hqDiff haDiff haZero haDegree (max 1 R) hLarge (l,i) (l,j)
  have hGrad (l : Fin 4) : Tendsto (fun n => classicalLeftPairing q (D₁ l (U (σ n) i)) (D₁ l (U (σ n) j)))
      atTop (𝓝 (∫ p, W₀ l p ∂τ)) := by
    have hi := (tendsto_fixedWeylPerturbationSchwartz_partial_sub_rawGradient
      r B g hB hg hconv c χ hχc (l,i)).comp hσ.tendsto_atTop
    have hj := (tendsto_fixedWeylPerturbationSchwartz_partial_sub_rawGradient
      r B g hB hg hconv c χ hχc (l,j)).comp hσ.tendsto_atTop
    have hR := tendsto_orderedPairing_sub_of_strong_replacement T
      (fun n => (D₁ l (U (σ n) i)).toLp 2 volume) (fun n => (D₁ l (U (σ n) j)).toLp 2 volume)
      (fun n => (W (σ n) (l,i)).toLp 2 volume) (fun n => (W (σ n) (l,j)).toLp 2 volume)
      M C (fun n => hDB l (σ n)) (fun n => hRawBound (σ n) (l,i)) hi hj
    simp only [hAct] at hR
    have hSum := hR.add (hRaw l).2
    rw [zero_add] at hSum
    exact hSum.congr (fun n => sub_add_cancel _ _)
  have hIF : Integrable F τ := integrable_finset_sum _ (fun l _ => (hRaw l).1)
  have hInt : (∫ p, F p ∂τ) = ∑ l, ∫ p, W₀ l p ∂τ :=
    integral_finset_sum _ (fun l _ => (hRaw l).1)
  have hG := tendsto_finset_sum Finset.univ (fun l _ => hGrad l)
  have hTot := hP.add hG
  rw [zero_add,← hInt] at hTot
  exact ⟨hIF,hTot.congr (fun n => sub_add_cancel _ _)⟩

end Burnett.V03
