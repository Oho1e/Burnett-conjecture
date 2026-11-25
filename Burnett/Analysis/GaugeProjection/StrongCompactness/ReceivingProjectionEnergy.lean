import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectionEnergyPairing
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly

/-! The actual projected energy on one receiving chart and one derivative slot. -/
set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 4600000

noncomputable section
namespace Burnett.P01

open Set Filter Function MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.A02.FrequencySplit (tau)
open Burnett.RicciSymbol (Index)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Matrix Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => CoordinateSpace

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem pairing_for_projectionEnergySymbol
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ c.chart '' K) (d : Index) (k i j : OrderedPair) :
    let hηc := hη.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u n a b := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc (σ n) (d, a, b)
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let F (p : Cosphere r) :=
      let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
      let w : ℝ := ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2
      (w : ℂ) * projectionEnergyPrincipalSymbol k i j ξ * atlasAmplitudeMatrix c A.density p i j
    Integrable F τ ∧ Tendsto (fun n =>
      inner ℂ (fourierMultiplier (projectionEnergyComponentSymbol k i j) ((u n j.1 j.2).toLp 2 volume))
        ((u n i.1 i.2).toLp 2 volume)) atTop (𝓝 (∫ p, F p ∂τ)) := by
  intro hηc u τ F
  let b (_ : E) (ξ : E) := projectionEnergyComponentSymbol k i j ξ
  let a (_ : E) (ξ : E) := projectionEnergyPrincipalSymbol k i j ξ
  have hb : ContDiffOn ℝ ∞ (uncurry b) (c.chart.target ×ˢ univ) :=
    ((projectionEnergyComponentSymbol_smooth k i j).comp contDiff_snd).contDiffOn
  have ha : ContDiffOn ℝ ∞ (uncurry a) (c.chart.target ×ˢ ({0}ᶜ : Set E)) :=
    (projectionEnergyPrincipalSymbol_smoothOn k i j).comp contDiffOn_snd (fun _ hz => hz.2)
  have hR : ∀ S : Set E, IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C := by
    intro S _ _
    refine ⟨2 / tau + 1, fun n => ⟨0, le_rfl, ?_⟩⟩
    intro x _ ξ hξ
    have he : (fun y => b y ξ - a y ξ) = (fun _ : E => (0 : ℂ)) := by
      funext y
      exact sub_eq_zero.mpr (projectionEnergyComponentSymbol_eq_principal_of_large k i j ξ
        ((lt_add_of_pos_right _ zero_lt_one).trans_le hξ))
    simp only [he, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero, mul_zero, le_refl]
  obtain ⟨hInt, hLim⟩ := hPair c K hK hKc η η hη hη
    (fourierMultiplier (projectionEnergyComponentSymbol k i j)) b a hb ha
    (fun _ _ s hs ξ _ => projectionEnergyPrincipalSymbol_scale k i j s hs ξ) hR
    (fun f v _ _ => projectionEnergyComponentSymbol_actualPairing k i j v f) (d, i) (d, j)
  have he (p : Cosphere r) :
      (let z := fixedChartPhase c p.val
       conj ((physicalCoefficient η z.1 * physicalCoefficient η z.1) * a z.1 (WithLp.toLp 2 z.2)) *
         atlasOrderedJetEntry c A.density p (d, j) (d, i)) = F p := by
    change conj ((((η : E → ℝ) (fixedChartPhase c p.val).1 : ℝ) : ℂ) *
        (((η : E → ℝ) (fixedChartPhase c p.val).1 : ℝ) : ℂ) *
        projectionEnergyPrincipalSymbol k i j (WithLp.toLp 2 (atlasChartUnitCovector c p))) *
      ((atlasChartUnitCovector c p d : ℂ) * (atlasChartUnitCovector c p d : ℂ) *
        atlasAmplitudeMatrix c A.density p i j) = _
    simp only [F, map_mul, Complex.conj_ofReal, projectionEnergyPrincipalSymbol_conj,
      Complex.ofReal_mul, pow_two]
    ring
  have hEq := funext he
  rw [← hEq]
  exact ⟨hInt, hLim⟩

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- For the actual common refinement, the whole-space squared norm of a
single projected component converges to its original diagonal covariance. -/
theorem tendsto_receiving_projectionEnergy
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ c.chart '' K) (d : Index) (k : OrderedPair) :
    let hηc := hη.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u n a b := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc (σ n) (d, a, b)
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let H (p : Cosphere r) :=
      let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
      let P := principalGaugeProjectionMatrix ξ
      let w : ℝ := ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2
      w * ((P * atlasAmplitudeMatrix c A.density p * Pᴴ) k k).re
    Integrable H τ ∧ Tendsto (fun n => ‖(projectionFullSchwartz (u n) k.1 k.2).toLp 2 volume‖^2)
      atTop (𝓝 (∫ p, H p ∂τ)) := by
  intro hηc u τ H
  let ξ (p : Cosphere r) := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let N (p : Cosphere r) := atlasAmplitudeMatrix c A.density p
  let w (p : Cosphere r) : ℝ :=
    ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2
  let F (i j : OrderedPair) (p : Cosphere r) :=
    (w p : ℂ) * projectionEnergyPrincipalSymbol k i j (ξ p) * N p i j
  have hPairs (i j : OrderedPair) :=
    pairing_for_projectionEnergySymbol r B g hB hg hn σ A hPair c K hK hKc η hη d k i j
  have hI (i j : OrderedPair) : Integrable (F i j) τ := (hPairs i j).1
  let V (i j : OrderedPair) (n : ℕ) := inner ℂ
    (fourierMultiplier (projectionEnergyComponentSymbol k i j) ((u n j.1 j.2).toLp 2 volume))
    ((u n i.1 i.2).toLp 2 volume)
  have hV (i j : OrderedPair) : Tendsto (V i j) atTop (𝓝 (∫ p, F i j p ∂τ)) := (hPairs i j).2
  have hSum := tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun i _ =>
    tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun j _ => hV i j))
  let J (p : Cosphere r) := ∑ i : OrderedPair, ∑ j : OrderedPair, F i j p
  have hJ : Integrable J τ := integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))
  have hintegral : (∑ i : OrderedPair, ∑ j : OrderedPair, ∫ p, F i j p ∂τ) = ∫ p, J p ∂τ := by
    simp only [J]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
    exact Finset.sum_congr rfl (fun i _ => (integral_finset_sum _ (fun j _ => hI i j)).symm)
  rw [hintegral] at hSum
  have hJR (p : Cosphere r) : (J p).re = H p := by
    have hJ' : J p = (w p : ℂ) *
        (principalGaugeProjectionMatrix (ξ p) * N p * (principalGaugeProjectionMatrix (ξ p))ᴴ) k k := by
      rw [← sum_projectionEnergyPrincipalSymbol_mul_matrix]
      simp only [J, F, Finset.mul_sum, mul_assoc]
    rw [hJ', Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hVI (n : ℕ) : (∑ i : OrderedPair, ∑ j : OrderedPair, V i j n).re =
      ‖(projectionFullSchwartz (u n) k.1 k.2).toLp 2 volume‖^2 := by
    rw [projectionFullSchwartz_component_norm_sq_eq_energyPairings]
    let W (i j : OrderedPair) := inner ℂ ((u n i.1 i.2).toLp 2 volume)
      (fourierMultiplier (projectionEnergyComponentSymbol k i j) ((u n j.1 j.2).toLp 2 volume))
    have hC (i j : OrderedPair) : V i j n = conj (W i j) := (inner_conj_symm _ _).symm
    change (∑ i : OrderedPair, ∑ j : OrderedPair, V i j n).re = (∑ i : OrderedPair, ∑ j : OrderedPair, W i j).re
    simp only [hC, ← map_sum, Complex.conj_re]
  have hLim := Complex.continuous_re.continuousAt.tendsto.comp hSum
  change Tendsto (fun n => (∑ i : OrderedPair, ∑ j : OrderedPair, V i j n).re) atTop
    (𝓝 ((∫ p, J p ∂τ).re)) at hLim
  have hre : (∫ p, J p ∂τ).re = ∫ p, (J p).re ∂τ := by
    simpa only [RCLike.re_to_complex] using (integral_re hJ).symm
  rw [hre] at hLim
  simp only [hJR, hVI] at hLim
  have hJRe : Integrable (fun p => (J p).re) τ := hJ.re
  exact ⟨hJRe.congr (Eventually.of_forall hJR), hLim⟩

end Burnett.P01
