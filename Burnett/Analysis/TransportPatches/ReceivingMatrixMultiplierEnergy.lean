import Burnett.Analysis.TransportPatches.ClassicalMatrixMultiplier
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly

/-! The whole-space multiplier norm on the existing ordered covariance. -/

set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 5900000

noncomputable section

namespace Burnett.C02

open Set Filter Function MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.RicciSymbol (Index)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M J : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

private theorem original_matrixEnergy_entry
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ c.chart '' K) (d : Index)
    (T : ClassicalMatrixMultiplier J) (k : J) (i j : OrderedPair) :
    let hηc := hη.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u n (l : OrderedPair) := (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc
      (σ n) (d, l)).toLp 2 volume
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let F (p : Cosphere r) :=
      let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
      let w : ℝ := ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2
      (w : ℂ) * conj (T.energyPrincipal k i j ξ) * atlasAmplitudeMatrix c A.density p i j
    Integrable F τ ∧ Tendsto (fun n =>
      inner ℂ (fourierMultiplier (T.energySymbol k i j) (u n j)) (u n i))
      atTop (𝓝 (∫ p, F p ∂τ)) := by
  intro hηc u τ F
  let b (_ : E) (ξ : E) := T.energySymbol k i j ξ
  let a (_ : E) (ξ : E) := T.energyPrincipal k i j ξ
  have hb : ContDiffOn ℝ ∞ (uncurry b) (c.chart.target ×ˢ univ) :=
    ((T.energySymbol_smooth k i j).comp contDiff_snd).contDiffOn
  have ha : ContDiffOn ℝ ∞ (uncurry a) (c.chart.target ×ˢ ({0}ᶜ : Set E)) :=
    (T.energyPrincipal_smooth k i j).comp contDiffOn_snd (fun _ hz => hz.2)
  have hR : ∀ S : Set E, IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C := by
    intro S _ _
    obtain ⟨R, C, hC, hRC⟩ := T.energySymbol_order_minus_one k i j
    refine ⟨R, fun n => ⟨C, hC, ?_⟩⟩
    intro x _ ξ hξ
    change (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n
      (fun _ : E => T.energySymbol k i j ξ - T.energyPrincipal k i j ξ) x‖ ≤ C
    cases n with
    | zero =>
        rw [norm_iteratedFDeriv_zero]
        exact hRC ξ hξ
    | succ n =>
        rw [iteratedFDeriv_succ_const]
        simpa only [Pi.zero_apply, norm_zero, mul_zero] using hC
  obtain ⟨hInt, hLim⟩ := hPair c K hK hKc η η hη hη
    (fourierMultiplier (T.energySymbol k i j)) b a hb ha
    (fun _ _ t ht ξ hξ => T.energyPrincipal_degree k i j t ht ξ hξ) hR
    (fun f v _ _ => T.energySymbol_pairing k i j f v) (d, i) (d, j)
  have hF (p : Cosphere r) :
      (let z := fixedChartPhase c p.val
       conj ((physicalCoefficient η z.1 * physicalCoefficient η z.1) * a z.1 (WithLp.toLp 2 z.2)) *
         atlasOrderedJetEntry c A.density p (d, j) (d, i)) = F p := by
    change conj ((((η : E → ℝ) (fixedChartPhase c p.val).1 : ℝ) : ℂ) *
        (((η : E → ℝ) (fixedChartPhase c p.val).1 : ℝ) : ℂ) *
        T.energyPrincipal k i j (WithLp.toLp 2 (atlasChartUnitCovector c p))) *
      ((atlasChartUnitCovector c p d : ℂ) * (atlasChartUnitCovector c p d : ℂ) *
        atlasAmplitudeMatrix c A.density p i j) = _
    simp only [F, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, pow_two]
    ring
  rw [← funext hF]
  exact ⟨hInt, hLim⟩

/-- The actual whole-space norm of one multiplier row applied to one derivative
direction converges along the existing subsequence to its ordered covariance. -/
theorem tendsto_receiving_matrixMultiplierEnergy
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ c.chart '' K) (d : Index)
    (T : ClassicalMatrixMultiplier J) (k : J) :
    let hηc := hη.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u n (l : OrderedPair) := (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hηc
      (σ n) (d, l)).toLp 2 volume
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let H (p : Cosphere r) :=
      let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
      let P := T.principal ξ
      let w : ℝ := ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2
      w * ((P * atlasAmplitudeMatrix c A.density p * Pᴴ) k k).re
    Integrable H τ ∧ Tendsto (fun n => ‖T.output (u n) k‖^2)
      atTop (𝓝 (∫ p, H p ∂τ)) := by
  intro hηc u τ H
  let ξ (p : Cosphere r) := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let N (p : Cosphere r) := atlasAmplitudeMatrix c A.density p
  let w (p : Cosphere r) : ℝ :=
    ((η : E → ℝ) (fixedChartPhase c p.val).1)^2 * (atlasChartUnitCovector c p d)^2
  let F (i j : OrderedPair) (p : Cosphere r) := (w p : ℂ) * conj (T.energyPrincipal k i j (ξ p)) * N p i j
  let V (i j : OrderedPair) (n : ℕ) :=
    inner ℂ (fourierMultiplier (T.energySymbol k i j) (u n j)) (u n i)
  have hPairs (i j : OrderedPair) := original_matrixEnergy_entry r B g hB hg hn σ A hPair c K hK hKc η hη d T k i j
  have hI (i j : OrderedPair) : Integrable (F i j) τ := (hPairs i j).1
  have hV (i j : OrderedPair) : Tendsto (V i j) atTop (𝓝 (∫ p, F i j p ∂τ)) := (hPairs i j).2
  have hSum := tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun i _ =>
    tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun j _ => hV i j))
  let Q (p : Cosphere r) := ∑ i : OrderedPair, ∑ j : OrderedPair, F i j p
  have hQ : Integrable Q τ := integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))
  have hintegral : (∑ i : OrderedPair, ∑ j : OrderedPair, ∫ p, F i j p ∂τ) = ∫ p, Q p ∂τ := by
    simp only [Q]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
    exact Finset.sum_congr rfl (fun i _ => (integral_finset_sum _ (fun j _ => hI i j)).symm)
  rw [hintegral] at hSum
  have hRe (p : Cosphere r) : (Q p).re = H p := by
    have hDiag : Q p = (w p : ℂ) * (T.principal (ξ p) * N p * (T.principal (ξ p))ᴴ) k k := by
      rw [← T.principal_covariance_diag]
      simp only [Q, F, Finset.mul_sum, mul_assoc]
    rw [hDiag, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hEnergy (n : ℕ) : (∑ i : OrderedPair, ∑ j : OrderedPair, V i j n).re = ‖T.output (u n) k‖^2 := by
    rw [T.output_norm_sq]
    let W (i j : OrderedPair) := inner ℂ (u n i)
      (fourierMultiplier (T.energySymbol k i j) (u n j))
    have hC (i j : OrderedPair) : V i j n = conj (W i j) := (inner_conj_symm _ _).symm
    change (∑ i : OrderedPair, ∑ j : OrderedPair, V i j n).re = (∑ i : OrderedPair, ∑ j : OrderedPair, W i j).re
    simp only [hC, ← map_sum, Complex.conj_re]
  have hL := Complex.continuous_re.continuousAt.tendsto.comp hSum
  change Tendsto (fun n => (∑ i : OrderedPair, ∑ j : OrderedPair, V i j n).re) atTop
    (𝓝 ((∫ p, Q p ∂τ).re)) at hL
  have hre : (∫ p, Q p ∂τ).re = ∫ p, (Q p).re ∂τ := by
    simpa only [RCLike.re_to_complex] using (integral_re hQ).symm
  rw [hre] at hL
  simp only [hRe, hEnergy] at hL
  exact ⟨hQ.re.congr (Eventually.of_forall hRe), hL⟩

end Burnett.C02
