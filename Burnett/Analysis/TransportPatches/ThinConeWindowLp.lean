import Burnett.Analysis.TransportPatches.ActualThinScreenCombination
import Burnett.Analysis.TransportPatches.WideWindowSphereJets
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

/-! The fixed thin profile and its complement are bounded uniformly over the frozen centers. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 7300000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.Geometry
open Burnett.A02.FrequencySplit (E homogeneous_multiplier_all_Lp_sphere_bound)
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile thinConeProfile_contDiffOn thinConeProfile_degreeZero
  scaledConeRatio descendingProfile_contDiff)
open scoped ContDiff ENNReal Manifold

open private joint_phase_smooth from Burnett.Analysis.TransportPatches.WideWindowSphereJets

/-- Quantitative Mikhlin on the literal existing Fourier output. This applies
to inputs lying in both spaces, including the already formed wide errors. -/
theorem exists_scalarFourierMultiplier_Lp_bound (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E → ℝ), ContDiffOn ℝ ∞ a ({0}ᶜ : Set E) →
      (∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = a ξ) → ∀ J : ℝ, 0 ≤ J →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n a ξ‖ ≤ J) →
      ∀ (M : BoundedSymbol E), (∀ ξ, M ξ = (a ξ : ℂ)) →
      ∀ (f : ComplexL2 E), MemLp (f : E → ℂ) (ENNReal.ofReal p) volume →
      let F := fourierMultiplier M f
      MemLp (F : E → ℂ) (ENNReal.ofReal p) volume ∧
        (eLpNorm (F : E → ℂ) (ENNReal.ofReal p) volume).toReal ≤
          C * J * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume).toReal := by
  obtain ⟨C, hC, hQuant⟩ := homogeneous_multiplier_all_Lp_sphere_bound p hp
  refine ⟨C, hC, ?_⟩
  intro a ha hDegree J hJ hJets M hM f hf F
  let P := ENNReal.ofReal p
  have hP : 1 ≤ P := by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  letI : Fact (1 ≤ P) := ⟨hP⟩
  obtain ⟨M', T, hM', hT, hL2, _⟩ := hQuant a ha hDegree J hJ hJets
  have hRep : (T (hf.toLp f) : E → ℂ) =ᵐ[volume] (F : E → ℂ) := by
    have h := hL2 (f : E → ℂ) (Lp.memLp f) hf
    rw [Lp.toLp_coeFn] at h
    rw [fourierMultiplier_congr_ae M' M (Eventually.of_forall fun ξ => (hM' ξ).trans (hM ξ).symm)] at h
    exact h
  refine ⟨(memLp_congr_ae hRep).1 (Lp.memLp _), ?_⟩
  rw [← eLpNorm_congr_ae hRep, ← Lp.norm_def]
  have hn : ‖hf.toLp f‖ = (eLpNorm (f : E → ℂ) P volume).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  rw [← hn]
  exact hT _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

private theorem chartThinProfile_jointSmooth (B : Field (M := M)) (c : AtlasChart M)
    (hB : IsSmooth B) (hn : IsNondegenerate B) (η i o : ℝ) :
    ContDiffOn ℝ ∞ (fun p : E × E => thinConeProfile (chartInverseMetric B c p.1) η i o p.2)
      (c.chart.target ×ˢ ({0}ᶜ : Set E)) := by
  have hEq (p : E × E) : scaledConeRatio (chartInverseMetric B c p.1) η p.2 =
      normalizedFrozenPhase (chartInverseMetric B c p.1) p.2 / η := by
    simp only [scaledConeRatio, normalizedFrozenPhase, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
  simp only [thinConeProfile, hEq]
  exact (descendingProfile_contDiff _ _).comp_contDiffOn
    (((joint_phase_smooth B c c.chart.target (Subset.refl _) hB hn).div_const η).pow 2)

/-- The width and cutoff profile are fixed before the compact chart family
is tested. The constants are uniform in the choice of the frozen center. -/
theorem exists_chartThinScalar_window_Lp (B : Field (M := M)) (c : AtlasChart M) (K : Set E)
    (hK : IsCompact K) (hKU : K ⊆ c.chart.target) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (η i o : ℝ) (hη : 0 < η) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ (f : ComplexL2 E),
      MemLp (f : E → ℂ) (ENNReal.ofReal p) volume →
      let m := chartInverseMetric B c x
      let S := fourierMultiplier (thinConeScalar m hη i o) f
      let S' := fourierMultiplier (thinComplementScalar m hη i o) f
      let P := ENNReal.ofReal p
      let R := C * (eLpNorm (f : E → ℂ) P volume).toReal
      (MemLp (S : E → ℂ) P volume ∧ (eLpNorm (S : E → ℂ) P volume).toReal ≤ R) ∧
      (MemLp (S' : E → ℂ) P volume ∧ (eLpNorm (S' : E → ℂ) P volume).toReal ≤ R) := by
  let T (p : E × E) := thinConeProfile (chartInverseMetric B c p.1) η i o p.2
  have hT : ContDiffOn ℝ ∞ T (c.chart.target ×ˢ ({0}ᶜ : Set E)) := chartThinProfile_jointSmooth B c hB hn η i o
  obtain ⟨J₁, hJ₁, hJets₁⟩ := compactChartFamily_uniform_frequency_jets K c.chart.target hK c.chart.open_target hKU T hT
  obtain ⟨J₂, hJ₂, hJets₂⟩ := compactChartFamily_uniform_frequency_jets K c.chart.target hK c.chart.open_target hKU
    (fun z => 1 - T z) (contDiffOn_const.sub hT)
  obtain ⟨A, hA, hBound⟩ := exists_scalarFourierMultiplier_Lp_bound p hp
  let J := J₁ + J₂
  have hJ : 0 ≤ J := add_nonneg hJ₁ hJ₂
  refine ⟨A * J, mul_nonneg hA hJ, ?_⟩
  intro x hx f hf m S S' P R
  let a := thinConeProfile m η i o
  let a' (ξ : E) := 1 - a ξ
  have ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set E) := thinConeProfile_contDiffOn m hη i o
  have ha' : ContDiffOn ℝ ∞ a' ({0}ᶜ : Set E) := contDiffOn_const.sub ha
  have hDeg (t : ℝ) (ht : 0 < t) (ξ : E) : a (t • ξ) = a ξ := thinConeProfile_degreeZero m η i o t ht.ne' ξ
  have hDeg' (t : ℝ) (ht : 0 < t) (ξ : E) : a' (t • ξ) = a' ξ := congrArg (fun v => 1 - v) (hDeg t ht ξ)
  have hFreq₁ (n : ℕ) (hn : n ≤ 6) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ n a ξ‖ ≤ J := (hJets₁ x hx n hn ξ hξ).trans (le_add_of_nonneg_right hJ₂)
  have hFreq₂ (n : ℕ) (hn : n ≤ 6) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ n a' ξ‖ ≤ J := (hJets₂ x hx n hn ξ hξ).trans (le_add_of_nonneg_left hJ₁)
  exact ⟨hBound a ha hDeg J hJ hFreq₁ (thinConeScalar m hη i o) (thinConeScalar_apply m hη i o) f hf,
    hBound a' ha' hDeg' J hJ hFreq₂ (thinComplementScalar m hη i o) (thinComplementScalar_apply m hη i o) f hf⟩

end Burnett.C02
