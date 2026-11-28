import Burnett.Analysis.TransportClosure.HamiltonAntipodalParity

/-! Joint regularity of the actual local Hamiltonian and of a genuine punctured
cotangent test used in the C04 equations. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.C04

open Bundle Set
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open UnitNullAngular (Phase chartPunctured chartInverse chartInverse_smooth
  dualPair_self contDiffOn_dualPair)
open CotangentAngularExtension
open scoped ContDiff Manifold Topology

open private frameBasis frameBasis_apply from Burnett.Geometry.Cotangent.Core

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

omit [IsManifold Model ∞ M] in
theorem isOpen_chartPunctured (c : M) : IsOpen (chartPunctured c) := by
  exact ((chartAt CoordinateSpace c).open_target.preimage continuous_fst).inter
    (isOpen_compl_singleton.preimage continuous_snd)

theorem cotangentCoords_ne_zero_of_punctured (c : M) (p : CotangentBundle M)
    (hc : p.proj ∈ (chartAt CoordinateSpace c).source) (hp : p ∈ puncturedCotangent) :
    cotangentCoords c p ≠ 0 := by
  intro hz
  apply hp
  have hLinear : p.2.toLinearMap = 0 := by
    apply (frameBasis c p.proj hc).ext
    intro i
    have hi := congrFun hz i
    simpa only [cotangentCoords, cotangentTrivialization_apply, frameBasis_apply,
      LinearMap.zero_apply, Pi.zero_apply] using hi
  exact ContinuousLinearMap.ext fun v => DFunLike.congr_fun hLinear v

theorem cotangentChart_mem_chartPunctured (c : M) (p : CotangentBundle M)
    (hc : p.proj ∈ (chartAt CoordinateSpace c).source) (hp : p ∈ puncturedCotangent) :
    cotangentChart c p ∈ chartPunctured c :=
  ⟨(chartAt CoordinateSpace c).mapsTo hc, cotangentCoords_ne_zero_of_punctured c p hc hp⟩

theorem cotangentChartInverse_mapsTo_punctured (c : M) :
    MapsTo (cotangentChartInverse c) (chartPunctured c) puncturedCotangent := by
  intro z hz hn
  have he := congrArg Prod.snd (cotangentChart_right_inv c ⟨hz.1, trivial⟩)
  change cotangentCoords c (cotangentChartInverse c z) = z.2 at he
  have hzero : cotangentCoords c (cotangentChartInverse c z) = 0 := by
    funext i
    simp [cotangentCoords, cotangentTrivialization_apply,
      show (cotangentChartInverse c z).2 = 0 from hn]
  exact hz.2 (he.symm.trans hzero)

/-- The actual scalar test has ordinary joint smoothness on the chart of the
punctured bundle. -/
theorem contDiffOn_cotangentChartTest_joint (c : M) (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent) :
    ContDiffOn ℝ ∞ (a ∘ cotangentChartInverse c) (chartPunctured c) := by
  have h := ha.comp
    ((contMDiffOn_cotangentChartInverse c).mono
      (fun (_ : Phase) (hz : _ ∈ chartPunctured c) => ⟨hz.1, trivial⟩))
    (cotangentChartInverse_mapsTo_punctured c)
  unfold CoordinatePhaseModel at h
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffOn

theorem chartHamiltonian_eq_inverseMetric (c : M)
    (B : Field (M := M)) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (z : Phase) (hz : z ∈ phaseTarget c) :
    chartHamiltonian c B hn z.1 z.2 = symbolNorm (chartInverse B c z.1) z.2 / 2 := by
  let p := cotangentChartInverse c z
  have hp : p.proj ∈ (chartAt CoordinateSpace c).source := cotangentChartInverse_mapsTo c hz
  have he : cotangentChart c p = z := cotangentChart_right_inv c hz
  have hx : chartAt CoordinateSpace c p.proj = z.1 := congrArg Prod.fst he
  have hξ : cotangentCoords c p = z.2 := congrArg Prod.snd he
  have h := dualEnergy_chart B hn hs c p hp
  rw [hx, hξ] at h
  exact congrArg (fun t : ℝ => t / 2) h

/-- The actual dual Hamiltonian equals the paper's half inverse-metric quadratic
form on the genuine phase target. -/
theorem contDiffOn_chartHamiltonian_joint (c : M) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B) :
    ContDiffOn ℝ ∞ (fun z : Phase => chartHamiltonian c B hn z.1 z.2) (phaseTarget c) := by
  have h : ContDiffOn ℝ ∞ (fun z : Phase => symbolNorm (chartInverse B c z.1) z.2 / 2)
      (phaseTarget c) := by
    simp only [← dualPair_self]
    exact (contDiffOn_dualPair _ (chartInverse_smooth B hB hn c)
      (fun (_ : Phase) (hz : _ ∈ phaseTarget c) => hz.1) contDiffOn_snd contDiffOn_snd).div_const 2
  exact h.congr fun z hz => chartHamiltonian_eq_inverseMetric c B hn hs z hz

end Burnett.C04
