import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-! Real order-zero tests in the manuscript's inner-product convention. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis components)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped Manifold Topology ComplexConjugate ComplexOrder ContDiff InnerProduct Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A degree-zero symbol has the same value at the actual unit covector and
its round-frequency representative from the same chart. -/
theorem atlasAngularPhaseCode_symbol_eq_unitCovector {r : Metric (M := M)}
    (c : AtlasChart M) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
    (a : CoordinateSpace → CoordinateSpace → ℂ) (ha : ∀ x, DegreeZero (a x)) :
    a (atlasAngularPhaseCode c p).1 (atlasAngularPhaseCode c p).2.val =
      a (c.chart (projection p)) (WithLp.toLp 2 (atlasChartUnitCovector c p)) := by
  let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
  have hξ : ξ ≠ 0 := by
    intro h
    apply atlasChartUnitCovector_ne_zero c p hp
    exact congrArg (WithLp.ofLp) h
  change a (FixedCotangentChart.fixedChartPhase c p.val).1 (atlasAngularDirection ξ).val = _
  rw [FixedCotangentChart.fixedChartPhase_of_mem c p.val hp, atlasAngularDirection_value hξ]
  exact ha _ _ (inv_pos.mpr (norm_pos_iff.mpr hξ)) ξ

variable [MeasurableSpace M] [BorelSpace M]

/-- Swapping the ordered jet slots conjugates the entry on the same positive
intrinsic covariance, in every compatible chart. -/
theorem ae_atlasOrderedJetEntry_conj_swap {r : Metric (M := M)}
    (A : IntrinsicAmplitudeCovariance r) (c : AtlasChart M)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ
      (TangentSpace Model (projection p)), (components b (A.density p)).PosSemidef)
    {K : Set M} (hK : MeasurableSet K) (hKc : K ⊆ c.chart.source) (i j : JetSlot) :
    (fun p => conj (atlasOrderedJetEntry c A.density p i j)) =ᵐ[A.control.restrict (amplitudeCosphereWindow r K)]
      (fun p => atlasOrderedJetEntry c A.density p j i) := by
  have hWin := measurableSet_amplitudeCosphereWindow r hK
  filter_upwards [ae_restrict_of_ae hPos, ae_restrict_mem (μ := A.control) hWin] with p hp hloc
  have hpc : projection p ∈ c.chart.source := hKc hloc
  have hPsd : (atlasAmplitudeMatrix c A.density p).PosSemidef := by
    rw [atlasAmplitudeMatrix_of_mem c A.density p hpc]
    exact hp (chartTangentBasis c (projection p) hpc)
  have hHerm := hPsd.isHermitian.apply i.2 j.2
  change conj (atlasAmplitudeMatrix c A.density p j.2 i.2) = _ at hHerm
  simp only [atlasOrderedJetEntry, map_mul, Complex.conj_ofReal, hHerm]
  ring

/-- The first-linear paper pairing conjugates the scalar test and swaps the
ordered jet entry. A real scalar test keeps the same weight. -/
theorem tendsto_receivingPaperPairing_of_weight {r : Metric (M := M)}
    (A : IntrinsicAmplitudeCovariance r) (c : AtlasChart M)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ
      (TangentSpace Model (projection p)), (components b (A.density p)).PosSemidef)
    {K : Set M} (hK : MeasurableSet K) (hKc : K ⊆ c.chart.source)
    (w : Cosphere r → ℂ) (i j : JetSlot)
    (u v : ℕ → ComplexL2 CoordinateSpace) (T : ComplexL2 CoordinateSpace →L[ℂ] ComplexL2 CoordinateSpace) :
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let F (p : Cosphere r) := w p * atlasOrderedJetEntry c A.density p i j
    let G (p : Cosphere r) := conj (w p) * atlasOrderedJetEntry c A.density p j i
    Integrable F τ →
    Tendsto (fun n => inner ℂ (u n) (T (v n))) atTop (𝓝 (∫ p, F p ∂τ)) →
    Integrable G τ ∧ conj (∫ p, F p ∂τ) = ∫ p, G p ∂τ ∧
      Tendsto (fun n => inner ℂ (T (v n)) (u n)) atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro τ F G hF hLim
  have hSwap := ae_atlasOrderedJetEntry_conj_swap A c hPos hK hKc i j
  have hConj : (fun p => conj (F p)) =ᵐ[τ] G := by
    filter_upwards [hSwap] with p hp
    simp only [F, G, map_mul, hp]
  have hEq : conj (∫ p, F p ∂τ) = ∫ p, G p ∂τ :=
    integral_conj.symm.trans (integral_congr_ae hConj)
  have hIG : Integrable (fun p => conj (F p)) τ :=
    hF.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hF.aestronglyMeasurable)
      (Eventually.of_forall fun _ => (Complex.norm_conj _).le)
  refine ⟨hIG.congr hConj, hEq, ?_⟩
  have h := (Complex.continuous_conj.tendsto _).comp hLim
  rw [hEq] at h
  exact h.congr (fun _ => inner_conj_symm _ _)

end Burnett.Microlocal.Overlap
