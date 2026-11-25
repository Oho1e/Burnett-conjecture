import Burnett.Analysis.Microlocal.Overlap.WindowedClassicalChartLimit
import Burnett.Analysis.Microlocal.Overlap.FiniteRestrictedDensitySum
import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalCovariantPartition

/-! A global principal pairing from independent compact chart realizations. -/
set_option autoImplicit false
set_option maxRecDepth 4750
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 390000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.CotangentTests (exists_finite_smooth_cutoffs_on_compact)
open Burnett.F07.IntrinsicAmplitudeCoordinates (components)
open Burnett.RicciSymbol (Index)
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- The compact-window data for one actual global form determine the global
limit for arbitrary compact left and right scalar tests. Every cutoff and
each finite chart partition disappears into the original tested weights. -/
theorem tendsto_originalCovariantGlobalCutoffTest_windowedClassical
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) (A : IntrinsicAmplitudeCovariance r)
    (hLocal : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (components b (A.density p)).PosSemidef)
    (Q : SymmetricJetGlobalForm M) (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (α ρ : M → ℝ) (hα : ContMDiff Model 𝓘(ℝ) ∞ α) (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ)
    (hαc : HasCompactSupport α) (hρc : HasCompactSupport ρ) :
    let G (p : Cosphere r) := ((α (projection p) * ρ (projection p) : ℝ) : ℂ) *
      windowedClassicalFormDensity P A p
    Integrable G A.control ∧
    Tendsto (fun n => conj (Q (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc (σ n))
        (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc (σ n))))
      atTop (𝓝 (∫ p, G p ∂A.control)) := by
  intro G
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    let c (x : M) := AtlasChart.atPoint x
    obtain ⟨N, label, β, V, _, hV, hβ, hOne⟩ :=
      exists_finite_smooth_cutoffs_on_compact (fun x => (c x).chart.source)
        (fun x => (c x).chart.open_source) hαc (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
    let f (k : Fin N) := β k * α
    have hf (k : Fin N) : ContMDiff Model 𝓘(ℝ) ∞ (f k) := (hβ k).1.mul hα
    have hfc (k : Fin N) : HasCompactSupport (f k) := (hβ k).2.1.mul_right
    let S (k : Fin N) := tsupport (f k)
    have hSc (k : Fin N) : S k ⊆ (c (label k)).chart.source :=
      tsupport_mul_subset_left.trans (hβ k).2.2.1
    have hSum (x : M) : ∑ k, f k x = α x := by
      change (∑ k, β k x * α x) = _
      by_cases hx : x ∈ V
      · rw [← Finset.sum_mul, hOne x hx, one_mul]
      · have hz : α x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hV hs))
        simp [hz]
    let W (k : Fin N) := amplitudeCosphereWindow r (S k)
    let w (k : Fin N) (p : Cosphere r) := ((f k (projection p) * ρ (projection p) : ℝ) : ℂ)
    let D := windowedClassicalFormDensity P A
    have hW (k : Fin N) : MeasurableSet (W k) := measurableSet_amplitudeCosphereWindow r (hfc k).isClosed.measurableSet
    have hSupport (k : Fin N) (p : Cosphere r) (hp : p ∉ W k) : w k p = 0 := by
      have hz : f k (projection p) = 0 := image_eq_zero_of_notMem_tsupport (show projection p ∉ S k from hp)
      simp only [w, hz, zero_mul, Complex.ofReal_zero]
    have localLimit (k : Fin N) := tendsto_originalCovariantGlobalCutoffTest_windowedClassicalChart
      r B g hB hg hn hsB hsG hconv hb σ hσ A hLocal hPos Q P
      (c (label k)) (S k) (hfc k) (hSc k) (f k) ρ (hf k) hρ (hfc k) hρc subset_rfl
    obtain ⟨hInt, hIntegral⟩ := integrable_finiteRestrictedDensitySum A.control W hW w D hSupport
      (fun k => (localLimit k).1)
    have hWeight : (fun p => (∑ k, w k p) * D p) = G := by
      funext p
      change ((∑ k, ((f k (projection p) * ρ (projection p) : ℝ) : ℂ)) * D p) = G p
      rw [← Complex.ofReal_sum, ← Finset.sum_mul, hSum (projection p)]
    rw [hWeight] at hInt hIntegral
    refine ⟨hInt, ?_⟩
    rw [hIntegral]
    have hLimit := tendsto_finset_sum Finset.univ (fun k _ => (localLimit k).2)
    refine hLimit.congr fun n => ?_
    rw [originalCovariantGlobalCutoffTest_eq_finiteSum r B g hB hg hsB hsG α hα hαc f hf hfc hSum (σ n)]
    simp only [map_sum, LinearMap.sum_apply]
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    letI : IsEmpty (Cosphere r) := ⟨fun p => isEmptyElim (projection p)⟩
    have hZero (s : smoothCompactSymmetricJet M) : s = 0 := Subtype.ext (funext isEmptyElim)
    rw [A.control.eq_zero_of_isEmpty, integral_zero_measure]
    refine ⟨integrable_zero_measure (f := G), ?_⟩
    simpa only [hZero (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc _),
      map_zero, LinearMap.zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

end Burnett.Microlocal.Overlap
