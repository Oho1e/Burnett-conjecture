import Burnett.Analysis.Microlocal.Overlap.AtlasJetOperatorNaturality

/-! Compatibility of the actual jet endomorphism measures on compact overlaps. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity fixedCotangentTransitionMatrix)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Kronecker Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

theorem continuousOn_atlasJetTransition_entry (c d : AtlasChart M) (i j : JetSlot) :
    ContinuousOn (fun x => atlasJetTransition c d x i j) (c.chart.source ∩ d.chart.source) := by
  let T := fixedCotangentTransitionMatrix c d
  have h (a b : Index) : ContinuousOn (fun x => (T x a b : ℂ)) (c.chart.source ∩ d.chart.source) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_fixedCotangentTransitionMatrix_entry c d a b)
  change ContinuousOn (fun x => (T x i.1 j.1 : ℂ) * ((T x i.2.1 j.2.1 : ℂ) * (T x i.2.2 j.2.2 : ℂ))) _
  exact (h i.1 j.1).mul ((h i.2.1 j.2.1).mul (h i.2.2 j.2.2))

/-- The coefficient multiplying a source endomorphism entry in the receiving chart. -/
def atlasJetOperatorTransitionWeight (c d : AtlasChart M) (x : M) (i j k l : JetSlot) : ℂ :=
  atlasJetTransition c d x i k * atlasJetTransition d c x l j

variable [IsManifold Model ∞ M]

theorem atlasJetCovarianceOperator_entry_change {r : Metric (M := M)} (c d : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) (i j : JetSlot) :
    atlasJetCovarianceOperator d A p i j = ∑ l : JetSlot, ∑ k : JetSlot,
      atlasJetOperatorTransitionWeight c d (projection p) i j k l * atlasJetCovarianceOperator c A p k l := by
  rw [atlasJetCovarianceOperator_change c d A p hc hd]
  simp only [Matrix.mul_apply, Finset.sum_mul, atlasJetOperatorTransitionWeight]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ac_rfl

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

theorem integrable_atlasJetOperatorTransitionTerm_on_compact {r : Metric (M := M)}
    (c d : AtlasChart M) (A : AmplitudeCovarianceDensity r) (μ : Measure (Cosphere r))
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source ∩ d.chart.source)
    (hSrc : ∀ k l : JetSlot, IntegrableOn (fun p => atlasJetCovarianceOperator c A p k l)
      (amplitudeCosphereWindow r K) μ) (i j k l : JetSlot) :
    IntegrableOn (fun p => atlasJetOperatorTransitionWeight c d (projection p) i j k l *
      atlasJetCovarianceOperator c A p k l) (amplitudeCosphereWindow r K) μ := by
  let W := amplitudeCosphereWindow r K
  let H (x : M) := atlasJetOperatorTransitionWeight c d x i j k l
  have hH : ContinuousOn H K := ((continuousOn_atlasJetTransition_entry c d i k).mono hSub).mul
    ((continuousOn_atlasJetTransition_entry d c l j).mono (fun _ hx => ⟨(hSub hx).2, (hSub hx).1⟩))
  have hP : ContinuousOn (fun p => H (projection p)) W :=
    hH.comp (continuous_projection r).continuousOn (fun _ hp => hp)
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hH).isBounded.exists_norm_le
  exact (hSrc k l).bdd_mul' (hP.aemeasurable hW).aestronglyMeasurable
    ((ae_restrict_mem (μ := μ) hW).mono fun p hp => hC _ (mem_image_of_mem H hp))

/-- On each Borel subset of a compact overlap, the receiving endomorphism
integral uses the source density with the actual transition in both directions. -/
theorem integral_atlasJetCovarianceOperator_change_on_compact {r : Metric (M := M)}
    (c d : AtlasChart M) (A : AmplitudeCovarianceDensity r) (μ : Measure (Cosphere r))
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source ∩ d.chart.source)
    (hSrc : ∀ k l : JetSlot, IntegrableOn (fun p => atlasJetCovarianceOperator c A p k l)
      (amplitudeCosphereWindow r K) μ) (U : Set (Cosphere r)) (i j : JetSlot) :
    let ρ := μ.restrict (amplitudeCosphereWindow r K)
    (∫ p in U, atlasJetCovarianceOperator d A p i j ∂ρ) =
      ∑ l : JetSlot, ∑ k : JetSlot, ∫ p in U,
        atlasJetOperatorTransitionWeight c d (projection p) i j k l * atlasJetCovarianceOperator c A p k l ∂ρ := by
  intro ρ
  let f (l k : JetSlot) (p : Cosphere r) :=
    atlasJetOperatorTransitionWeight c d (projection p) i j k l * atlasJetCovarianceOperator c A p k l
  have hTerms (l k : JetSlot) : Integrable (f l k) (ρ.restrict U) :=
    (integrable_atlasJetOperatorTransitionTerm_on_compact c d A μ hK hSub hSrc i j k l).integrableOn
  have hOuter (l : JetSlot) : Integrable (fun p => ∑ k : JetSlot, f l k p) (ρ.restrict U) :=
    integrable_finset_sum _ (fun k _ => hTerms l k)
  calc
    _ = ∫ p in U, (∑ l : JetSlot, ∑ k : JetSlot, f l k p) ∂ρ := by
      apply integral_congr_ae
      have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
      filter_upwards [ae_restrict_of_ae (s := U) (ae_restrict_mem (μ := μ) hW)] with p hp
      exact atlasJetCovarianceOperator_entry_change c d A p (hSub hp).1 (hSub hp).2 i j
    _ = ∑ l : JetSlot, ∫ p in U, (∑ k : JetSlot, f l k p) ∂ρ :=
      integral_finset_sum _ (fun l _ => hOuter l)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      exact integral_finset_sum _ (fun k _ => hTerms l k)

variable [SecondCountableTopology M]

/-- Both compact-overlap matrix measures use the same original global
control, with the endomorphism similarity law on every Borel set. -/
theorem original_atlasJetCovarianceOperator_matrixMeasure_overlap
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c d : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source ∩ d.chart.source) :
    let ρ := A.control.restrict (amplitudeCosphereWindow r K)
    ∃ νc νd : VectorMeasure (Cosphere r) (JetSlot → JetSlot → ℂ),
      ∀ U : Set (Cosphere r), MeasurableSet U → ∀ i j : JetSlot,
        νc U i j = (∫ p in U, atlasJetCovarianceOperator c A.density p i j ∂ρ) ∧
        νd U i j = (∫ p in U, atlasJetCovarianceOperator d A.density p i j ∂ρ) ∧
        νd U i j = ∑ l : JetSlot, ∑ k : JetSlot, ∫ p in U,
          atlasJetOperatorTransitionWeight c d (projection p) i j k l *
            atlasJetCovarianceOperator c A.density p k l ∂ρ := by
  intro ρ
  have hc : K ⊆ c.chart.source := hSub.trans inter_subset_left
  have hd : K ⊆ d.chart.source := hSub.trans inter_subset_right
  obtain ⟨νc, hνc⟩ := original_atlasJetCovarianceOperator_matrixMeasure_on_compact r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA c hK hc
  obtain ⟨νd, hνd⟩ := original_atlasJetCovarianceOperator_matrixMeasure_on_compact r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA d hK hd
  have hCov := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).2 c hK hc
  have hSrc := integrable_atlasJetCovarianceOperator_on_compact c A.density A.control hK hc hCov
  refine ⟨νc, νd, fun U hU i j => ⟨hνc U hU i j, hνd U hU i j, ?_⟩⟩
  exact (hνd U hU i j).trans
    (integral_atlasJetCovarianceOperator_change_on_compact c d A.density A.control hK hSub hSrc U i j)

end Burnett.Microlocal.Overlap
