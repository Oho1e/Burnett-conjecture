import Burnett.Analysis.Microlocal.Overlap.GlobalAmplitudeEntryMeasure

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open MaximalChart (AtlasChart)
open ChartVolume (derivativeMatrix)
open MetricJetNaturality (derivativeMatrix_apply)
open UnitCosphere (Cosphere projection continuous_projection)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovectors (tensorPairTransition)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeCovarianceDensity chartComponents chartComponents_change fixedCotangentTransitionMatrix)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open scoped ComplexConjugate ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

theorem continuousOn_fixedCotangentTransitionMatrix_entry (c d : AtlasChart M) (i j : Index) :
    ContinuousOn (fun x => fixedCotangentTransitionMatrix c d x i j)
      (c.chart.source ∩ d.chart.source) := by
  let e := d.transition c
  have hD : ContinuousOn (fderiv ℝ e) e.source :=
    (d.smooth_transition c).continuousOn_fderiv_of_isOpen e.open_source (by simp)
  have hMap : MapsTo d.chart (c.chart.source ∩ d.chart.source) e.source := by
    intro x hx
    refine ⟨d.chart.mapsTo hx.2, ?_⟩
    change d.chart.symm (d.chart x) ∈ c.chart.source
    rw [d.chart.left_inv hx.2]
    exact hx.1
  have hEntry : ContinuousOn (fun y => derivativeMatrix (fderiv ℝ e y) j i) e.source := by
    simp only [derivativeMatrix_apply]
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn
      (hD.clm_apply continuousOn_const)
  exact hEntry.comp (d.chart.continuousOn.mono inter_subset_right) hMap

/-- The transition of an ordered tensor pair expressed in the destination chart. -/
abbrev atlasAmplitudeTransition (c d : AtlasChart M) (x : M) : Matrix Pair Pair ℂ :=
  tensorPairTransition (fixedCotangentTransitionMatrix c d x)

theorem continuousOn_atlasAmplitudeTransition_entry (c d : AtlasChart M) (i j : Pair) :
    ContinuousOn (fun x => atlasAmplitudeTransition c d x i j)
      (c.chart.source ∩ d.chart.source) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_fixedCotangentTransitionMatrix_entry c d i.1 j.1)).mul
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_fixedCotangentTransitionMatrix_entry c d i.2 j.2))

variable [IsManifold Model ∞ M]

/-- Ordered complex components of the same actual tensor in an arbitrary
compatible chart. The extension is evaluated only on that chart's source. -/
def atlasAmplitudeMatrix {r : Metric (M := M)} (c : AtlasChart M) (J : AmplitudeCovarianceDensity r)
    (p : Cosphere r) : Matrix Pair Pair ℂ := by
  classical
  exact if hx : projection p ∈ c.chart.source then chartComponents c (projection p) hx (J p)
    else 0

theorem atlasAmplitudeMatrix_of_mem {r : Metric (M := M)} (c : AtlasChart M)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    atlasAmplitudeMatrix c J p = chartComponents c (projection p) hp (J p) := by
  rw [atlasAmplitudeMatrix, dif_pos hp]

theorem atlasAmplitudeMatrix_preferred {r : Metric (M := M)} (c : M)
    (J : AmplitudeCovarianceDensity r) : atlasAmplitudeMatrix (.atPoint c) J = intrinsicAmplitudeMatrix c J := rfl

/-- The full congruence at a point, with all four ordered slots retained. -/
theorem atlasAmplitudeMatrix_change {r : Metric (M := M)} (c d : AtlasChart M)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) :
    let T := atlasAmplitudeTransition c d (projection p)
    atlasAmplitudeMatrix d J p = T * atlasAmplitudeMatrix c J p * Tᴴ := by
  intro T
  rw [atlasAmplitudeMatrix_of_mem d J p hd, atlasAmplitudeMatrix_of_mem c J p hc]
  exact chartComponents_change c d (projection p) hc hd (J p)

/-- Each entry of the congruence is a finite sum of the source entries
multiplied by actual cotangent transition coefficients. -/
theorem atlasAmplitudeMatrix_entry_change {r : Metric (M := M)} (c d : AtlasChart M)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) (i j : Pair) :
    let T := atlasAmplitudeTransition c d (projection p)
    atlasAmplitudeMatrix d J p i j =
      ∑ k : Pair, ∑ l : Pair, (T i l * conj (T j k)) * atlasAmplitudeMatrix c J p l k := by
  intro T
  rw [atlasAmplitudeMatrix_change c d J p hc hd]
  change (T * atlasAmplitudeMatrix c J p * Tᴴ) i j = _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

theorem integrable_atlasAmplitudeMatrix_change_terms_on_compact
    (r : Metric (M := M)) (c d : AtlasChart M) (J : AmplitudeCovarianceDensity r)
    (μ : Measure (Cosphere r)) {K : Set M} (hK : IsCompact K)
    (hSub : K ⊆ c.chart.source ∩ d.chart.source)
    (hSrc : ∀ i j, Integrable (fun p => atlasAmplitudeMatrix c J p i j)
      (μ.restrict (amplitudeCosphereWindow r K))) (i j k l : Pair) :
    let T (p : Cosphere r) := atlasAmplitudeTransition c d (projection p)
    Integrable (fun p => (T p i l * conj (T p j k)) * atlasAmplitudeMatrix c J p l k)
      (μ.restrict (amplitudeCosphereWindow r K)) := by
  intro T
  let W := amplitudeCosphereWindow r K
  let C (x : M) := atlasAmplitudeTransition c d x i l * conj (atlasAmplitudeTransition c d x j k)
  have hC : ContinuousOn C K := ((continuousOn_atlasAmplitudeTransition_entry c d i l).mul
    (Complex.continuous_conj.comp_continuousOn (continuousOn_atlasAmplitudeTransition_entry c d j k))).mono hSub
  have hProj : ContinuousOn (fun p : Cosphere r => C (projection p)) W :=
    hC.comp (continuous_projection r).continuousOn (fun _ hp => hp)
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  obtain ⟨b, hBound⟩ := (hK.image_of_continuousOn hC).isBounded.exists_norm_le
  apply (hSrc l k).bdd_mul' (hProj.aemeasurable hW).aestronglyMeasurable
  exact (ae_restrict_mem (μ := μ) hW).mono fun p hp => hBound _ (mem_image_of_mem C hp)

/-- A compact overlap permits the transition to be integrated entry by entry. -/
theorem integrable_atlasAmplitudeMatrix_change_on_compact
    (r : Metric (M := M)) (c d : AtlasChart M) (J : AmplitudeCovarianceDensity r)
    (μ : Measure (Cosphere r)) {K : Set M} (hK : IsCompact K)
    (hSub : K ⊆ c.chart.source ∩ d.chart.source)
    (hSrc : ∀ i j, Integrable (fun p => atlasAmplitudeMatrix c J p i j)
      (μ.restrict (amplitudeCosphereWindow r K))) (i j : Pair) :
    Integrable (fun p => atlasAmplitudeMatrix d J p i j) (μ.restrict (amplitudeCosphereWindow r K)) := by
  let T (p : Cosphere r) := atlasAmplitudeTransition c d (projection p)
  have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hSum : Integrable (fun p => ∑ k : Pair, ∑ l : Pair,
      (T p i l * conj (T p j k)) * atlasAmplitudeMatrix c J p l k)
      (μ.restrict (amplitudeCosphereWindow r K)) :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      integrable_atlasAmplitudeMatrix_change_terms_on_compact r c d J μ hK hSub hSrc i j k l
  apply hSum.congr
  filter_upwards [ae_restrict_mem (μ := μ) hW] with p hp
  exact (atlasAmplitudeMatrix_entry_change c d J p (hSub hp).1 (hSub hp).2 i j).symm

variable [SecondCountableTopology M]

/-- Every ordered component of the global original amplitude is integrable on
a compact base window in any compatible smooth chart. The finite subcover uses
the existing original witnesses on the specified subsequence. -/
theorem original_globalAmplitude_integrable_atlasChart_on_compact
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source) (i j : Pair) :
    Integrable (fun p => atlasAmplitudeMatrix c A.density p i j)
      (A.control.restrict (amplitudeCosphereWindow r K)) := by
  let V (n : ℕ) := (q n).cutoffLocusAbove (1 / 2)
  let L (n : ℕ) := (q n).compactCutoffLocus (1 / 2)
  let U (n : ℕ) := amplitudeCosphereWindow r (K ∩ L n)
  let f (p : Cosphere r) := atlasAmplitudeMatrix c A.density p i j
  have hV (n : ℕ) : IsOpen (V n) := (q n).isOpen_cutoffLocusAbove _
  have hVL (n : ℕ) : V n ⊆ L n := (q n).cutoffLocusAbove_subset_compactCutoffLocus (by norm_num)
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hV (fun x _ => cover.symm ▸ mem_univ x)
  have hKCover : amplitudeCosphereWindow r K ⊆ ⋃ n ∈ I, U n := by
    intro p hp
    obtain ⟨n, hn, hnV⟩ := mem_iUnion₂.mp (hI hp)
    exact mem_iUnion₂.mpr ⟨n, hn, hp, hVL n hnV⟩
  have hPiece (n : ℕ) : IntegrableOn f (U n) A.control := by
    let d : AtlasChart M := .atPoint (q n).center
    have hL : IsCompact (L n) := (q n).isCompact_compactCutoffLocus _
    have hS : IsCompact (K ∩ L n) := hK.inter_right hL.isClosed
    have hQ : K ∩ L n ⊆ (q n).nonzeroLocus := inter_subset_right.trans
      ((q n).compactCutoffLocus_subset_nonzeroLocus (by norm_num))
    have hOverlap : K ∩ L n ⊆ d.chart.source ∩ c.chart.source :=
      fun _ hx => ⟨(hQ hx).1, hSub hx.1⟩
    apply integrable_atlasAmplitudeMatrix_change_on_compact r d c A.density A.control hS hOverlap _ i j
    intro a b
    have hFrom := (original_globalAmplitude_entryMeasure_on_compactChart r B g hB hg hsB hsG hnB hnG
      hconv hb hv σ hσ A hA (q n) (ν n) (hf n) (hRep n) hS hQ a b).1
    exact hFrom
  have hFin : IntegrableOn f (⋃ n ∈ I, U n) A.control :=
    integrableOn_finset_iUnion.mpr (fun n _ => hPiece n)
  exact hFin.mono_set hKCover

end Burnett.Microlocal.Overlap
