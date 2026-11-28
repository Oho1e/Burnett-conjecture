import Burnett.Analysis.TransportClosure.RealChartFourierReflection
import Burnett.Analysis.Microlocal.Overlap.SeparableSetIntegralExt

/-! Reflection is a conjugating symmetry of the original chart covariance entries. -/
set_option autoImplicit false
set_option maxRecDepth 4100
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Metric Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension (finiteSmoothRestriction finiteSmoothRestriction_apply)
open Burnett.Microlocal.MatrixMeasureAssembly (entryMeasure traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.Microlocal.SeparablePositive (separableOperator finiteSeparableOperator conjugateSymbol conjugateSymbol_apply)
open Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.SmoothBaseTests
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

def compactChartAntipodal (K : BallData) (z : Chart K) : Chart K :=
  (z.1, ⟨-(z.2 : E), by simpa only [mem_sphere, dist_zero_right, norm_neg] using z.2.property⟩)

theorem continuous_compactChartAntipodal (K : BallData) : Continuous (compactChartAntipodal K) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

theorem compactChartAntipodal_involutive (K : BallData) : Involutive (compactChartAntipodal K) := by
  intro z
  refine Prod.ext ?_ ?_
  · rfl
  · apply Subtype.ext
    exact neg_neg (z.2 : E)

private theorem conjugateReflectedAngularSymbol_smooth (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ContDiffOn ℝ ∞ (conjugateReflectedAngularSymbol m : E → ℂ) ({0}ᶜ : Set E) :=
  Complex.conjCLE.contDiff.comp_contDiffOn <|
    hm.comp contDiff_id.neg.contDiffOn (fun ξ hξ => by simpa only [mem_compl_iff, mem_singleton_iff, neg_eq_zero] using hξ)

private theorem conjugateReflectedAngularSymbol_degreeZero (m : BoundedSymbol E) (hm : DegreeZero (m : E → ℂ)) :
    DegreeZero (conjugateReflectedAngularSymbol m : E → ℂ) := by
  intro s hs ξ
  change conj (m (-(s • ξ))) = conj (m (-ξ))
  rw [← smul_neg, hm s hs (-ξ)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private theorem originalVolume_chartReflected_densityTerm
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (q : CompactChartInput M) (σ : ℕ → ℕ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (a m : BoundedSymbol E) (ha : Continuous (a : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ)) (i j : JetSlot) :
    let D (z : Chart q.ball) := density ν hf z i j
    (∫ z, (a z.1 * m (-(z.2 : E))) * conj (D z) ∂traceMeasure ν) =
      ∫ z, (a z.1 * m z.2) * D z ∂traceMeasure ν := by
  intro D
  let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
  let a' := conjugateSymbol a
  let m' := conjugateReflectedAngularSymbol m
  have ha' : Continuous (a' : E → ℂ) := Complex.continuous_conj.comp ha
  have hm' := conjugateReflectedAngularSymbol_smooth m hm
  have hd' := conjugateReflectedAngularSymbol_degreeZero m hd
  obtain ⟨_, _, _, _, _, _, hLimit⟩ := hRep
  have hT (c d : BoundedSymbol E) (hc : Continuous (c : E → ℂ))
      (hD : ContDiffOn ℝ ∞ (d : E → ℂ) ({0}ᶜ : Set E)) (hd' : DegreeZero (d : E → ℂ)) :
      Tendsto (fun n => inner ℂ (w (σ n) i) (separableOperator c d (w (σ n) j)))
        atTop (𝓝 (∫ z : Chart q.ball, (c z.1 * d z.2) * D z ∂traceMeasure ν)) := by
    have hRestr (z : Chart q.ball) : finiteSmoothRestriction q.ball (fun _ : Unit => c) (fun _ => d)
        (fun _ => hc) (fun _ => hD) z = c z.1 * d z.2 := by
      rcases z with ⟨y, ξ⟩
      rw [finiteSmoothRestriction_apply, Fintype.sum_unique]
    simpa only [w, D, hRestr, finiteSeparableOperator, Fintype.sum_unique] using
      hLimit Unit (fun _ => c) (fun _ => d) (fun _ => hc) (fun _ => hD) (fun _ => hd') i j
  have hC := (Complex.continuous_conj.tendsto _).comp (hT a' m' ha' hm' hd')
  have hC' : Tendsto (fun n => inner ℂ (w (σ n) i) (separableOperator a m (w (σ n) j)))
      atTop (𝓝 (conj (∫ z : Chart q.ball, (a' z.1 * m' z.2) * D z ∂traceMeasure ν))) := by
    apply hC.congr
    intro n
    change conj (inner ℂ (w (σ n) i) (separableOperator a' m' (w (σ n) j))) = _
    rw [← conj_originalVolume_separablePairing_eq_reflected B g hB hg hn q a m (σ n) i j]
    exact starRingEnd_self_apply (inner ℂ (w (σ n) i) (separableOperator a m (w (σ n) j)))
  rw [← integral_conj] at hC'
  simpa only [a', m', conjugateSymbol_apply, conjugateReflectedAngularSymbol, map_mul,
    starRingEnd_self_apply] using tendsto_nhds_unique hC' (hT a m ha hm hd)

/-- Reflection of the angular variable conjugates the very same Borel
entries of the original gradient covariance, along its fixed subsequence. -/
theorem originalVolume_chartEntryMeasure_antipodal
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (q : CompactChartInput M) (σ : ℕ → ℕ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (S : Set (Chart q.ball)) (hS : MeasurableSet S) (i j : JetSlot) :
    conj (entryMeasure ν hf i j (compactChartAntipodal q.ball ⁻¹' S)) = entryMeasure ν hf i j S := by
  let D (z : Chart q.ball) := density ν hf z i j
  have hI : Integrable D (traceMeasure ν) := integrable_density_entry ν hf i j
  have hIC : Integrable (fun z => conj (D z)) (traceMeasure ν) :=
    hI.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hI.aestronglyMeasurable)
      (Eventually.of_forall fun z => by rw [Complex.norm_conj])
  have hMeas := (continuous_compactChartAntipodal q.ball).measurable
  have ht (t : TermParameters) := originalVolume_chartReflected_densityTerm B g hB hg hn q σ ν hf hRep
    (baseSymbol q.ball t.1) (complexRationalAngularSymbol t.2) (complexBase_contDiff q.ball t.1).continuous
    (complexRationalAngular_contDiffOn t.2) (complexRationalAngular_degreeZero t.2) i j
  have hEq := setIntegral_preimage_eq_of_weightedChartTerms q.ball (traceMeasure ν) (traceMeasure ν)
    (compactChartAntipodal q.ball) hMeas (fun z => conj (D z)) D hIC hI ht S hS
  rw [integral_conj, hRep.2.2.2.2.1 _ (hMeas hS) i j, hRep.2.2.2.2.1 S hS i j] at hEq
  exact hEq

end Burnett.Microlocal.Overlap
