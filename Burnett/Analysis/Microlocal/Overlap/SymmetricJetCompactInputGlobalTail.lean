import Burnett.Analysis.Microlocal.Overlap.SymmetricJetGlobalTailOriginal
import Burnett.Geometry.Cotangent.CompactTestPartition

/-! The original compact right tests themselves give the finite separated
tail decomposition. -/
set_option autoImplicit false
set_option maxRecDepth 4650
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 410000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Geometry.CotangentTests (exists_finite_smooth_cutoffs_on_compact)
open scoped ContDiff Manifold Topology BigOperators

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The difference of the two fixed compact right tests is supported away
from the output in finitely many chart windows. Its true global pairing
tends to zero along the full original sequence. -/
theorem tendsto_symmetricJetGlobalForm_originalFull_sub_near_of_compactInput
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (Q : SymmetricJetGlobalForm M) (K : SymmetricJetPairingKernel M)
    (hQ : HasSeparatedSymmetricJetKernel (ManifoldVolume.geometricMeasure B) Q K)
    (c : AtlasChart M) (S V : Set M) (hS : IsCompact S) (hSc : S ⊆ c.chart.source)
    (hV : IsOpen V) (hSV : S ⊆ V)
    (hK : ∀ (d : AtlasChart M) (T : Set M), IsCompact T → T ⊆ d.chart.source → Disjoint S T →
      ∀ i j, ContinuousOn (uncurry (symmetricJetKernelEntry K c d i j)) (S ×ˢ T))
    (α ρ η : M → ℝ) (hα : ContMDiff Model 𝓘(ℝ) ∞ α)
    (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ) (hη : ContMDiff Model 𝓘(ℝ) ∞ η)
    (hαc : HasCompactSupport α) (hρc : HasCompactSupport ρ) (hηc : HasCompactSupport η)
    (hαS : tsupport α ⊆ S) (hNear : EqOn ρ η V) :
    let v := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc
    let u := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc
    let w := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG η hη hηc
    Tendsto (fun n => Q (v n) (u n) - Q (v n) (w n)) atTop (𝓝 0) := by
  intro v u w
  let T := tsupport ρ ∪ tsupport η
  let U (p : M) := (AtlasChart.atPoint p).chart.source \ S
  have hTU : T \ V ⊆ ⋃ p, U p := by
    intro p hp
    exact mem_iUnion.mpr ⟨p, mem_chart_source E p, fun hs => hp.2 (hSV hs)⟩
  obtain ⟨N, label, β, W, _, hTW, hβ, hOne⟩ :=
    exists_finite_smooth_cutoffs_on_compact U
      (fun p => (AtlasChart.atPoint p).chart.open_source.sdiff hS.isClosed)
      ((hρc.union hηc).diff hV) hTU
  let d (i : Fin N) := AtlasChart.atPoint (label i)
  let hSmooth (i : Fin N) := (hβ i).1
  let z (n : ℕ) := u n + (-1 : ℂ) • w n
  have hSplit (n : ℕ) : z n = ∑ i, scaleCompactSymmetricJet (β i) (hSmooth i) (z n) := by
    apply Subtype.ext
    funext p
    simp only [Submodule.coe_sum, Finset.sum_apply, scaleCompactSymmetricJet_apply]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum]
    by_cases hpW : p ∈ W
    · rw [hOne p hpW, Complex.ofReal_one, one_smul]
    have hSame : ρ p = η p := by
      by_cases hpV : p ∈ V
      · exact hNear hpV
      have hOut : p ∉ T := fun hpT => hpW (hTW ⟨hpT, hpV⟩)
      rw [image_eq_zero_of_notMem_tsupport (fun hp => hOut (Or.inl hp)),
        image_eq_zero_of_notMem_tsupport (fun hp => hOut (Or.inr hp))]
    have hValue : (u n).val p = (w n).val p := by
      simp only [u, w, originalCovariantGlobalCutoffTest, globalCutoffSymmetricJetTest_apply, hSame]
    have hZero : (z n).val p = 0 := by
      simp only [z, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hValue]
      calc
        _ = ((1 : ℂ) + -1) • (w n).val p := by rw [add_smul, one_smul]
        _ = 0 := by rw [add_neg_cancel, zero_smul]
    rw [hZero, smul_zero]
  let tail (i : Fin N) (n : ℕ) :=
    Q (v n) (scaleCompactSymmetricJet (β i) (hSmooth i) (z n))
  have hTail (i : Fin N) : Tendsto (tail i) atTop (𝓝 0) := by
    have hC := (hβ i).2.1
    have hD : tsupport (β i) ⊆ (d i).chart.source := fun _ hp => ((hβ i).2.2.1 hp).1
    have hSep : Disjoint S (tsupport (β i)) :=
      Set.disjoint_left.mpr fun _ hp hβp => ((hβ i).2.2.1 hβp).2 hp
    exact tendsto_symmetricJetGlobalForm_scale_originalDifference r B g hB hg hn hsB hsG hconv hb
      Q K hQ c (d i) S (tsupport (β i)) hS hC hSep hSc hD (hK (d i) _ hC hD hSep)
      α (β i) ρ η hα (hSmooth i) hρ hη hαc hC hρc hηc hαS Subset.rfl
  have hSum : Tendsto (fun n => ∑ i, tail i n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hTail i)
  apply hSum.congr
  intro n
  change ∑ i, Q (v n) (scaleCompactSymmetricJet (β i) (hSmooth i) (z n)) = Q (v n) (u n) - Q (v n) (w n)
  rw [← map_sum, ← hSplit n]
  simp only [z, map_add, map_smul, neg_smul, one_smul, sub_eq_add_neg]

end Burnett.Microlocal.Overlap
