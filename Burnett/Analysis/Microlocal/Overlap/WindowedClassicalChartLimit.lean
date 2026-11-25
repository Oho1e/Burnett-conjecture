import Burnett.Analysis.Microlocal.Overlap.WindowedClassicalSymmetricJetForm
import Burnett.Analysis.Microlocal.Overlap.CompactSymmetricJetWindowLimit
import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalCovariantPartition
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetCompactInputGlobalTail

/-! The global form tested by one compact chart output and an arbitrary compact input. -/
set_option autoImplicit false
set_option maxRecDepth 4750
set_option maxHeartbeats 6500000
set_option synthInstance.maxHeartbeats 390000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.F07.IntrinsicAmplitudeCoordinates (components)
open Burnett.RicciSymbol (Index)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- The near term asks for just one compact chart window. The separated
remainder of the original compact right input tends to zero. -/
theorem tendsto_originalCovariantGlobalCutoffTest_windowedClassicalChart [Nonempty M]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) (A : IntrinsicAmplitudeCovariance r)
    (hLocal : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (components b (A.density p)).PosSemidef)
    (Q : SymmetricJetGlobalForm M) (P : WindowedClassicalSymmetricJetForm B hB hn Q)
    (c : AtlasChart M) (S : Set M) (hS : IsCompact S) (hSc : S ⊆ c.chart.source)
    (α ρ : M → ℝ) (hα : ContMDiff Model 𝓘(ℝ) ∞ α) (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ)
    (hαc : HasCompactSupport α) (hρc : HasCompactSupport ρ) (hαS : tsupport α ⊆ S) :
    let τ := A.control.restrict (amplitudeCosphereWindow r S)
    let G (p : Cosphere r) := ((α (projection p) * ρ (projection p) : ℝ) : ℂ) *
      windowedClassicalFormDensity P A p
    Integrable G τ ∧
    Tendsto (fun n => conj (Q (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc (σ n))
        (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc (σ n))))
      atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro τ G
  obtain ⟨V, β, hV, hSV, hβ, hβc, hβs, hβOne⟩ := exists_globalPlateau_in_chart c S hS hSc
  let η := β * ρ
  have hη : ContMDiff Model 𝓘(ℝ) ∞ η := hβ.mul hρ
  have hηc : HasCompactSupport η := hβc.mul_right
  have hηs : tsupport η ⊆ c.chart.source := tsupport_mul_subset_left.trans hβs
  have hNear : EqOn ρ η V := by
    intro p hp
    change ρ p = β p * ρ p
    rw [hβOne p hp, one_mul]
  let L := S ∪ tsupport η
  have hL : IsCompact L := hS.union hηc
  have hLc : L ⊆ c.chart.source := union_subset hSc hηs
  have hSL : S ⊆ L := subset_union_left
  obtain ⟨χ, hχ, hχEq⟩ := exists_chartCutoff_of_globalScalar c α hα hαc (hαS.trans hSc)
  obtain ⟨ξ, hξ, hξEq⟩ := exists_chartCutoff_of_globalScalar c η hη hηc hηs
  have hχL : tsupport (χ : E → ℝ) ⊆ c.chart '' L := hχ.trans (image_mono (hαS.trans hSL))
  have hξL : tsupport (ξ : E → ℝ) ⊆ c.chart '' L := hξ.trans (image_mono subset_union_right)
  have hLt := image_subset_iff.mpr (c.chart.mapsTo.mono_left hLc)
  have hLcompact := hL.image_of_continuousOn (c.chart.continuousOn.mono hLc)
  obtain ⟨C⟩ := P.window c (c.chart '' L) hLcompact hLt
  let τL := A.control.restrict (amplitudeCosphereWindow r L)
  let G' (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    ∑ i : JetSlot, ∑ j : JetSlot,
      conj ((physicalCoefficient χ z.1 * physicalCoefficient ξ z.1) *
        P.principal c i j z.1 (WithLp.toLp 2 z.2)) * atlasOrderedJetEntry c A.density p j i
  obtain ⟨hIG', hLimit⟩ := tendsto_originalCovariantSymmetricJetTest_of_compactWindowData r B g hB hg hn
    σ A hLocal Q c L hL hLc (P.principal c) C χ ξ hχL hξL
  have hLm := measurableSet_amplitudeCosphereWindow r hL.isClosed.measurableSet
  have hSub : amplitudeCosphereWindow r S ⊆ amplitudeCosphereWindow r L := preimage_mono hSL
  have hAe : G' =ᵐ[τL] G := by
    filter_upwards [ae_restrict_mem (μ := A.control) hLm,
      ae_windowedClassicalFormDensity_eq_entries P A c hPos L hL.isClosed.measurableSet hLc] with p hp hDensity
    have hpc : projection p ∈ c.chart.source := hLc hp
    have hz := congrArg Prod.fst (fixedChartPhase_of_mem c p.val hpc)
    have hLeft : physicalCoefficient χ (fixedChartPhase c p.val).1 = (α (projection p) : ℂ) := by
      rw [hz]
      exact congrArg (fun a : ℝ => (a : ℂ)) (hχEq _ hpc)
    have hRight : physicalCoefficient ξ (fixedChartPhase c p.val).1 = (η (projection p) : ℂ) := by
      rw [hz]
      exact congrArg (fun a : ℝ => (a : ℂ)) (hξEq _ hpc)
    let w := ((α (projection p) * ρ (projection p) : ℝ) : ℂ)
    have hWeight : physicalCoefficient χ (fixedChartPhase c p.val).1 *
        physicalCoefficient ξ (fixedChartPhase c p.val).1 = w := by
      rw [hLeft, hRight, ← Complex.ofReal_mul]
      by_cases hpS : projection p ∈ S
      · rw [← hNear (hSV hpS)]
      · have hZero : α (projection p) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hpα => hpS (hαS hpα))
        simp [w, hZero]
    have hConj : conj w = w := Complex.conj_ofReal _
    calc
      G' p = w * ∑ i : JetSlot, ∑ j : JetSlot, conj (windowedClassicalFormMatrix P c p i j) *
          atlasOrderedJetEntry c A.density p j i := by
        change (∑ i, ∑ j, conj ((physicalCoefficient χ (fixedChartPhase c p.val).1 *
          physicalCoefficient ξ (fixedChartPhase c p.val).1) * windowedClassicalFormMatrix P c p i j) *
          atlasOrderedJetEntry c A.density p j i) = _
        simp_rw [hWeight]
        simp only [map_mul, hConj, Finset.mul_sum, mul_assoc]
      _ = G p := congrArg (w * ·) hDensity
  have hIG : Integrable G τL := hIG'.congr hAe
  have hInt : (∫ p, G' p ∂τL) = ∫ p, G p ∂τ := by
    rw [integral_congr_ae hAe]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hLm hSub
    intro p hp
    have hZero : α (projection p) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hpα => hp.2 (hαS hpα))
    simp [G, hZero]
  refine ⟨hIG.mono_measure (Measure.restrict_mono hSub le_rfl), ?_⟩
  let v := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc
  let u := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc
  let w := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG η hη hηc
  have hNearLimit : Tendsto (fun n => conj (Q (v (σ n)) (w (σ n)))) atTop (𝓝 (∫ p, G' p ∂τL)) := by
    apply hLimit.congr
    intro n
    change _ = conj (Q (v (σ n)) (w (σ n)))
    rw [show v (σ n) = originalCovariantSymmetricJetTest r B g hB hg hn c χ (hχL.trans hLt) (σ n)
      from originalCovariantGlobalCutoffTest_eq_chartTest r B g hB hg hn hsB hsG c α hα hαc
        (hαS.trans hSc) χ (hχL.trans hLt) hχEq (σ n),
      show w (σ n) = originalCovariantSymmetricJetTest r B g hB hg hn c ξ (hξL.trans hLt) (σ n)
      from originalCovariantGlobalCutoffTest_eq_chartTest r B g hB hg hn hsB hsG c η hη hηc
        hηs ξ (hξL.trans hLt) hξEq (σ n)]
  rw [hInt] at hNearLimit
  have hTail := tendsto_symmetricJetGlobalForm_originalFull_sub_near_of_compactInput
    r B g hB hg hn hsB hsG hconv hb Q P.kernel P.separated_action c S V hS hSc hV hSV
    (fun d T hT hTd hST => P.kernel_continuous c d S T hS hT hSc hTd hST)
    α ρ η hα hρ hη hαc hρc hηc hαS hNear
  have hErr : Tendsto (fun n => conj (Q (v (σ n)) (u (σ n))) - conj (Q (v (σ n)) (w (σ n))))
      atTop (𝓝 0) := by
    have hConj := (Complex.continuous_conj.tendsto (0 : ℂ)).comp (hTail.comp hσ)
    change Tendsto (fun n => conj (Q (v (σ n)) (u (σ n)) - Q (v (σ n)) (w (σ n)))) atTop (𝓝 (conj (0 : ℂ))) at hConj
    simpa only [map_sub, map_zero] using hConj
  have hFull := hErr.add hNearLimit
  rw [zero_add] at hFull
  exact hFull.congr (fun n => sub_add_cancel _ _)

end Burnett.Microlocal.Overlap
