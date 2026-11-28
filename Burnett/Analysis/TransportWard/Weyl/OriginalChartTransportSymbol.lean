import Burnett.Analysis.TransportClosure.C04HamiltonChartRegularity
import Burnett.Analysis.TransportClosure.C04OddChartPartition

set_option autoImplicit false
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.C04

open Function Filter Set Burnett.RicciSymbol
open scoped ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open CotangentAngularExtension

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The coordinate symbol of the genuine test, using zero outside the chart
and at the excluded zero covectors. -/
def originalChartTransportSymbol (c : M) (b : CotangentBundle M → ℝ) (x : E) (ξ : Covector) : ℝ := by
  classical
  exact if x ∈ (chartAt E c).target ∧ ξ ≠ 0 then b (cotangentChartInverse c (x, ξ)) else 0

theorem originalChartTransportSymbol_eq (c : M) (b : CotangentBundle M → ℝ)
    (x : E) (hx : x ∈ (chartAt E c).target) (ξ : Covector) (hξ : ξ ≠ 0) :
    originalChartTransportSymbol c b x ξ = b (cotangentChartInverse c (x, ξ)) :=
  if_pos ⟨hx, hξ⟩

theorem originalChartTransportSymbol_eq_zero_off_image (c : M) (b : CotangentBundle M → ℝ)
    {K : Set M} (hZero : ∀ p ∈ puncturedCotangent, p.proj ∉ K → b p = 0)
    (x : E) (hx : x ∉ (chartAt E c) '' K) (ξ : Covector) :
    originalChartTransportSymbol c b x ξ = 0 := by
  classical
  let e := chartAt E c
  by_cases h : x ∈ e.target ∧ ξ ≠ 0
  · rw [originalChartTransportSymbol_eq c b x h.1 ξ h.2]
    apply hZero (cotangentChartInverse c (x, ξ)) (cotangentChartInverse_mapsTo_punctured c h)
    intro hk
    apply hx
    change e.symm x ∈ K at hk
    exact ⟨e.symm x, hk, e.right_inv h.1⟩
  · exact if_neg h

/-- The exact extension of the intrinsic chart test has the support, smooth
positive homogeneity and antipodal parity used by the variable Weyl and
frozen cubic calculations. -/
theorem originalChartTransportSymbol_properties [T2Space M] (c : M) (b : CotangentBundle M → ℝ)
    (hb : IsDegreeOneTransportTest b) (hOdd : IsAntipodallyOdd b) {K : Set M}
    (hK : IsCompact K) (hSub : K ⊆ (chartAt E c).source)
    (hZero : ∀ p ∈ puncturedCotangent, p.proj ∉ K → b p = 0) :
    let L := (chartAt E c) '' K
    let a := originalChartTransportSymbol c b
    IsCompact L ∧ L ⊆ (chartAt E c).target ∧ (∀ x ∉ L, ∀ ξ, a x ξ = 0) ∧
      ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)) ∧
      (∀ x (t : ℝ), 0 < t → ∀ ξ : Covector, ξ ≠ 0 → a x (t • ξ) = t * a x ξ) ∧
      (∀ x (ξ : Covector), a x (-ξ) = -a x ξ) := by
  intro L a
  let e := chartAt E c
  have hL : IsCompact L := hK.image_of_continuousOn (e.continuousOn.mono hSub)
  have hLT : L ⊆ e.target := Set.image_subset_iff.mpr (e.mapsTo.mono_left hSub)
  have hOff (x : E) (hx : x ∉ L) (ξ : Covector) : a x ξ = 0 :=
    originalChartTransportSymbol_eq_zero_off_image c b hZero x hx ξ
  refine ⟨hL, hLT, hOff, ?_, ?_, ?_⟩
  · intro z hz
    have hz0 : z.2 ≠ 0 := hz.2
    by_cases hx : z.1 ∈ e.target
    · have hMem : z ∈ UnitNullAngular.chartPunctured c := ⟨hx, hz0⟩
      have hC := (contDiffOn_cotangentChartTest_joint c b hb.1).contDiffAt
        ((isOpen_chartPunctured c).mem_nhds hMem)
      have hEq : uncurry a =ᶠ[𝓝 z] b ∘ cotangentChartInverse c := by
        filter_upwards [(isOpen_chartPunctured c).mem_nhds hMem] with q hq
        exact originalChartTransportSymbol_eq c b q.1 hq.1 q.2 hq.2
      exact (hC.congr_of_eventuallyEq hEq).contDiffWithinAt
    · have hzL : z.1 ∉ L := fun h => hx (hLT h)
      have hOpen : IsOpen (Prod.fst ⁻¹' Lᶜ : Set (E × Covector)) :=
        hL.isClosed.isOpen_compl.preimage continuous_fst
      have hEq : uncurry a =ᶠ[𝓝 z] fun _ : E × Covector => (0 : ℝ) := by
        filter_upwards [hOpen.mem_nhds hzL] with q hq
        exact hOff q.1 hq q.2
      exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hEq).contDiffWithinAt
  · intro x t ht ξ hξ
    by_cases hx : x ∈ e.target
    · dsimp only [a]
      rw [originalChartTransportSymbol_eq c b x hx (t • ξ) (smul_ne_zero ht.ne' hξ),
        originalChartTransportSymbol_eq c b x hx ξ hξ, cotangentChartInverse_scale c x hx ξ t]
      exact hb.2.1 _ (cotangentChartInverse_mapsTo_punctured c ⟨hx, hξ⟩) t ht
    · rw [hOff x (fun h => hx (hLT h)), hOff x (fun h => hx (hLT h)), mul_zero]
  · intro x ξ
    by_cases hx : x ∈ e.target
    · by_cases hξ : ξ = 0
      · subst ξ
        have hz : a x 0 = 0 := if_neg (fun h => h.2 rfl)
        rw [neg_zero, hz, neg_zero]
      · dsimp only [a]
        rw [originalChartTransportSymbol_eq c b x hx (-ξ) (neg_ne_zero.mpr hξ),
          originalChartTransportSymbol_eq c b x hx ξ hξ, ← neg_one_smul ℝ ξ,
          cotangentChartInverse_scale c x hx ξ (-1)]
        exact hOdd _ (cotangentChartInverse_mapsTo_punctured c ⟨hx, hξ⟩)
    · rw [hOff x (fun h => hx (hLT h)), hOff x (fun h => hx (hLT h)), neg_zero]

end Burnett.C04
