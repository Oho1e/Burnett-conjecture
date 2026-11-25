import Burnett.Geometry.Causality.ChartChronologicalNeighborhoods
import Burnett.Geometry.Causality.ClosedCausalDiamonds

set_option autoImplicit false
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter MeasureTheory
open scoped ENNReal ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

variable {M : Type*} [TopologicalSpace M]

/-- Causally convex neighborhoods distinguish points by their chronological
past and future. -/
theorem eq_of_chronological_sections_eq [T1Space M]
    {I J : Set (M × M)} (hIJ : I ⊆ J)
    (hAround : ∀ x : M, ∀ V ∈ 𝓝 x, ∃ a b : M, a ∈ V ∧ b ∈ V ∧ (a, x) ∈ I ∧ (x, b) ∈ I)
    (hLoc : ∀ x : M, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → (a, z) ∈ J → (z, b) ∈ J → z ∈ V)
    {x y : M} (hp : sectionAt I x = sectionAt I y)
    (hf : sectionAt (Prod.swap ⁻¹' I) x = sectionAt (Prod.swap ⁻¹' I) y) : x = y := by
  by_contra hne
  obtain ⟨V, hV, hVout, hVconv⟩ := hLoc x ({y}ᶜ) (isOpen_compl_singleton.mem_nhds (by simpa using hne))
  obtain ⟨a, b, ha, hb, hax, hxb⟩ := hAround x V hV
  have hay : (a, y) ∈ I := by
    change a ∈ sectionAt I y
    rw [← hp]
    exact hax
  have hyb : (y, b) ∈ I := by
    change b ∈ sectionAt (Prod.swap ⁻¹' I) y
    rw [← hf]
    exact hxb
  exact hVout (hVconv ha hb (hIJ hay) (hIJ hyb)) (mem_singleton y)

variable [MeasurableSpace M] [BorelSpace M]

theorem past_volume_strict_of_proper_inclusion (μ : Measure M) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {I : Set (M × M)} (hI : IsOpen I) (hTrans : Transitive fun a b => (a, b) ∈ I)
    (hMid : ∀ ⦃a b : M⦄, (a, b) ∈ I → ∃ c, (a, c) ∈ I ∧ (c, b) ∈ I)
    {x y : M} (hSub : sectionAt I x ⊆ sectionAt I y) (hNe : sectionAt I x ≠ sectionAt I y) :
    μ (sectionAt I x) < μ (sectionAt I y) := by
  let A := sectionAt I x
  let B := sectionAt I y
  have hA : IsOpen A := hI.preimage (continuous_id.prodMk continuous_const)
  have hB : IsOpen B := hI.preimage (continuous_id.prodMk continuous_const)
  have hNot : ¬ B ⊆ A := fun h => hNe (Subset.antisymm hSub h)
  obtain ⟨p, hp, hp'⟩ := not_subset.mp hNot
  obtain ⟨q, hpq, hqy⟩ := hMid hp
  have hqA : q ∉ closure A := by
    intro hq
    let W := (fun z : M => (p, z)) ⁻¹' I
    have hW : IsOpen W := hI.preimage (continuous_const.prodMk continuous_id)
    obtain ⟨z, hz, hzx⟩ := mem_closure_iff.mp hq W hW hpq
    exact hp' (hTrans hz hzx)
  have hGap : IsOpen (B \ closure A) := hB.inter isClosed_closure.isOpen_compl
  refine measure_lt_of_open_gap μ hA.measurableSet hSub hGap
    ⟨q, hqy, hqA⟩ (fun z hz => ⟨hz.1, fun hzA => hz.2 (subset_closure hzA)⟩)

/-- The logarithmic volume time is strictly increasing between distinct
causally related points once chronological past/future inclusion is known. -/
theorem logarithmic_volume_time_strict_along_causal [T1Space M] (μ : Measure M)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {I J : Set (M × M)} (hI : IsOpen I) (hIJ : I ⊆ J)
    (hTrans : Transitive fun a b => (a, b) ∈ I)
    (hMid : ∀ ⦃a b : M⦄, (a, b) ∈ I → ∃ c, (a, c) ∈ I ∧ (c, b) ∈ I)
    (hAround : ∀ x : M, ∀ V ∈ 𝓝 x, ∃ a b : M, a ∈ V ∧ b ∈ V ∧ (a, x) ∈ I ∧ (x, b) ∈ I)
    (hLoc : ∀ x : M, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → (a, z) ∈ J → (z, b) ∈ J → z ∈ V)
    {x y : M} (hne : x ≠ y)
    (hp : sectionAt I x ⊆ sectionAt I y)
    (hf : sectionAt (Prod.swap ⁻¹' I) y ⊆ sectionAt (Prod.swap ⁻¹' I) x) :
    let T p := Real.log (μ (sectionAt I p)).toReal - Real.log (μ (sectionAt (Prod.swap ⁻¹' I) p)).toReal
    T x < T y := by
  intro T
  let I' := Prod.swap ⁻¹' I
  have hI' : IsOpen I' := hI.preimage continuous_swap
  have hPositive (p : M) : 0 < (μ (sectionAt I p)).toReal ∧ 0 < (μ (sectionAt I' p)).toReal := by
    obtain ⟨a, b, _, _, ha, hb⟩ := hAround p univ univ_mem
    have ho : IsOpen (sectionAt I p) := hI.preimage (continuous_id.prodMk continuous_const)
    have ho' : IsOpen (sectionAt I' p) := hI'.preimage (continuous_id.prodMk continuous_const)
    exact ⟨ENNReal.toReal_pos (ho.measure_ne_zero μ ⟨a, ha⟩) (measure_ne_top μ _),
      ENNReal.toReal_pos (ho'.measure_ne_zero μ ⟨b, hb⟩) (measure_ne_top μ _)⟩
  let P p := Real.log (μ (sectionAt I p)).toReal
  let F p := Real.log (μ (sectionAt I' p)).toReal
  have hpLe : P x ≤ P y := Real.log_le_log (hPositive x).1 (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hp))
  have hfLe : F y ≤ F x := Real.log_le_log (hPositive y).2 (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hf))
  change P x - F x < P y - F y
  by_cases heP : sectionAt I x = sectionAt I y
  · have heF : sectionAt I' y ≠ sectionAt I' x := fun h =>
      hne (eq_of_chronological_sections_eq hIJ hAround hLoc heP h.symm)
    have hfStrict := past_volume_strict_of_proper_inclusion μ hI'
      (fun _ _ _ ha hb => hTrans hb ha)
      (by intro a b h; obtain ⟨z, hz, hz'⟩ := hMid h; exact ⟨z, hz', hz⟩) hf heF
    have hLog := Real.log_lt_log (hPositive y).2 ((ENNReal.toReal_lt_toReal (measure_ne_top μ _)
      (measure_ne_top μ _)).mpr hfStrict)
    change F y < F x at hLog
    linarith
  · have hpStrict := past_volume_strict_of_proper_inclusion μ hI hTrans hMid hp heP
    have hLog := Real.log_lt_log (hPositive x).1 ((ENNReal.toReal_lt_toReal (measure_ne_top μ _)
      (measure_ne_top μ _)).mpr hpStrict)
    change P x < P y at hLog
    linarith

end Burnett.Geometry.FiniteCausalVolume
