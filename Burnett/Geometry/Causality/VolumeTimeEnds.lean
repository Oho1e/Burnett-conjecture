import Burnett.Geometry.Causality.ChronologicalVolume

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {M : Type*} [MeasurableSpace M]

/-- Along an increasing sequence of pasts, the logarithmic volume time
diverges to the future if the decreasing futures have null intersection. -/
theorem logarithmic_volume_time_tendsto_atTop {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsCountablyGenerated (atTop : Filter ι)] (μ : Measure M) [IsFiniteMeasure μ]
    {A B : ι → Set M} (hA : Monotone A) (hB : Antitone B)
    (hBmeas : ∀ n, MeasurableSet (B n)) (hApos : ∀ n, μ (A n) ≠ 0)
    (hBpos : ∀ n, μ (B n) ≠ 0) (hInt : μ (⋂ n, B n) = 0) :
    Tendsto (fun n => Real.log (μ (A n)).toReal - Real.log (μ (B n)).toReal) atTop atTop := by
  let i := Classical.arbitrary ι
  have hEnds : Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
    rw [← hInt]
    exact tendsto_measure_iInter_atTop (fun n => (hBmeas n).nullMeasurableSet) hB
      ⟨i, measure_ne_top μ _⟩
  have hEndsReal : Tendsto (fun n => (μ (B n)).toReal) atTop (𝓝 0) := by
    have hReal := ENNReal.continuousAt_toReal (x := 0) (by simp)
    simpa only [ENNReal.toReal_zero] using hReal.tendsto.comp hEnds
  have hAbove : Tendsto (fun n => (μ (B n)).toReal) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hEndsReal,
      Eventually.of_forall fun n => ENNReal.toReal_pos (hBpos n) (measure_ne_top μ _)⟩
  have hLog : Tendsto (fun n => Real.log (μ (B n)).toReal) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hAbove
  have hLower (n : ι) (hi : i ≤ n) : Real.log (μ (A i)).toReal ≤ Real.log (μ (A n)).toReal := by
    have hSet : μ (A i) ≤ μ (A n) := measure_mono (hA hi)
    have hReal := ENNReal.toReal_mono (measure_ne_top μ _) hSet
    have hPos := ENNReal.toReal_pos (hApos i) (measure_ne_top μ _)
    exact (Real.log_le_log_iff hPos (hPos.trans_le hReal)).mpr hReal
  apply tendsto_atTop.mpr
  intro t
  filter_upwards [tendsto_atBot.mp hLog (Real.log (μ (A i)).toReal - t), eventually_ge_atTop i] with n hn hi
  have hLowerN := hLower n hi
  linarith

/-- At the past end, the past volumes vanish and the time diverges to the past. -/
theorem logarithmic_volume_time_tendsto_atBot {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsCountablyGenerated (atTop : Filter ι)] (μ : Measure M) [IsFiniteMeasure μ]
    {A B : ι → Set M} (hA : Antitone A) (hB : Monotone B)
    (hAmeas : ∀ n, MeasurableSet (A n)) (hApos : ∀ n, μ (A n) ≠ 0)
    (hBpos : ∀ n, μ (B n) ≠ 0) (hInt : μ (⋂ n, A n) = 0) :
    Tendsto (fun n => Real.log (μ (A n)).toReal - Real.log (μ (B n)).toReal) atTop atBot := by
  have ht := logarithmic_volume_time_tendsto_atTop μ hB hA hAmeas hBpos hApos hInt
  simpa only [Function.comp_def, neg_sub] using tendsto_neg_atTop_atBot.comp ht

end Burnett.Geometry.FiniteCausalVolume
