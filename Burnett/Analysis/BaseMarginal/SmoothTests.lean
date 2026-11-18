import Burnett.Geometry.FlatRigidity.WeakCurvature
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Smooth tests of local base measures

Pointwise positivity and determination of finite measures on one coordinate region.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F08.ActualBaseMarginal

open Filter MeasureTheory Set Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology

/-- Positivity on every nonnegative smooth test, together with local open-set
positivity of the genuine base volume, gives the pointwise sign of a continuous field. -/
theorem nonnegOn_of_smooth_test_integrals
    (μ : Measure CoordinateSpace) {U : Set CoordinateSpace} (hU : IsOpen U)
    (f : CoordinateSpace → ℝ) (hf : ContinuousOn f U)
    (hopen : ∀ V : Set CoordinateSpace, IsOpen V → V ⊆ U → V.Nonempty → μ V ≠ 0)
    (hInt : ∀ φ : CoordinateSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → Integrable (fun x => φ x * f x) μ)
    (htest : ∀ φ : CoordinateSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, φ x * f x ∂μ) :
    ∀ x ∈ U, 0 ≤ f x := by
  intro y hy
  by_contra! hyf
  let V : Set CoordinateSpace := {x ∈ U | f x < 0}
  have hV : IsOpen V := isOpen_iff_mem_nhds.mpr fun x hx => by
    have hUx := hU.mem_nhds hx.1
    exact inter_mem hUx ((hf.continuousAt hUx).preimage_mem_nhds (isOpen_Iio.mem_nhds hx.2))
  have hyV : y ∈ V := ⟨hy, hyf⟩
  have hsub : ({y} : Set CoordinateSpace) ⊆ V := singleton_subset_iff.mpr hyV
  obtain ⟨L, _, _, hLV, φ, hs, hc, hφL, hφn, hφone⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart isCompact_singleton hV hsub
  have hφV := hφL.trans hLV
  have hφU : tsupport φ ⊆ U := hφV.trans (fun _ hx => hx.1)
  have hφy : φ y = 1 := hφone y rfl
  let g (x : CoordinateSpace) := -(φ x * f x)
  have hPos : 0 ≤ g := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hφn x).1 (hφV hx).2.le)
    · simp [g, image_eq_zero_of_notMem_tsupport hx]
  have hgInt : Integrable g μ := (hInt φ hs hc hφU).neg
  let W : Set CoordinateSpace := V ∩ {x | 0 < φ x}
  have hW : IsOpen W := hV.inter (isOpen_lt continuous_const hs.continuous)
  have hWU : W ⊆ U := fun _ hx => hx.1.1
  have hWne : W.Nonempty := ⟨y, hyV, by change 0 < φ y; rw [hφy]; exact zero_lt_one⟩
  have hWg : W ⊆ Function.support g := by
    intro x hx
    exact (neg_pos.mpr (mul_neg_of_pos_of_neg hx.2 hx.1.2)).ne'
  have hmass : 0 < μ (Function.support g) :=
    (pos_iff_ne_zero.mpr (hopen W hW hWU hWne)).trans_le (measure_mono hWg)
  have hp := (integral_pos_iff_support_of_nonneg hPos hgInt).mpr hmass
  have ht := htest φ hs hc hφU (fun x => (hφn x).1)
  change 0 < ∫ x, -(φ x * f x) ∂μ at hp
  rw [integral_neg] at hp
  linarith

end Burnett.F08.ActualBaseMarginal

namespace Burnett.F08.ActualBaseMarginal

open MeasureTheory Set Filter Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology ENNReal

/-- Smooth compact tests determine finite Borel measures concentrated on
the tested open coordinate region. Compact sets are separated from the
complement of a chosen open neighborhood by smooth functions. -/
theorem finiteMeasures_eq_of_local_smooth_tests
    (μ ν : Measure CoordinateSpace) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U : Set CoordinateSpace} (hU : IsOpen U) (hμ : μ Uᶜ = 0) (hν : ν Uᶜ = 0)
    (htest : ∀ φ : CoordinateSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν := by
  have hCompact (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ U) : μ K = ν K := by
    have hOneWay (m n : Measure CoordinateSpace) [IsFiniteMeasure m] [IsFiniteMeasure n]
        (hMom : ∀ φ : CoordinateSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ U → (∫ x, φ x ∂m) = ∫ x, φ x ∂n) :
        m K ≤ n K := by
      apply le_of_forall_gt
      intro b hb
      obtain ⟨W, hKW, hW, hnW⟩ := K.exists_isOpen_lt_of_lt (μ := n) b hb
      let V := W ∩ U
      have hV : IsOpen V := hW.inter hU
      have hKV : K ⊆ V := subset_inter hKW hKU
      obtain ⟨L, _, _, hLV, φ, hs, hc, hφL, hφB, hφ1⟩ :=
        Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hK hV hKV
      have hφV := hφL.trans hLV
      have hφU : tsupport φ ⊆ U := hφV.trans inter_subset_right
      have hBelow : m.real K ≤ ∫ x, φ x ∂m := by
        have hI : Integrable (K.indicator (fun _ : CoordinateSpace => (1 : ℝ))) m :=
          (integrable_const (1 : ℝ)).indicator hK.measurableSet
        calc
          _ = ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂m := by
            rw [integral_indicator hK.measurableSet]
            simp
          _ ≤ _ := integral_mono hI (hs.continuous.integrable_of_hasCompactSupport hc) (fun x => by
            by_cases hx : x ∈ K
            · simp [Set.indicator_of_mem hx, hφ1 x hx]
            · simpa only [Set.indicator_of_notMem hx] using (hφB x).1)
      have hAbove : (∫ x, φ x ∂n) ≤ n.real V := by
        have hI : Integrable (V.indicator (fun _ : CoordinateSpace => (1 : ℝ))) n :=
          (integrable_const (1 : ℝ)).indicator hV.measurableSet
        calc
          _ ≤ ∫ x, V.indicator (fun _ => (1 : ℝ)) x ∂n :=
            integral_mono (hs.continuous.integrable_of_hasCompactSupport hc) hI (fun x => by
              by_cases hx : x ∈ V
              · simpa only [Set.indicator_of_mem hx] using (hφB x).2
              · rw [Set.indicator_of_notMem hx,
                  image_eq_zero_of_notMem_tsupport (fun hxT => hx (hφV hxT))])
          _ = _ := by rw [integral_indicator hV.measurableSet]; simp
      have hReal := hBelow.trans ((hMom φ hs hc hφU).le.trans hAbove)
      have hMass : m K ≤ n V :=
        (ENNReal.toReal_le_toReal (measure_ne_top m _) (measure_ne_top n _)).mp hReal
      exact (hMass.trans (measure_mono inter_subset_left)).trans_lt hnW
    exact le_antisymm (hOneWay μ ν htest)
      (hOneWay ν μ (fun φ hφ hcφ hsφ => (htest φ hφ hcφ hsφ).symm))
  apply Measure.ext
  intro S hS
  have hμae : ∀ᵐ x ∂μ, x ∈ U := by rwa [ae_iff]
  have hνae : ∀ᵐ x ∂ν, x ∈ U := by rwa [ae_iff]
  have hSett (m : Measure CoordinateSpace) (hm : ∀ᵐ x ∂m, x ∈ U) :
      m S = m (S ∩ U) := by
    apply measure_congr
    filter_upwards [hm] with x hx
    apply propext
    change x ∈ S ↔ x ∈ S ∩ U
    exact ⟨fun hs => ⟨hs, hx⟩, fun hs => hs.1⟩
  rw [hSett μ hμae, hSett ν hνae]
  rw [(hS.inter hU.measurableSet).measure_eq_iSup_isCompact μ,
    (hS.inter hU.measurableSet).measure_eq_iSup_isCompact ν]
  apply iSup_congr
  intro K
  apply iSup_congr
  intro hKS
  apply iSup_congr
  intro hK
  exact hCompact K hK (hKS.trans inter_subset_right)

end Burnett.F08.ActualBaseMarginal
