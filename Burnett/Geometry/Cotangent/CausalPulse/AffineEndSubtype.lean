import Burnett.Geometry.Cotangent.NullTrajectoryContinuation

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonAffineReparam

open Set Filter
open scoped Topology
open Burnett.Geometry.CotangentHamiltonAffineExtension (rightAffineEndFilter lt_sSup_of_mem_open_interval)
open Burnett.Geometry.CotangentHamiltonTimeReversal (leftAffineEndFilter)

/-- The topology of the future affine end agrees with the upper tail filter
of the actual open parameter interval, including the finite endpoint case. -/
theorem map_atTop_coe_eq_rightAffineEnd {I : Set ℝ} (hI : IsOpen I)
    (hOrd : I.OrdConnected) (hNe : I.Nonempty) :
    Filter.map ((↑) : I → ℝ) atTop = rightAffineEndFilter I := by
  letI : Nonempty I := hNe.to_subtype
  have hIright := (affineEndFilters_eventually_mem I hI hOrd hNe).2
  classical
  ext U
  change ((↑) : I → ℝ) ⁻¹' U ∈ (atTop : Filter I) ↔ U ∈ rightAffineEndFilter I
  by_cases hBound : BddAbove I
  · have hEventually : ∀ᶠ t in 𝓝[<] (sSup I), t ∈ I := by
      simpa only [rightAffineEndFilter, if_pos hBound] using hIright
    rw [rightAffineEndFilter, if_pos hBound]
    constructor
    · intro hU
      obtain ⟨a, ha⟩ := eventually_atTop.mp hU
      filter_upwards [hEventually, Ioo_mem_nhdsLT (lt_sSup_of_mem_open_interval hI hBound a.property)] with t ht ht'
      exact ha ⟨t, ht⟩ ht'.1.le
    · intro hU
      obtain ⟨b, hb, hUb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hU
      obtain ⟨a, ha, hba⟩ := exists_lt_of_lt_csSup hNe hb
      exact eventually_atTop.mpr ⟨⟨a, ha⟩, fun t ht =>
        hUb ⟨hba.trans_le ht, lt_sSup_of_mem_open_interval hI hBound t.property⟩⟩
  · have hEventually : ∀ᶠ t in atTop, t ∈ I := by
      simpa only [rightAffineEndFilter, if_neg hBound] using hIright
    rw [rightAffineEndFilter, if_neg hBound]
    constructor
    · intro hU
      obtain ⟨a, ha⟩ := eventually_atTop.mp hU
      filter_upwards [hEventually, eventually_ge_atTop (a : ℝ)] with t ht ht'
      exact ha ⟨t, ht⟩ ht'
    · intro hU
      obtain ⟨b, hb⟩ := eventually_atTop.mp hU
      obtain ⟨a, ha, hba⟩ := not_bddAbove_iff.mp hBound b
      exact eventually_atTop.mpr ⟨⟨a, ha⟩, fun t ht => hb _ (hba.le.trans ht)⟩

private theorem sInf_lt_of_mem_open_domain {I : Set ℝ} (hI : IsOpen I)
    (hBound : BddBelow I) {a : ℝ} (ha : a ∈ I) : sInf I < a := by
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds ha)
  have hm : (l + a) / 2 < a := by linarith [hlr.1]
  exact (csInf_le hBound (hsub ⟨by linarith [hlr.1], hm.trans hlr.2⟩)).trans_lt hm

/-- The topology of the past affine end agrees with the lower tail filter
of the actual open parameter interval, including the finite endpoint case. -/
theorem map_atBot_coe_eq_leftAffineEnd {I : Set ℝ} (hI : IsOpen I)
    (hOrd : I.OrdConnected) (hNe : I.Nonempty) :
    Filter.map ((↑) : I → ℝ) atBot = leftAffineEndFilter I := by
  letI : Nonempty I := hNe.to_subtype
  have hIleft := (affineEndFilters_eventually_mem I hI hOrd hNe).1
  classical
  ext U
  change ((↑) : I → ℝ) ⁻¹' U ∈ (atBot : Filter I) ↔ U ∈ leftAffineEndFilter I
  by_cases hBound : BddBelow I
  · have hEventually : ∀ᶠ t in 𝓝[>] (sInf I), t ∈ I := by
      simpa only [leftAffineEndFilter, if_pos hBound] using hIleft
    rw [leftAffineEndFilter, if_pos hBound]
    constructor
    · intro hU
      obtain ⟨a, ha⟩ := eventually_atBot.mp hU
      filter_upwards [hEventually, Ioo_mem_nhdsGT (sInf_lt_of_mem_open_domain hI hBound a.property)] with t ht ht'
      exact ha ⟨t, ht⟩ ht'.2.le
    · intro hU
      obtain ⟨b, hb, hUb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hU
      obtain ⟨a, ha, hab⟩ := exists_lt_of_csInf_lt hNe hb
      exact eventually_atBot.mpr ⟨⟨a, ha⟩, fun t ht =>
        hUb ⟨sInf_lt_of_mem_open_domain hI hBound t.property, (show (t : ℝ) ≤ a from ht).trans_lt hab⟩⟩
  · have hEventually : ∀ᶠ t in atBot, t ∈ I := by
      simpa only [leftAffineEndFilter, if_neg hBound] using hIleft
    rw [leftAffineEndFilter, if_neg hBound]
    constructor
    · intro hU
      obtain ⟨a, ha⟩ := eventually_atBot.mp hU
      filter_upwards [hEventually, eventually_le_atBot (a : ℝ)] with t ht ht'
      exact ha ⟨t, ht⟩ ht'
    · intro hU
      obtain ⟨b, hb⟩ := eventually_atBot.mp hU
      obtain ⟨a, ha, hab⟩ := not_bddBelow_iff.mp hBound b
      exact eventually_atBot.mpr ⟨⟨a, ha⟩, fun t ht => hb _ ((show (t : ℝ) ≤ a from ht).trans hab.le)⟩

theorem atTop_isCountablyGenerated_open_interval {I : Set ℝ} (hI : IsOpen I)
    (hOrd : I.OrdConnected) (hNe : I.Nonempty) : IsCountablyGenerated (atTop : Filter I) := by
  haveI : IsCountablyGenerated (rightAffineEndFilter I) := by
    unfold rightAffineEndFilter
    split <;> infer_instance
  have h := comap_map (f := (atTop : Filter I)) Subtype.coe_injective
  rw [map_atTop_coe_eq_rightAffineEnd hI hOrd hNe] at h
  rw [← h]
  infer_instance

theorem atBot_isCountablyGenerated_open_interval {I : Set ℝ} (hI : IsOpen I)
    (hOrd : I.OrdConnected) (hNe : I.Nonempty) : IsCountablyGenerated (atBot : Filter I) := by
  haveI : IsCountablyGenerated (leftAffineEndFilter I) := by
    unfold leftAffineEndFilter
    split <;> infer_instance
  have h := comap_map (f := (atBot : Filter I)) Subtype.coe_injective
  rw [map_atBot_coe_eq_leftAffineEnd hI hOrd hNe] at h
  rw [← h]
  infer_instance

end Burnett.Geometry.CotangentHamiltonAffineReparam
