import Burnett.Analysis.AngularCaps.ActualEnlargedCapJets
import Burnett.Analysis.AngularCaps.ParabolicBaseNeighbors
import Burnett.Analysis.AngularCaps.ParabolicBaseTemplate

set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Filter Function
open scoped BigOperators Topology ContDiff

/-- An exact encoding of a variable-size finite sum by a fixed number of
coefficients. In unused slots the coefficient is zero and the coordinate
is the nonzero null axis. -/
theorem exists_zeroPadded_capNeighbors {t : Finset Vec} {N : ℕ} (hN : t.card ≤ N)
    (u : Vec → NullFrequencyCoordinates) :
    ∃ v : CapNeighborParameters N,
      (∀ i, v i = (0,nullAxis) ∨ ∃ x ∈ t, v i = (1,u x)) ∧
      ∀ f : NullFrequencyCoordinates → ℝ, ∑ i, (v i).1*f (v i).2 = ∑ x ∈ t, f (u x) := by
  classical
  have hCard : Fintype.card {x // x ∈ t} ≤ N := by simpa only [Fintype.card_coe] using hN
  let e : {x // x ∈ t} ↪ Fin N :=
    (Fintype.equivFin {x // x ∈ t}).toEmbedding.trans (Fin.castLEEmb hCard)
  let v (i : Fin N) : ℝ × NullFrequencyCoordinates := if h : ∃ x : {x // x ∈ t}, e x = i then
    (1,u (Classical.choose h).1) else (0,nullAxis)
  have hPick (x : {x // x ∈ t}) : v (e x) = (1,u x.1) := by
    have hx : ∃ y : {y // y ∈ t}, e y = e x := ⟨x,rfl⟩
    simp only [v,dif_pos hx]
    rw [e.injective (Classical.choose_spec hx)]
  refine ⟨v,?_,?_⟩
  · intro i
    by_cases hi : ∃ x : {x // x ∈ t}, e x = i
    · exact Or.inr ⟨(Classical.choose hi).1,(Classical.choose hi).2,by simp only [v,dif_pos hi]⟩
    · exact Or.inl (by simp only [v,dif_neg hi])
  · intro f
    have hz (i : Fin N) (_ : i ∈ Finset.univ) (hi : i ∉ Finset.univ.map e) :
        (v i).1 * f (v i).2 = 0 := by
      have hi' : ¬∃ x : {x // x ∈ t}, e x = i :=
        fun ⟨x,hx⟩ => hi (Finset.mem_map.mpr ⟨x,Finset.mem_univ x,hx⟩)
      simp only [v,dif_neg hi',zero_mul]
    calc
      _ = ∑ i ∈ Finset.univ.map e, (v i).1 * f (v i).2 :=
        (Finset.sum_subset (Finset.subset_univ _) hz).symm
      _ = ∑ x : {x // x ∈ t}, (v (e x)).1 * f (v (e x)).2 := Finset.sum_map _ _ _
      _ = ∑ x : {x // x ∈ t}, f (u x.1) :=
        Finset.sum_congr rfl fun x _ => by simp only [hPick,one_mul]
      _ = _ := by
        have he : (Finset.univ : Finset {x // x ∈ t}) = t.attach := by ext x; simp
        rw [he]
        exact Finset.sum_attach t (fun x => f (u x))

private theorem absolute_coordinates_norm_le {u : NullFrequencyCoordinates} {V : ℝ}
    (hs : |u.1| ≤ V) (ht : |u.2.1| ≤ V) (hz : ‖u.2.2‖ ≤ V) : ‖u‖ ≤ V := by
  rw [Prod.norm_def,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  exact max_le hs (max_le ht hz)

/-- The actual base symbol has the `δ`-independent weighted derivative bounds,
using only the finite angular overlap and common norm bounds for its
null-coordinate charts. -/
theorem actual_capMultiplier_parabolic_jets (B inner outer : ℝ) {a : ℝ}
    (ha : 0 < a) (hIn : 0 ≤ inner) (hIO : inner < outer) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
      ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
      ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 4*B*(4*δ) ≤ 1 →
      ∀ t : Finset Vec, (↑t : Set Vec) ⊆ unitNull m →
      (↑t : Set Vec).Pairwise (fun v z => δ/4 < projectiveDist v z) →
      ∀ u : NullFrequencyCoordinates, u ≠ 0 →
        ‖u‖^j*‖iteratedFDeriv ℝ j (fun v =>
          capMultiplier t m δ (a*δ^2) inner outer w (chartScaledFrequency F δ v)) u‖ ≤ C := by
  let Z := 4*B*1
  let T := Z^2+4*(outer*a)
  let M := max 1 (max Z T)
  let V := max 1 (max B (max (16*B^2) ((16*B)^2*B)))
  let N : ℕ := 17^4
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨C,hC,hJ⟩ := parabolicBaseProfile_uniformJets N inner outer B V ha.ne'
    (one_div_pos.mpr hM) (show (0:ℝ) < 1/2 by norm_num) j
  refine ⟨C,hC,?_⟩
  intro m w F hw hF hI δ hδ hδone hSmall t ht hSep
  let mapFreq := chartScaledFrequency F δ
  let P (u : NullFrequencyCoordinates) := capMultiplier t m δ (a*δ^2) inner outer w (mapFreq u)
  have hη : 0 < a*δ^2 := mul_pos ha (pow_pos hδ _)
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have ht0 (z : Vec) (hz : z ∈ t) : z ≠ 0 := by
    have hNorm : ‖z‖ = 1 := (ht hz).1
    intro h
    simp [h] at hNorm
  have hMap : ContDiff ℝ ∞ mapFreq := chartScaledFrequency_contDiff F δ
  have hSmooth : ContDiffOn ℝ ∞ P {u | u ≠ 0} :=
    (capMultiplier_contDiffOn ht0 m δ hη inner outer hw0).comp hMap.contDiffOn
      (fun _ hu => chartScaledFrequency_ne_zero F hδ.ne' hu)
  have hDegree (r : ℝ) (hr : r ≠ 0) (u : NullFrequencyCoordinates) : P (r • u) = P u := by
    change capMultiplier t m δ (a*δ^2) inner outer w (chartScaledFrequency F δ (r • u)) = P u
    rw [chartScaledFrequency_smul]
    exact capMultiplier_degreeZero t m δ (a*δ^2) inner outer w r hr (mapFreq u)
  have hOnSphere (u : NullFrequencyCoordinates) (hu : ‖u‖ = 1) :
      ‖iteratedFDeriv ℝ j P u‖ ≤ C := by
    let x := mapFreq u
    have hu0 : u ≠ 0 := by intro h; simp [h] at hu
    have hx : x ≠ 0 := chartScaledFrequency_ne_zero F hδ.ne' hu0
    by_cases hs : x ∈ tsupport (capMultiplier t m δ (a*δ^2) inner outer w)
    · have hSupp := capMultiplier_tsupport_bounds hδ hη hIn hIO hw0 hx hs
      have hCone : |quadratic m x| ≤ (outer*a)*δ^2*‖x‖^2 := by convert hSupp.2 using 1; ring
      have hE : 0 ≤ outer*a := mul_nonneg (hIn.trans hIO.le) ha.le
      have hSmall' : 4*B*(1*δ) ≤ 1 := by
        have hB := (norm_nonneg _).trans hI
        have h := mul_le_mul_of_nonneg_left (show 1*δ ≤ 4*δ by linarith only [hδ])
          (mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) hB)
        exact h.trans hSmall
      have hAng : projectiveWedgeSq x w ≤ (1*δ)^2 := by simpa only [one_mul] using hSupp.1
      have hBounds := scaled_cap_coordinate_bounds F hI (show (0:ℝ) ≤ 1 from zero_le_one)
        hδ hE hSmall' hw hx hAng hCone
      change let v := parabolicRescale δ (F.toFrequency.symm (mapFreq u))
        ‖x‖ ≤ 2*|v.1| ∧ |v.1| ≤ B*‖x‖ ∧ ‖v.2.2‖ ≤ Z*|v.1| ∧ |v.2.1| ≤ T*|v.1| at hBounds
      dsimp only at hBounds
      rw [show parabolicRescale δ (F.toFrequency.symm (mapFreq u)) = u from
        chartScaledFrequency_rescale F hδ.ne' u] at hBounds
      have hS := normalized_null_coordinate_lower hu hM (le_max_left _ _)
        ((le_max_left Z T).trans (le_max_right _ _)) ((le_max_right Z T).trans (le_max_right _ _))
        hBounds.2.2.1 hBounds.2.2.2
      let t₀ := activeAngularCenters t δ x
      let u₀ (z : Vec) := parabolicRescale δ (F.toFrequency.symm z)
      have hN' : t₀.card ≤ N := by
        have hC' : ((t₀.card : ℕ) : ℝ) ≤ 17^4 :=
          activeAngularCenters_card_le hδ (fun z hz => (ht hz).1) hSep hx
        dsimp only [N]
        exact_mod_cast hC'
      obtain ⟨v,hvChoice,hvSum⟩ := exists_zeroPadded_capNeighbors hN' u₀
      have hv : v ∈ boundedCapNeighbors N V (1/2) := by
        intro i
        rcases hvChoice i with h | ⟨z,hz,h⟩
        · rw [h]
          refine ⟨⟨le_rfl,zero_le_one⟩,?_,?_⟩
          · have he : ‖nullAxis‖ = 1 := by simp [nullAxis,Prod.norm_def]
            rw [he]
            exact le_max_left _ _
          · norm_num [nullAxis]
        · rw [h]
          obtain ⟨hs₁,hs₂,hScreen,hTime⟩ := activeAngularCenter_scaled_bounds F hI hδ hSmall ht hw hx hSupp.1 hz
          refine ⟨⟨zero_le_one,le_rfl⟩,?_,hs₁⟩
          exact absolute_coordinates_norm_le
            (hs₂.trans ((le_max_left _ _).trans (le_max_right _ _)))
            (hTime.trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)))
            (hScreen.trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)))
      have hReconstruct (z : Vec) (_ : z ∈ t₀) : F.toFrequency (parabolicDilation δ (u₀ z)) = z := by
        dsimp only [u₀]
        rw [parabolicDilation_rescale hδ.ne',F.toFrequency.apply_symm_apply]
      have huS : u.1 ≠ 0 := abs_pos.mp ((one_div_pos.mpr hM).trans_le hS)
      have hNear : ∀ᶠ y in 𝓝 u, y.1 ≠ 0 :=
        (isOpen_ne_fun (continuous_fst : Continuous fun y : NullFrequencyCoordinates => y.1)
          (continuous_const (y := (0:ℝ)))).mem_nhds huS
      have hLocal :=
        (capMultiplier_locally_active t m δ (a*δ^2) inner outer w x).comp_tendsto hMap.continuous.continuousAt
      have hEq : P =ᶠ[𝓝 u] parabolicBaseProfile F.toFrequency.toContinuousLinearMap a δ inner outer v := by
        filter_upwards [hNear,hLocal] with y hy hyLoc
        calc
          P y = capMultiplier t₀ m δ (a*δ^2) inner outer w (mapFreq y) := hyLoc
          _ = _ := by
            rw [show mapFreq y = F.toFrequency (parabolicDilation δ y) from rfl,
              capMultiplier_parabolic_eq F t₀ a inner outer hδ.ne' hy u₀ hReconstruct]
            unfold parabolicBaseProfile parabolicBaseAngularSum
            rw [hvSum (fun z => parabolicAngularFactor F.toFrequency.toContinuousLinearMap δ (3/4) 1 y z)]
      rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds]
      exact hJ _ (chart_mem_boundedNullCoordinateMaps F hF hI) δ ⟨hδ.le,hδone⟩ v hv u hu hS
    · have hZero := notMem_tsupport_iff_eventuallyEq.mp hs
      have hEq : P =ᶠ[𝓝 u] (fun _ => 0) := hZero.comp_tendsto hMap.continuous.continuousAt
      rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_zero_fun]
      simpa only [Pi.zero_apply,norm_zero] using hC.le
  exact fun _ hu => weighted_iteratedFDeriv_le_of_unitSphere hSmooth hDegree hOnSphere hu

end Burnett.Analysis.ProjectiveNullCaps
