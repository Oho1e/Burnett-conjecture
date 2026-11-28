import Burnett.Analysis.AngularCaps.ActualBaseCapJets

set_option autoImplicit false
set_option maxHeartbeats 13000000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.Analysis.ProjectiveNullCaps

open private absolute_coordinates_norm_le from Burnett.Analysis.AngularCaps.ActualBaseCapJets

/-- A single bounded list of actual angular neighbors works on the entire
normalized profile of one base cap, including the low-ratio trace. -/
theorem exists_wardBaseCapProfile_exact {m : Form} {w : Vec} (F : NullCapChart m w)
    (t : Finset Vec) (ht : (↑t : Set Vec) ⊆ unitNull m)
    (B tube inner outer δ : ℝ) (hB : 0 < B)
    (hI : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B)
    (hw : ‖w‖ = 1) (hδ : 0 < δ) (hSmall : 4*B*(4*δ) ≤ 1)
    (hSep : (↑t : Set Vec).Pairwise (fun x y => δ/4 < projectiveDist x y)) :
    let N : ℕ := 33^4
    let M := max 1 (max B (max (16*B^2) ((16*B)^2*B)))
    ∃ v : CapNeighborParameters N, v ∈ boundedCapNeighbors N M (1/2) ∧
      ∀ u : NullFrequencyCoordinates, u.1 ≠ 0 →
        capMultiplier t m δ (tube*δ^2) inner outer w (chartScaledFrequency F δ u) =
          parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ inner outer v u := by
  classical
  intro N M
  let A (u : NullFrequencyCoordinates) := chartScaledFrequency F δ u
  let C := centersMeeting t w (4*δ)
  let U (z : Vec) := parabolicRescale δ (F.toFrequency.symm z)
  have hSub : C ⊆ t := Finset.filter_subset _ _
  have unit (z : Vec) (hz : z ∈ t) : ‖z‖ = 1 := (ht hz).1
  have ne (z : Vec) (hz : ‖z‖ = 1) : z ≠ 0 := by
    intro he
    simp only [he,norm_zero,zero_ne_one] at hz
  have repr (z : Vec) (hz : ‖z‖ = 1) : unitRep z = z := by simp [unitRep,hz]
  have sep : (↑t : Set Vec).Pairwise (fun x y => (δ/2)/2 < projectiveDist x y) := by
    intro x hx y hy hne
    have h := hSep hx hy hne
    linarith only [h]
  have hCard : C.card ≤ N := by
    have h := projectiveCaps_bounded_overlap (half_pos hδ) sep 8 (by norm_num) w
    have he : 8*(δ/2) = 4*δ := by ring
    rw [he] at h
    have h' : (C.card : ℝ) ≤ (33:ℝ)^4 := by
      simpa only [C,show (4:ℝ)*8+1 = 33 by norm_num] using h
    exact_mod_cast h'
  obtain ⟨v,hvPick,hvSum⟩ := exists_zeroPadded_capNeighbors hCard U
  have hb (z : Vec) (hz : z ∈ C) :
      1/2 ≤ |(U z).1| ∧ |(U z).1| ≤ B ∧ ‖(U z).2.2‖ ≤ 16*B^2 ∧
        |(U z).2.1| ≤ (16*B)^2*B := by
    have hzDist : projectiveDist z w ≤ 4*δ := by
      rw [projectiveDist_comm z w]
      exact (Finset.mem_filter.mp hz).2
    have hzUnit := unit z (hSub hz)
    have hz0 := ne z hzUnit
    have hW := (projectiveWedgeSq_compare_unitRep_dist hz0 (ne w hw)).2
    rw [repr z hzUnit, repr w hw] at hW
    have hA : projectiveWedgeSq z w ≤ (4*δ)^2 :=
      hW.trans (pow_le_pow_left₀ (projectiveDist_nonneg _ _) hzDist 2)
    have hQ : |quadratic m z| ≤ (0:ℝ)*δ^2*‖z‖^2 := by simp [(ht (hSub hz)).2]
    obtain ⟨hs,hs',hzV,htV⟩ := scaled_cap_coordinate_bounds F hI (by norm_num : (0:ℝ) ≤ 4)
      hδ (le_refl (0:ℝ)) hSmall hw hz0 hA hQ
    rw [hzUnit] at hs
    change 1 ≤ 2*|(U z).1| at hs
    have hsB : |(U z).1| ≤ B := by simpa only [U,hzUnit,mul_one] using hs'
    have hz' : ‖(U z).2.2‖ ≤ (16*B)*|(U z).1| := by
      convert hzV using 1
      ring
    have ht' : |(U z).2.1| ≤ (16*B)^2*|(U z).1| := by
      convert htV using 1
      ring
    refine ⟨by linarith only [hs],hsB,hz'.trans ?_,ht'.trans ?_⟩
    · exact (mul_le_mul_of_nonneg_left hsB (by positivity)).trans_eq (by ring)
    · exact mul_le_mul_of_nonneg_left hsB (sq_nonneg _)
  have hv : v ∈ boundedCapNeighbors N M (1/2) := by
    intro i
    rcases hvPick i with h | ⟨z,hz,h⟩
    · rw [h]
      refine ⟨⟨le_rfl,zero_le_one⟩,?_,by norm_num [nullAxis]⟩
      have e : ‖nullAxis‖ = 1 := by simp [nullAxis,Prod.norm_def]
      rw [e]
      exact le_max_left _ _
    · rw [h]
      obtain ⟨hs₁,hs₂,hzT,htT⟩ := hb z hz
      refine ⟨⟨zero_le_one,le_rfl⟩,?_,hs₁⟩
      exact absolute_coordinates_norm_le
        (hs₂.trans ((le_max_left _ _).trans (le_max_right _ _)))
        (htT.trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)))
        (hzT.trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)))
  refine ⟨v,hv,?_⟩
  intro u hu
  let x := A u
  have hx : x ≠ 0 := chartScaledFrequency_ne_zero F hδ.ne' (fun he => hu (congrArg Prod.fst he))
  have hw₀ := ne w hw
  have isNeighbor (z : Vec) (hz : z ∈ t)
      (hX : capAngularProfile δ (3/4) 1 w x ≠ 0)
      (hZ : capAngularProfile δ (3/4) 1 z x ≠ 0) : z ∈ C := by
    have hWedge (v : Vec) (h : capAngularProfile δ (3/4) 1 v x ≠ 0) :
        projectiveWedgeSq x v ≤ δ^2 := by
      simpa only [one_mul] using
        (capAngularProfile_nonzero_angle hδ (by norm_num : (0:ℝ) ≤ 3/4)
          (by norm_num : (3/4:ℝ) < 1) h).le
    have hXDist := projectiveDist_unitRep_le_of_wedgeSq_le hx hw₀ hδ.le (hWedge w hX)
    have hZDist := projectiveDist_unitRep_le_of_wedgeSq_le hx (ne z (unit z hz)) hδ.le (hWedge z hZ)
    rw [repr w hw] at hXDist
    rw [repr z (unit z hz), projectiveDist_comm] at hZDist
    have hTri := projectiveDist_triangle z (unitRep x) w
    refine Finset.mem_filter.mpr ⟨hz,?_⟩
    rw [projectiveDist_comm w z]
    linarith only [hXDist,hZDist,hTri]
  have hExact : capMultiplier t m δ (tube*δ^2) inner outer w x =
      capMultiplier C m δ (tube*δ^2) inner outer w x := by
    by_cases hX : capAngularProfile δ (3/4) 1 w x = 0
    · rw [capMultiplier_at_nonzero _ _ _ _ _ _ _ hx, capMultiplier_at_nonzero _ _ _ _ _ _ _ hx]
      simp only [hX,zero_div,mul_zero]
    · have hMass : capAngularMass C δ x = capAngularMass t δ x := by
        unfold capAngularMass
        refine Finset.sum_subset hSub fun z hz hzC => ?_
        exact Classical.byContradiction fun hZ => hzC (isNeighbor z hz hX hZ)
      rw [capMultiplier_at_nonzero _ _ _ _ _ _ _ hx, capMultiplier_at_nonzero _ _ _ _ _ _ _ hx,
        capDenominator,capDenominator,hMass]
  have hBack (z : Vec) (_ : z ∈ C) : F.toFrequency (parabolicDilation δ (U z)) = z := by
    dsimp only [U]
    rw [parabolicDilation_rescale hδ.ne',F.toFrequency.apply_symm_apply]
  calc
    _ = capMultiplier C m δ (tube*δ^2) inner outer w x := hExact
    _ = _ := by
      change capMultiplier C m δ (tube*δ^2) inner outer w (F.toFrequency (parabolicDilation δ u)) = _
      rw [capMultiplier_parabolic_eq F C tube inner outer hδ.ne' hu U hBack]
      unfold parabolicBaseProfile parabolicBaseAngularSum
      rw [hvSum (fun z => parabolicAngularFactor F.toFrequency.toContinuousLinearMap δ (3/4) 1 u z)]

end Burnett.C02
