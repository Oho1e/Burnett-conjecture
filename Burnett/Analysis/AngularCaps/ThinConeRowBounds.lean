import Burnett.Analysis.AngularCaps.UniformNullCharts
import Burnett.Analysis.AngularCaps.LorentzNullLines

set_option autoImplicit false
set_option maxHeartbeats 4300000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Finset Metric
open scoped BigOperators

private def unitRowSize (z : Form × Vec) : ℝ := ∑ j : Index, |rowValue z.1 z.2 j|

private theorem continuous_rowValue_of_pair (j : Index) :
    Continuous fun z : Form × Vec => rowValue z.1 z.2 j := by
  unfold rowValue
  apply continuous_finset_sum
  intro i _
  have hi : Continuous fun z : Form × Vec => z.1 i := (continuous_apply i).comp continuous_fst
  exact ((continuous_apply j).comp hi).mul
    ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) i).comp continuous_snd)

private theorem unitRowSize_pos {m : Form} (hND : Nondegenerate m)
    {x : Vec} (hx : ‖x‖ = 1) : 0 < unitRowSize (m,x) := by
  by_contra! hn
  have hZero (j : Index) : rowValue m x j = 0 := by
    apply abs_nonpos_iff.mp
    exact (Finset.single_le_sum (fun k _ => abs_nonneg (rowValue m x k)) (Finset.mem_univ j)).trans hn
  have hh : x = 0 := hND x hZero
  simp [hh] at hx

/-- One common positive transverse component of the quadratic derivative is
available at every unit direction in a fixed compact nondegenerate family. -/
theorem exists_uniform_unit_rowLower {K : Set Form} (hK : IsCompact K)
    (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ a : ℝ, 0 < a ∧ ∀ m ∈ K, ∀ x : Vec, ‖x‖ = 1 → ∃ j : Index, a ≤ |rowValue m x j| := by
  let S := K ×ˢ sphere (0 : Vec) 1
  by_cases hS : S.Nonempty
  · have hComp : IsCompact S := hK.prod (isCompact_sphere _ _)
    have hCont : Continuous unitRowSize := continuous_finset_sum _ fun j _ => (continuous_rowValue_of_pair j).abs
    obtain ⟨z,hz,hMin⟩ := hComp.exists_isMinOn hS hCont.continuousOn
    have hPos := unitRowSize_pos (hND z.1 hz.1)
      (show ‖z.2‖ = 1 by simpa only [mem_sphere,dist_zero_right] using hz.2)
    refine ⟨unitRowSize z/4,div_pos hPos (by norm_num),?_⟩
    intro m hm x hx
    have hMem : (m,x) ∈ S := ⟨hm,by simpa only [mem_sphere,dist_zero_right] using hx⟩
    obtain ⟨j,_,hMax⟩ := Finset.exists_max_image
      (Finset.univ : Finset Index) (fun j => |rowValue m x j|) Finset.univ_nonempty
    have hSmall : unitRowSize (m,x) ≤ 4*|rowValue m x j| := by
      unfold unitRowSize
      calc
        _ ≤ ∑ _ : Index, |rowValue m x j| := Finset.sum_le_sum hMax
        _ = _ := by simp
    have hBound := ((isMinOn_iff.mp hMin) (m,x) hMem).trans hSmall
    exact ⟨j,(div_le_iff₀ (show (0:ℝ) < 4 by norm_num)).mpr (by linarith only [hBound])⟩
  · refine ⟨1,zero_lt_one,fun m hm x hx => ?_⟩
    have hMem : (m,x) ∈ S := ⟨hm,by simpa only [mem_sphere,dist_zero_right] using hx⟩
    exact (hS ⟨(m,x),hMem⟩).elim

def unitAxis (j : Index) : Vec := EuclideanSpace.single j (1 : ℝ)

@[simp] theorem norm_unitAxis (j : Index) : ‖unitAxis j‖ = 1 := by simp [unitAxis]

theorem pairing_unitAxis_right (m : Form) (x : Vec) (j : Index) :
    pairing m x (unitAxis j) = rowValue m x j := by
  unfold pairing
  rw [Finset.sum_eq_single j]
  · simp [unitAxis]
  · intro i _ hij
    simp [unitAxis,hij]
  · exact fun h => (h (Finset.mem_univ j)).elim

theorem exists_uniform_unitAxis_quadratic_upper {K : Set Form} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m ∈ K, ∀ j : Index, |quadratic m (unitAxis j)| ≤ B := by
  obtain ⟨B,hB,hBound⟩ := exists_uniform_row_bound hK
  refine ⟨B,hB,fun m hm j => ?_⟩
  rw [quadratic,pairing_unitAxis_right]
  exact hBound m hm (unitAxis j) (by simp) j

theorem continuous_quadratic_fixed (m : Form) : Continuous (quadratic m) := by
  unfold quadratic pairing
  apply continuous_finset_sum
  intro j _
  exact ((continuous_rowValue_of_pair j).comp (continuous_const.prodMk continuous_id)).mul
    (PiLp.continuous_apply 2 (fun _ : Index => ℝ) j)

end Burnett.Analysis.ProjectiveNullCaps
