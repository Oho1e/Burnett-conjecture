import Burnett.Analysis.AngularCaps.NullGridCoordinates

set_option autoImplicit false
set_option maxHeartbeats 5800000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set
open scoped BigOperators

/-- Choose only genuine null directions as representatives of the occupied
two-dimensional grid cells in each transverse affine chart. -/
theorem exists_grid_projectiveNull_cover {m : Form} (hm : Symmetric m)
    {N : ℕ} (hN : 0 < N) {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hLower : ∀ i (x : Vec), x ∈ chartBox i → quadratic m x = 0 →
      ∃ j : Index, j ≠ i ∧ a ≤ |rowValue m x j|)
    (hUpper : ∀ x : Vec, ‖x‖ ≤ 2 → ∀ j, |rowValue m x j| ≤ B) :
    ∃ c : Finset Vec,
      (↑c : Set Vec) ⊆ unitNull m ∧ c.card ≤ 32*(2*N+1)^2 ∧
      ∀ v ∈ unitNull m, ∃ w ∈ c, projectiveDist v w ≤ (4*(1+2*B/a))*(N:ℝ)⁻¹ := by
  classical
  let occupied : Finset (GridLabel N) := Finset.univ.filter (fun l => ∃ x, inNullGridCell m a l x)
  have hChoose (l : ↥occupied) : ∃ x, inNullGridCell m a l.val x := (Finset.mem_filter.mp l.property).2
  let rep (l : ↥occupied) := Classical.choose (hChoose l)
  have hRep (l : ↥occupied) : inNullGridCell m a l.val (rep l) := Classical.choose_spec (hChoose l)
  let centers := occupied.attach.image (fun l => unitRep (rep l))
  refine ⟨centers, ?_, ?_, fun v hv => ?_⟩
  · intro y hy
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx, _⟩ := hRep l
    exact unitRep_mem_unitNull (zero_lt_one.trans_le (norm_at_least_one_of_chartBox hx.1)) hx.2.1
  · calc
      centers.card ≤ occupied.attach.card := Finset.card_image_le
      _ = occupied.card := Finset.card_attach
      _ ≤ Fintype.card (GridLabel N) := Finset.card_le_univ _
      _ ≤ _ := gridLabel_card_le N
  · obtain ⟨i, x, hx, hQ, hDirection⟩ := exists_projective_chart hv
    obtain ⟨j, hji, hj⟩ := hLower i x hx hQ
    obtain ⟨σ, hσ⟩ := exists_transverseSide hj
    let p : AxisChoice := ⟨(i,j), hji⟩
    have hSector : x ∈ nullSector m p.1.1 p.1.2 σ a := ⟨hx, hQ, hσ⟩
    obtain ⟨l, hl⟩ := exists_gridLabel_of_sector N hSector
    have hlIn : l ∈ occupied := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hl⟩⟩
    let l' : ↥occupied := ⟨l, hlIn⟩
    have hIn : unitRep (rep l') ∈ centers :=
      Finset.mem_image.mpr ⟨l', Finset.mem_attach _ _, rfl⟩
    refine ⟨unitRep (rep l'), hIn, (projectiveDist_triangle v (unitRep x) _).trans ?_⟩
    rw [hDirection, zero_add]
    exact (projectiveDist_le_dist _ _).trans
      (inNullGridCell_rep_dist_le hm hN ha hB hUpper hl (hRep l'))

/-- A compact family of nondegenerate symmetric forms has one two-dimensional
covering-number constant for the true projective null directions. -/
theorem exists_compactFamily_gridNullCover {K : Set Form} (hK : IsCompact K)
    (hs : ∀ m ∈ K, Symmetric m) (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ c : Finset Vec, (↑c : Set Vec) ⊆ unitNull m ∧ (c.card : ℝ) ≤ C/δ^2 ∧
        ∀ v ∈ unitNull m, ∃ w ∈ c, projectiveDist v w ≤ δ/4 := by
  obtain ⟨a, ha, lower⟩ := exists_uniform_transverse_axis hK hND
  obtain ⟨B, hB, upper⟩ := exists_uniform_row_bound hK
  let L := 4*(1+2*B/a)
  have hL : 0 < L := mul_pos (by norm_num)
    (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (mul_nonneg zero_le_two hB.le) ha.le))
  let C := 32*(8*L+3)^2
  have hC : 0 < C := mul_pos (by norm_num)
    (pow_pos (add_pos (mul_pos (by norm_num) hL) (by norm_num)) _)
  refine ⟨C, hC, fun m hm δ hδ hδone => ?_⟩
  let N := Nat.ceil (4*L/δ)
  have hQuot : 0 < 4*L/δ := div_pos (mul_pos (by norm_num) hL) hδ
  have hLow : 4*L/δ ≤ (N:ℝ) := Nat.le_ceil _
  have hN' : (0:ℝ) < N := hQuot.trans_le hLow
  have hN : 0 < N := Nat.cast_pos.mp hN'
  obtain ⟨c, hc, hCard, hCover⟩ := exists_grid_projectiveNull_cover (hs m hm) hN ha hB.le (lower m hm) (upper m hm)
  refine ⟨c,hc,?_,fun v hv => ?_⟩
  · have hHigh : (N:ℝ) < 4*L/δ+1 := Nat.ceil_lt_add_one hQuot.le
    have hTerm : 2*(N:ℝ)+1 ≤ (8*L+3)/δ := by
      calc
        _ ≤ 8*L/δ+3 := by
          rw [mul_div_assoc] at hHigh ⊢
          linarith only [hHigh]
        _ ≤ _ := by
          rw [add_div]
          exact add_le_add_left ((le_div_iff₀ hδ).mpr
            (mul_le_of_le_one_right (by norm_num) hδone)) _
    have hCasts : (c.card : ℝ) ≤ 32*(2*(N:ℝ)+1)^2 := by exact_mod_cast hCard
    calc
      _ ≤ 32*(2*(N:ℝ)+1)^2 := hCasts
      _ ≤ 32*((8*L+3)/δ)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hTerm 2) (by norm_num)
      _ = _ := by rw [div_pow]; exact (mul_div_assoc _ _ _).symm
  · obtain ⟨w, hw, hwNear⟩ := hCover v hv
    refine ⟨w, hw, hwNear.trans ?_⟩
    have hMul : 4*L ≤ (N:ℝ)*δ := (div_le_iff₀ hδ).mp hLow
    change L*(N:ℝ)⁻¹ ≤ δ/4
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hN').mpr
    calc
      _ ≤ δ*(N:ℝ)/4 := (le_div_iff₀ (show (0:ℝ) < 4 by norm_num)).mpr (by nlinarith only [hMul])
      _ = _ := by ring

end Burnett.Analysis.ProjectiveNullCaps
