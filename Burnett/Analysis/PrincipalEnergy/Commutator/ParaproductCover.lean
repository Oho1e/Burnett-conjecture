import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletDyadicSquare
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators

private theorem ball_four_volume (c : Space) (r : ℝ) (hr : 0≤r) :
    volume (ball c (4*r)) = 256 * volume (ball c r) := by
  rw [← Measure.addHaar_closedBall_eq_addHaar_ball volume c (4*r),
    ← Measure.addHaar_closedBall_eq_addHaar_ball volume c r,
    Measure.addHaar_closedBall_mul volume c (by norm_num : (0:ℝ)≤4) hr,
    Measure.addHaar_closedBall_center volume c]
  norm_num [finrank_euclideanSpace_fin]

/-- The Carleson mass above a threshold is controlled by one spatial
superlevel set. The covering keeps the vertical scale of every original point. -/
theorem finite_ball_carleson_level_le (J : Finset ℕ) (s : ℕ → ℝ) (t : ℝ)
    (hs : ∀ j ∈ J, 0<s j ∧ s j≤t) (ν : ℕ → Measure Space) (C : ℝ≥0∞)
    (hPack : ∀ (c : Space) (R : ℝ), 0<R →
      (∑ j ∈ J.filter (fun j => s j≤R), ν j (ball c R)) ≤ C * volume (ball c R))
    (F : ℕ → Space → ℝ) (M : Space → ℝ)
    (hDom : ∀ j ∈ J, ∀ x y, y ∈ ball x (s j) → F j x ≤ M y) (level : ℝ) :
    (∑ j ∈ J, ν j {x | level < F j x}) ≤ (256*C) * volume {x | level < M x} := by
  classical
  let T : Set (Space × ℕ) := {p | p.2 ∈ J ∧ level < F p.2 p.1}
  let r (p : Space × ℕ) : ℝ := s p.2
  let B (p : Space × ℕ) := ball p.1 (r p)
  obtain ⟨u,hUT,hDisj,hCover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement B T r 2
    (by norm_num) (fun p hp => (hs p.2 hp.1).1.le) t (fun p hp => (hs p.2 hp.1).2)
    (fun p hp => ⟨p.1,mem_ball_self (hs p.2 hp.1).1⟩)
  have hPos (p : u) : 0 < r p := (hs p.1.2 (hUT p.2).1).1
  have hu : u.Countable := hDisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun p hp => ⟨p.1,mem_ball_self (hPos ⟨p,hp⟩)⟩)
  letI : Countable u := hu.to_subtype
  let V (j : ℕ) (p : u) : Set Space := if s j≤4*r p then ball p.1.1 (4*r p) else ∅
  have coverLevel (j : ℕ) (hj : j ∈ J) : {x | level < F j x} ⊆ ⋃ p : u, V j p := by
    intro x hx
    obtain ⟨p,hp,⟨z,hzx,hzp⟩,hScale⟩ := hCover (x,j) ⟨hj,hx⟩
    let q : u := ⟨p,hp⟩
    have hS : s j ≤ 4*r q := by
      change s j ≤ 2*r q at hScale
      linarith [hPos q]
    have hD : dist x q.1.1 < 4*r q := by
      have h1 : dist x z < s j := by simpa only [dist_comm] using mem_ball.mp hzx
      have h2 : dist z q.1.1 < r q := mem_ball.mp hzp
      linarith [dist_triangle x z q.1.1]
    refine mem_iUnion.mpr ⟨q,?_⟩
    change x ∈ if s j≤4*r q then ball q.1.1 (4*r q) else ∅
    rw [if_pos hS]
    exact mem_ball.mpr hD
  have hSum (p : u) : (∑ j ∈ J, ν j (V j p)) ≤ C * volume (ball p.1.1 (4*r p)) := by
    -- The zero entries are precisely the scales taller than this enlarged ball.
    have hEq : (∑ j ∈ J, ν j (V j p)) =
        ∑ j ∈ J.filter (fun j => s j≤4*r p), ν j (ball p.1.1 (4*r p)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : s j≤4*r p <;> simp [V,h]
    rw [hEq]
    exact hPack p.1.1 _ (by linarith [hPos p])
  have hSpatial : ⋃ p ∈ u, B p ⊆ {x | level < M x} := by
    intro x hx
    obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp hx
    exact (hUT hp).2.trans_le (hDom p.2 (hUT hp).1 p.1 x hx)
  calc
    _ ≤ ∑ j ∈ J, ∑' p : u, ν j (V j p) := Finset.sum_le_sum fun j hj =>
      (measure_mono (coverLevel j hj)).trans (measure_iUnion_le _)
    _ = ∑' p : u, ∑ j ∈ J, ν j (V j p) := by
      calc
        _ = ∑' j : J, ∑' p : u, ν j (V j p) := (J.tsum_subtype _).symm
        _ = ∑' p : u, ∑' j : J, ν j (V j p) := ENNReal.tsum_comm
        _ = _ := tsum_congr fun p => J.tsum_subtype (fun j : ℕ => ν j (V j p))
    _ ≤ ∑' p : u, C * volume (ball p.1.1 (4*r p)) := ENNReal.tsum_le_tsum hSum
    _ = (256*C) * ∑' p : u, volume (B p) := by
      simp_rw [fun p : u => ball_four_volume p.1.1 (r p) (hPos p).le,
        ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ _ := by
      rw [← measure_biUnion hu hDisj (fun _ _ => measurableSet_ball)]
      exact mul_le_mul_left' (measure_mono hSpatial) _

private theorem square_distribution (μ : Measure Space) (F : Space → ℝ)
    (hF : Measurable F) (hNonneg : ∀ x, 0≤F x) :
    (∫⁻ x, ENNReal.ofReal ((F x)^2) ∂μ) =
      ∫⁻ level in Ioi (0:ℝ), μ {x | level < F x} * ENNReal.ofReal (2*level) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (g := fun a : ℝ => 2*a) μ
    (Eventually.of_forall hNonneg) hF.aemeasurable
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
        exact mul_nonneg (by norm_num) (le_of_lt ht))
  have hPrimitive (a : ℝ) : (∫ t in (0:ℝ)..a, 2*t) = a^2 := by
    rw [intervalIntegral.integral_const_mul,integral_id]
    ring
  simpa only [hPrimitive] using h

/-- Finite Carleson embedding over actual spatial balls and all bounded
positive scale selections, with a spatial majorant throughout each ball. -/
theorem finite_ball_carleson_square_le (J : Finset ℕ) (s : ℕ → ℝ) (t : ℝ)
    (hs : ∀ j ∈ J, 0<s j ∧ s j≤t) (ν : ℕ → Measure Space) (C : ℝ≥0∞) (hC : C≠⊤)
    (hPack : ∀ (c : Space) (R : ℝ), 0<R →
      (∑ j ∈ J.filter (fun j => s j≤R), ν j (ball c R)) ≤ C * volume (ball c R))
    (F : ℕ → Space → ℝ) (hF : ∀ j, Measurable (F j)) (hN : ∀ j x, 0≤F j x)
    (M : Space → ℝ) (hM : Measurable M) (hMN : ∀ x, 0≤M x)
    (hDom : ∀ j ∈ J, ∀ x y, y ∈ ball x (s j) → F j x ≤ M y) :
    (∑ j ∈ J, ∫⁻ x, ENNReal.ofReal ((F j x)^2) ∂ν j) ≤
      (256*C) * ∫⁻ x, ENNReal.ofReal ((M x)^2) := by
  simp_rw [fun j => square_distribution (ν j) (F j) (hF j) (hN j)]
  rw [square_distribution volume M hM hMN, ← lintegral_finset_sum]
  · calc
      _ ≤ ∫⁻ level in Ioi (0:ℝ), ((256*C)*volume {x | level < M x})*ENNReal.ofReal (2*level) := by
        apply lintegral_mono
        intro level
        change (∑ j ∈ J, ν j {x | level < F j x} * ENNReal.ofReal (2*level)) ≤
          ((256*C)*volume {x | level < M x})*ENNReal.ofReal (2*level)
        rw [← Finset.sum_mul]
        exact mul_le_mul_right' (finite_ball_carleson_level_le J s t hs ν C hPack F M hDom level) _
      _ = _ := by
        simpa only [mul_assoc] using lintegral_const_mul'
          (μ := (volume : Measure ℝ).restrict (Ioi 0)) (256*C)
          (fun level => volume {x | level < M x} * ENNReal.ofReal (2*level))
          (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC)
  · intro j _
    have hLevel : Antitone (fun level : ℝ => ν j {x | level < F j x}) := fun a b hab =>
      measure_mono (fun _ hx => hab.trans_lt hx)
    exact hLevel.measurable.mul ((measurable_const.mul measurable_id).ennreal_ofReal)

end Burnett.Analysis.CarlesonEmbedding
