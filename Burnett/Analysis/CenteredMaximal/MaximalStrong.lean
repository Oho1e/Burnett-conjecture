import Burnett.Analysis.CenteredMaximal.MaximalMoment

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory Filter Set Metric
open scoped ENNReal

theorem centeredMax_mono {g h : Space → ℝ≥0∞} (hle : ∀ x, g x ≤ h x) (x : Space) :
    centeredMax g x ≤ centeredMax h x := by
  apply iSup_mono
  intro r
  exact ENNReal.div_le_div_right (lintegral_mono hle) _

theorem centeredMax_iSup (f : ℕ → Space → ℝ≥0∞) (hm : ∀ n, Measurable (f n))
    (hi : Monotone f) (x : Space) :
    centeredMax (fun y => ⨆ n, f n y) x = ⨆ n, centeredMax (f n) x := by
  simp only [centeredMax,lintegral_iSup hm hi,ENNReal.iSup_div]
  exact iSup_comm

/-- All positive radii and all measurable nonnegative inputs, including
unbounded inputs, in the four-dimensional strong maximal inequality. -/
theorem centeredMax_strong_moment (g : Space → ℝ≥0∞) (hg : Measurable g) (p : ℝ) (hp : 1<p) :
    (∫⁻ x, (centeredMax g x)^p) ≤ maximalConstant p * ∫⁻ x, (g x)^p := by
  let f := fun (n : ℕ) (x : Space) => min (g x) (n : ℝ≥0∞)
  have hm (n : ℕ) : Measurable (f n) := hg.min measurable_const
  have hi : Monotone f := fun m n h x => min_le_min_left _ (by exact_mod_cast h)
  have fin (n : ℕ) (x : Space) : f n x ≠ ⊤ := ne_top_of_le_ne_top (by finiteness : (n : ℝ≥0∞) ≠ ⊤) (min_le_right _ _)
  have sup (x : Space) : (⨆ n, f n x) = g x := by
    change (⨆ n : ℕ, g x ⊓ (n : ℝ≥0∞)) = g x
    rw [← inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
  have eqM (x : Space) : (centeredMax g x)^p = ⨆ n, (centeredMax (f n) x)^p := by
    have h := centeredMax_iSup f hm hi x
    simp_rw [sup] at h
    rw [h]
    exact (ENNReal.orderIsoRpow p (by linarith)).map_iSup _
  simp_rw [eqM]
  rw [lintegral_iSup (fun n => (centeredMax_measurable (f n)).pow_const p)
    (fun i j hij x => ENNReal.rpow_le_rpow (centeredMax_mono (hi hij) x) (by linarith))]
  apply iSup_le
  intro n
  let F := fun x => (f n x).toReal
  have hreal : (fun x => ENNReal.ofReal (F x)) = f n := funext (fun x => ENNReal.ofReal_toReal (fin n x))
  have hbounded (x : Space) : F x ≤ (n : ℝ) := by
    simpa only [F,ENNReal.toReal_natCast] using ENNReal.toReal_mono (by finiteness : (n : ℝ≥0∞) ≠ ⊤) (min_le_right (g x) n)
  have h := centeredMax_moment_bounded F (hm n).ennreal_toReal (fun _ => ENNReal.toReal_nonneg) n hbounded p hp
  rw [hreal] at h
  refine h.trans (mul_le_mul_left' (lintegral_mono fun x => ?_) _)
  exact ENNReal.rpow_le_rpow ((congrFun hreal x).le.trans (min_le_left (g x) n)) (by linarith)

end Burnett.Analysis.CenteredMaximal
