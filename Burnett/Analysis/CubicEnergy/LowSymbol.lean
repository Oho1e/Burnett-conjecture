import Burnett.Analysis.CubicEnergy.HighSymbols
import Burnett.Analysis.CubicEnergy.SegmentIntegral

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Filter Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped Topology ContDiff Interval

private abbrev safe := {p : E × E | 2*‖p.1‖ < ‖p.2‖}
private theorem safe_open : IsOpen safe :=
  isOpen_lt (continuous_const.mul continuous_fst.norm) continuous_snd.norm

private def segment (z : (E × E) × ℝ) : E := z.1.2 + z.2 • z.1.1

private theorem segment_safe :
    MapsTo segment (safe ×ˢ Ioo (-2:ℝ) 2) {w | w ≠ 0} := by
  rintro ⟨⟨η,ξ⟩,t⟩ ⟨h,hT⟩
  change 2*‖η‖ < ‖ξ‖ at h
  change ξ+t • η ≠ 0
  intro bad
  have hx : ξ = -(t • η) := eq_neg_of_add_eq_zero_left bad
  have hn := congrArg norm hx
  rw [norm_neg,norm_smul,Real.norm_eq_abs] at hn
  exact (not_le_of_gt h) (hn.trans_le (mul_le_mul_of_nonneg_right (abs_lt.mpr hT).le (norm_nonneg η)))

private theorem derivative_average_smooth (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (j : Index) :
    ContDiffOn ℝ ∞ (fun p : E × E => derivComponent b j p.1 p.2) safe := by
  have ho : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
  have hs : ContDiff ℝ ∞ segment :=
    (contDiff_snd.comp contDiff_fst).add (contDiff_snd.smul (contDiff_fst.comp contDiff_fst))
  apply smooth_segment_average safe_open (fun z => (fderiv ℝ b (segment z)) (coordinateBasis j))
  exact ((hb.fderiv_of_isOpen ho (by simp)).comp hs.contDiffOn segment_safe).clm_apply contDiffOn_const

theorem lowSymbol_contDiffOn (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (j : Index) :
    ContDiffOn ℝ ∞ (fun p : E × E => lowSymbol b j p.1 p.2) {p | p ≠ 0} := by
  have ho : IsOpen {p : E × E | p ≠ 0} := isClosed_singleton.isOpen_compl
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  by_cases hs : p ∈ safe
  · exact ((lowWeight_contDiffOn p hp).contDiffAt (ho.mem_nhds hp)).mul
      (((derivative_average_smooth b hb j) p hs).contDiffAt (safe_open.mem_nhds hs))
  · have hn : ‖p.2‖ ≤ 2*‖p.1‖ := le_of_not_gt hs
    have hη : 0 < ‖p.1‖ := by
      by_contra! h
      have he := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
      rw [he,norm_zero,mul_zero] at hn
      exact hp (Prod.ext he (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))))
    have hlt : ‖p.2‖ < 4*‖p.1‖ := by linarith
    have hnbr := (isOpen_lt continuous_snd.norm (continuous_const.mul continuous_fst.norm)).mem_nhds hlt
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hnbr] with q hq
    simp [lowSymbol,lowWeight_eq_zero hq.le]

private theorem derivative_degree_zero {b : E → ℝ} (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hhom : ∀ (t : ℝ), 0<t → ∀ z, b (t • z)=t*b z) (t : ℝ) (ht : 0<t) (x v : E) :
    fderiv ℝ b (t • x) v = fderiv ℝ b x v := by
  by_cases hx : x = 0
  · simp [hx]
  have ho : IsOpen {x : E | x ≠ 0} := isClosed_singleton.isOpen_compl
  have diff (z : E) (hz : z ≠ 0) := ((hb.differentiableOn (by simp)) z hz).differentiableAt (ho.mem_nhds hz)
  let A : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  have h₁ : HasFDerivAt (b ∘ A) ((fderiv ℝ b (t • x)).comp A) x :=
    (diff _ htx).hasFDerivAt.comp x A.hasFDerivAt
  have h₂ := (diff x hx).hasFDerivAt.const_smul t
  have he : b ∘ A = fun z => t • b z := funext (hhom t ht)
  rw [he] at h₁
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (h₁.unique h₂)
  change (fderiv ℝ b (t • x)) (t • v) = t * (fderiv ℝ b x v) at hh
  rw [map_smul,smul_eq_mul] at hh
  exact mul_left_cancel₀ ht.ne' hh

theorem lowSymbol_scale {b : E → ℝ} (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hhom : ∀ (t : ℝ), 0<t → ∀ z, b (t • z)=t*b z) (j : Index) (t : ℝ) (ht : 0<t) (η ξ : E) :
    lowSymbol b j (t • η) (t • ξ) = lowSymbol b j η ξ := by
  unfold lowSymbol derivComponent
  rw [lowWeight_scale t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  change (fderiv ℝ b (t • ξ + u • t • η)) (coordinateBasis j) = _
  rw [smul_comm u t η,← smul_add,derivative_degree_zero hb hhom t ht]

end Burnett.A02.FrequencySplit
