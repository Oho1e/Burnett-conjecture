import Burnett.Geometry.MaximalChart.MetricCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Quantitative geometry for any fixed compatible smooth chart transition.
The localized Fourier kernel uses its actual determinant half-density. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Set MeasureTheory Filter Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.MaximalChart (AtlasChart chartTransition_fderiv_leftInverse chartDerivative_det_ne_zero)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Jacobian with respect to Lebesgue half-densities in the actual charts. -/
def jacobianWeight (c d : AtlasChart M) (x : CoordinateSpace) : ℝ :=
  Real.sqrt |(fderiv ℝ (c.transition d) x).det|

theorem chartTransition_fderiv_uniform_lower (c d : AtlasChart M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKs : K ⊆ (c.transition d).source) :
    ∃ q : ℝ, 0 < q ∧ ∀ x ∈ K, ∀ v : CoordinateSpace,
      q * ‖v‖ ≤ ‖(fderiv ℝ (c.transition d) x) v‖ := by
  let e := c.transition d
  let f := d.transition c
  have hsymm : e.symm = f := by
    simp only [e, f, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hm : MapsTo e e.source f.source := by
    rw [← hsymm]
    exact e.mapsTo
  have hs : ContDiffOn ℝ 0 (fderiv ℝ f) f.source :=
    (d.smooth_transition c).fderiv_of_isOpen f.open_source (by simp)
  have hd := hs.continuousOn
  have hC : ContinuousOn (fun x => ‖fderiv ℝ f (e x)‖) K :=
    ((hd.comp e.continuousOn hm).mono hKs).norm
  obtain ⟨C, hC⟩ := hK.bddAbove_image hC
  let D := max C 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1 / D, div_pos one_pos hD, ?_⟩
  intro x hx v
  have hnorm : ‖fderiv ℝ f (e x)‖ ≤ D := by
    have h : ‖fderiv ℝ f (e x)‖ ≤ C := hC (mem_image_of_mem _ hx)
    exact h.trans (by dsimp [D]; linarith [le_max_left C 0])
  have hinv : (fderiv ℝ f (e x)) ((fderiv ℝ e x) v) = v :=
    congrArg (fun A : CoordinateSpace →L[ℝ] CoordinateSpace => A v)
      (chartTransition_fderiv_leftInverse c d (hKs hx))
  have htarget : ‖v‖ ≤ D * ‖(fderiv ℝ e x) v‖ :=
    calc
      ‖v‖ = ‖(fderiv ℝ f (e x)) ((fderiv ℝ e x) v)‖ := congrArg norm hinv.symm
      _ ≤ ‖fderiv ℝ f (e x)‖ * ‖(fderiv ℝ e x) v‖ := (fderiv ℝ f (e x)).le_opNorm _
      _ ≤ D * ‖(fderiv ℝ e x) v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ hD).2 (by simpa only [mul_comm] using htarget)

def chartDerivativeEquiv (c d : AtlasChart M) (x : CoordinateSpace) (hx : x ∈ (c.transition d).source) : CoordinateSpace ≃L[ℝ] CoordinateSpace :=
  (fderiv ℝ (c.transition d) x).toContinuousLinearEquivOfDetNeZero
    (chartDerivative_det_ne_zero c d x hx)

private theorem smooth_continuousLinearMap_det :
    ContDiff ℝ ∞ (fun A : CoordinateSpace →L[ℝ] CoordinateSpace => A.det) := by
  let b := (stdOrthonormalBasis ℝ CoordinateSpace).toBasis
  have hEq (A : CoordinateSpace →L[ℝ] CoordinateSpace) : A.det = Matrix.det (LinearMap.toMatrix b b A.toLinearMap) :=
    (LinearMap.det_toMatrix b A.toLinearMap).symm
  simp_rw [hEq, Matrix.det_apply', LinearMap.toMatrix_apply]
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  change ContDiff ℝ ∞ (fun A : CoordinateSpace →L[ℝ] CoordinateSpace => b.coord (σ i) (A (b i)))
  exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.comp
    (ContinuousLinearMap.apply ℝ CoordinateSpace (b i)).contDiff)

theorem jacobianWeight_contDiffOn (c d : AtlasChart M) :
    ContDiffOn ℝ ∞ (jacobianWeight c d) (c.transition d).source := by
  let e := c.transition d
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (c.smooth_transition d).fderiv_of_isOpen e.open_source (by simp)
  have hdet : ContDiffOn ℝ ∞ (fun x : CoordinateSpace => (fderiv ℝ e x).det) e.source :=
    smooth_continuousLinearMap_det.comp_contDiffOn hD
  have hne (x : CoordinateSpace) (hx : x ∈ e.source) := chartDerivative_det_ne_zero c d x hx
  exact (hdet.abs hne).sqrt fun x hx => abs_ne_zero.mpr (hne x hx)

def overlapTransition (c d : AtlasChart M) : CoordinateSpace → CoordinateSpace := by
  classical
  let e := c.transition d
  exact e.source.piecewise e (fun _ => 0)

theorem overlapTransition_eq (c d : AtlasChart M) {x : CoordinateSpace}
    (hx : x ∈ (c.transition d).source) :
    overlapTransition c d x = c.transition d x := by
  classical
  simp [overlapTransition, hx]

theorem overlapTransition_measurable (c d : AtlasChart M) : Measurable (overlapTransition c d) := by
  classical
  let e := c.transition d
  exact e.continuousOn.measurable_piecewise continuousOn_const e.open_source.measurableSet

theorem overlapTransition_fderiv (c d : AtlasChart M) {x : CoordinateSpace}
    (hx : x ∈ (c.transition d).source) :
    fderiv ℝ (overlapTransition c d) x = fderiv ℝ (c.transition d) x := by
  have he : overlapTransition c d =ᶠ[𝓝 x] (c.transition d) := by
    filter_upwards [(c.transition d).open_source.mem_nhds hx] with y hy
    exact overlapTransition_eq c d hy
  exact he.fderiv_eq

theorem overlapTransition_contDiffOn (c d : AtlasChart M) :
    ContDiffOn ℝ ∞ (overlapTransition c d) (c.transition d).source :=
  (c.smooth_transition d).congr (fun _ hx => overlapTransition_eq c d hx)

def overlapJacobianWeight (c d : AtlasChart M) (x : CoordinateSpace) : ℝ :=
  Real.sqrt |(fderiv ℝ (overlapTransition c d) x).det|

theorem overlapJacobianWeight_eq (c d : AtlasChart M) {x : CoordinateSpace}
    (hx : x ∈ (c.transition d).source) :
    overlapJacobianWeight c d x = Real.sqrt |(fderiv ℝ (c.transition d) x).det| := by
  rw [overlapJacobianWeight, overlapTransition_fderiv c d hx]

theorem overlapJacobianWeight_measurable (c d : AtlasChart M) : Measurable (overlapJacobianWeight c d) := by
  have hd : Measurable (fun x => (fderiv ℝ (overlapTransition c d) x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (overlapTransition c d))
  exact (Real.continuous_sqrt.comp continuous_abs).measurable.comp hd

theorem overlapJacobianWeight_contDiffOn (c d : AtlasChart M) :
    ContDiffOn ℝ ∞ (overlapJacobianWeight c d) (c.transition d).source :=
  (jacobianWeight_contDiffOn c d).congr (fun _ hx => overlapJacobianWeight_eq c d hx)

private theorem exists_compact_convex_derivative_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {f : E → F} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hConv : Convex ℝ K) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  have hf' : ContDiffOn ℝ 0 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hf'.continuousOn.mono hKU).norm
  have hBound (x : E) (hx : x ∈ K) : ‖fderiv ℝ f x‖ ≤ max B 0 :=
    le_trans (hB (mem_image_of_mem _ hx)) (le_max_left _ _)
  have hDiff (x : E) (hx : x ∈ K) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp)
  exact ⟨max B 0, le_max_right _ _, fun x hx y hy =>
    hConv.norm_image_sub_le_of_norm_fderiv_le hDiff hBound hx hy⟩

theorem overlapKernel_geometry_bounds (c d : AtlasChart M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    ∃ q L W H δ₀ : ℝ, 0 < q ∧ 0 ≤ L ∧ 0 ≤ W ∧ 0 ≤ H ∧ 0 < δ₀ ∧
      (∀ δ, 0 ≤ δ → δ ≤ δ₀ → L * δ ≤ q / 2) ∧
      (∀ x ∈ K, DifferentiableAt ℝ Φ x) ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ Φ y - fderiv ℝ Φ x‖ ≤ L * ‖y - x‖) ∧
      (∀ x ∈ K, ∀ v, q * ‖v‖ ≤ ‖fderiv ℝ Φ x v‖) ∧
      (∀ x ∈ K, ‖w x‖ ≤ W) ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖w y - w x‖ ≤ H * ‖x - y‖) := by
  intro Φ w
  let U := (c.transition d).source
  have hU : IsOpen U := (c.transition d).open_source
  have hf : ContDiffOn ℝ ∞ Φ U := overlapTransition_contDiffOn c d
  have hf' : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U := hf.fderiv_of_isOpen hU (by simp)
  have hw : ContDiffOn ℝ ∞ w U := overlapJacobianWeight_contDiffOn c d
  obtain ⟨L, hL, hDf⟩ := exists_compact_convex_derivative_bound hU hK hKU hConv hf'
  obtain ⟨H, hH, hDw⟩ := exists_compact_convex_derivative_bound hU hK hKU hConv hw
  obtain ⟨W, hW⟩ := hK.bddAbove_image (hw.continuousOn.mono hKU).norm
  obtain ⟨q, hq, hLow⟩ := chartTransition_fderiv_uniform_lower c d K hK hKU
  let δ₀ := q / (2 * (L + 1))
  have hp : 0 < L + 1 := by linarith
  have hδ₀ : 0 < δ₀ := div_pos hq (mul_pos (by norm_num) hp)
  refine ⟨q, L, max W 0, H, δ₀, hq, hL, le_max_right _ _, hH, hδ₀, ?_, ?_, hDf, ?_, ?_, ?_⟩
  · intro δ hδ hsmall
    calc
      L * δ ≤ (L + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
      _ ≤ (L + 1) * δ₀ := mul_le_mul_of_nonneg_left hsmall hp.le
      _ = q / 2 := by dsimp [δ₀]; field_simp
  · intro x hx
    exact (hf.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp)
  · intro x hx v
    change q * ‖v‖ ≤ ‖fderiv ℝ (overlapTransition c d) x v‖
    rw [overlapTransition_fderiv c d (hKU hx)]
    exact hLow x hx v
  · exact fun x hx => le_trans (hW (mem_image_of_mem _ hx)) (le_max_left _ _)
  · intro x hx y hy
    rw [norm_sub_rev x y]
    exact hDw x hx y hy

private theorem compact_separated_image_lower {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {K : Set E} {f : E → F}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hi : InjOn f K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, ∀ y ∈ K, δ ≤ ‖x - y‖ → b ≤ ‖f x - f y‖ := by
  let S := (K ×ˢ K) ∩ {p : E × E | δ ≤ ‖p.1 - p.2‖}
  have hSep : IsClosed {p : E × E | δ ≤ ‖p.1 - p.2‖} :=
    isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm
  have hS : IsCompact S := (hK.prod hK).inter_right hSep
  have hFst := hf.comp continuous_fst.continuousOn (show MapsTo Prod.fst S K from fun _ hp => hp.1.1)
  have hSnd := hf.comp continuous_snd.continuousOn (show MapsTo Prod.snd S K from fun _ hp => hp.1.2)
  have hcont : ContinuousOn (fun p : E × E => ‖f p.1 - f p.2‖) S := (hFst.sub hSnd).norm
  have hpos (p : E × E) (hp : p ∈ S) : 0 < ‖f p.1 - f p.2‖ := by
    have hxy : p.1 ≠ p.2 := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hp.2))
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (hi hp.1.1 hp.1.2 h)))
  obtain ⟨a, ha, hab⟩ := hS.exists_forall_le' hcont hpos
  exact ⟨a, ha, fun x hx y hy h => hab (x, y) ⟨⟨hx, hy⟩, h⟩⟩

theorem overlapFar_uniform_arguments (c d : AtlasChart M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source) {δ : ℝ} (hδ : 0 < δ) :
    let Φ := overlapTransition c d
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, ∀ y ∈ K, δ ≤ ‖x - y‖ →
      a ≤ ‖Φ x - Φ y‖ ∧ a ≤ ‖fderiv ℝ Φ x (x - y)‖ := by
  intro Φ
  have hc : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hi : InjOn Φ K := by
    intro x hx y hy he
    change overlapTransition c d x = overlapTransition c d y at he
    rw [overlapTransition_eq c d (hKU hx), overlapTransition_eq c d (hKU hy)] at he
    exact (c.transition d).injOn (hKU hx) (hKU hy) he
  obtain ⟨b, hb, hbound⟩ := compact_separated_image_lower hK hc hi hδ
  obtain ⟨q, hq, hqbound⟩ := chartTransition_fderiv_uniform_lower c d K hK hKU
  refine ⟨min b (q * δ), lt_min hb (mul_pos hq hδ), ?_⟩
  intro x hx y hy hxy
  refine ⟨(min_le_left _ _).trans (hbound x hx y hy hxy), ?_⟩
  change min b (q * δ) ≤ ‖fderiv ℝ (overlapTransition c d) x (x - y)‖
  rw [overlapTransition_fderiv c d (hKU hx)]
  exact ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left hxy hq.le)).trans (hqbound x hx (x-y))

end Burnett.Microlocal.AtlasOverlapKernel
