import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Burnett.Analysis.Fourier.SchwartzDensity
import Mathlib.Analysis.Normed.Operator.Completeness

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open Set MeasureTheory Metric Burnett.Fourier
open scoped ENNReal

private abbrev ELp (p : ℝ≥0∞) := Lp ℂ p (volume : Measure E)

private def common (p q : ℝ≥0∞) : Submodule ℂ (ELp p) where
  carrier := {x | MemLp (x : E → ℂ) q volume}
  zero_mem' := MemLp.zero.ae_eq (Lp.coeFn_zero ℂ p (volume : Measure E)).symm
  add_mem' {x y} hx hy := (hx.add hy).ae_eq (Lp.coeFn_add x y).symm
  smul_mem' c x hx := (hx.const_smul c).ae_eq (Lp.coeFn_smul c x).symm

private def swap (p q : ℝ≥0∞) : common p q →ₗ[ℂ] ELp q where
  toFun x := x.property.toLp ((x : ELp p) : E → ℂ)
  map_add' x y := by
    apply Lp.ext
    filter_upwards [(x+y).property.coeFn_toLp,x.property.coeFn_toLp,y.property.coeFn_toLp,
      Lp.coeFn_add (x : ELp p) (y : ELp p),
      Lp.coeFn_add (x.property.toLp _) (y.property.toLp _)] with ξ hs hx hy hp hq
    exact (hs.trans hp).trans (hq.trans (show _ = _ from congrArg₂ (·+·) hx hy)).symm
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [(c • x).property.coeFn_toLp,x.property.coeFn_toLp,
      Lp.coeFn_smul c (x : ELp p),Lp.coeFn_smul c (x.property.toLp _)] with ξ hs hx hp hq
    exact (hs.trans hp).trans (hq.trans (show _ = _ from congrArg (fun z : ℂ => c • z) hx)).symm

private theorem common_dense (p : ℝ≥0∞) (hp : p ≠ ⊤) [Fact (1≤p)] :
    Dense (common p 2 : Set (ELp p)) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hpos : 0 < ε/2 := by positivity
  obtain ⟨g,hg,dist,cg,pg⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.ofReal_ne_zero_iff.mpr hpos)
  refine ⟨pg.toLp g,((cg.memLp_of_hasCompactSupport (p := 2) hg).ae_eq pg.coeFn_toLp.symm),?_⟩
  rw [dist_eq_norm,← Lp.toLp_coeFn f (Lp.memLp f),← MemLp.toLp_sub,Lp.norm_toLp]
  exact ((ENNReal.toReal_le_toReal ((Lp.memLp f).sub pg).2.ne ENNReal.ofReal_ne_top).mpr dist).trans_lt
    (by simpa only [ENNReal.toReal_ofReal hpos.le] using half_lt_self hε)

theorem mikhlin_extend_from_intersection (p : ℝ≥0∞) (hp : p ≠ ⊤) [Fact (1≤p)]
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (C : ℝ≥0∞) (hc : C<⊤)
    (bound : ∀ (f : E → ℂ) (h₂ : MemLp f 2 volume), MemLp f p volume →
      eLpNorm (T (h₂.toLp f) : E → ℂ) p volume ≤ C * eLpNorm f p volume) :
    ∃ S : ELp p →L[ℂ] ELp p, (∀ f, ‖S f‖ ≤ C.toReal * ‖f‖) ∧
      ∀ (f : E → ℂ) (h₂ : MemLp f 2 volume) (hₚ : MemLp f p volume),
        (S (hₚ.toLp f) : E → ℂ) =ᵐ[volume] (T (h₂.toLp f) : E → ℂ) := by
  let U := common p 2
  let A := T.toLinearMap.comp (swap p 2)
  have ret (x : U) : A x ∈ common 2 p := by
    refine ⟨Lp.aestronglyMeasurable (A x),?_⟩
    exact (bound _ x.property (Lp.memLp (x : ELp p))).trans_lt (ENNReal.mul_lt_top hc (Lp.memLp (x : ELp p)).2)
  let B := (swap 2 p).comp (A.codRestrict (common 2 p) ret)
  have be (x : U) : (B x : E → ℂ) =ᵐ[volume] (A x : E → ℂ) := (ret x).coeFn_toLp
  have norm (x : U) : ‖B x‖ ≤ C.toReal * ‖x‖ := by
    have hx := bound _ x.property (Lp.memLp (x : ELp p))
    change eLpNorm (A x : E → ℂ) p volume ≤ _ at hx
    rw [← eLpNorm_congr_ae (be x),← Lp.enorm_def,← Lp.enorm_def] at hx
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hc.ne enorm_ne_top) hx
    simpa only [ENNReal.toReal_mul,toReal_enorm] using h
  let Bc := B.mkContinuous C.toReal norm
  have dense := common_dense p hp
  let emb := U.subtypeₗᵢ.isometry.isUniformInducing
  let S := Bc.extend U.subtypeL dense.denseRange_val emb
  have agree (x : U) : S x = B x := ContinuousLinearMap.extend_eq Bc U.subtypeL dense.denseRange_val emb x
  refine ⟨S,?_,?_⟩
  · intro f
    apply dense.denseRange_val.induction_on (p := fun y => ‖S y‖ ≤ C.toReal*‖y‖) f
    · exact isClosed_le S.continuous.norm (continuous_const.mul continuous_norm)
    · intro x
      rw [agree]
      exact norm x
  · intro f h₂ hₚ
    let x : U := ⟨hₚ.toLp f,h₂.ae_eq hₚ.coeFn_toLp.symm⟩
    change (S (x : ELp p) : E → ℂ) =ᵐ[volume] _
    rw [agree]
    have hx : swap p 2 x = h₂.toLp f := MemLp.toLp_congr x.property h₂ hₚ.coeFn_toLp
    have hax : A x = T (h₂.toLp f) := congrArg T hx
    simpa only [hax] using be x

end Burnett.A02.FrequencySplit
