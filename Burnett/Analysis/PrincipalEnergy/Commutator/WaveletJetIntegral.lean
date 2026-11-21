import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletSynthesisDerivative
import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletCenterVariation
import Burnett.Analysis.PrincipalEnergy.Commutator.SchwartzCoordinateJet
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Fourier
open Burnett.Analysis.SymmetricEnergy (coordinateH1 coordinateDirection)
open scoped ComplexConjugate InnerProductSpace Topology

private theorem inner_schwartz_toLp_eq_integral (g v : SchwartzMap Space ℂ) :
    ⟪g.toLp 2 volume,v.toLp 2 volume⟫_ℂ=∫ z, conj (g z)*v z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume,v.coeFn_toLp 2 volume] with z hg hv
  rw [hg,hv,RCLike.inner_apply']

private theorem schwartz_toLp_integral_of_translate (f k H : SchwartzMap Space ℂ)
    (w : Space → SchwartzMap Space ℂ) (hw : ∀ y z, w y z=k (z-y))
    (hH : ∀ z, H z=∫ y, f y*k (z-y))
    (hI : Integrable (fun y => f y • (w y).toLp 2 volume)) :
    (∫ y, f y • (w y).toLp 2 volume)=H.toLp 2 volume := by
  apply (schwartzL2Range_dense (V := Space)).eq_of_inner_right
  intro u
  obtain ⟨g,rfl⟩ := (schwartzRangeEquiv (V := Space)).surjective u
  change ⟪g.toLp 2 volume,∫ y, f y • (w y).toLp 2 volume⟫_ℂ=⟪g.toLp 2 volume,H.toLp 2 volume⟫_ℂ
  have hLinear := (innerSL ℂ (g.toLp 2 volume)).integral_comp_comm hI
  simp only [innerSL_apply] at hLinear
  rw [← hLinear]
  simp_rw [inner_smul_right,inner_schwartz_toLp_eq_integral,hw]
  let V : Measure Space := volume
  let F (z y : Space) := conj (g z)*(f y*k (z-y))
  have hProd : Integrable (uncurry F) (V.prod V) := by
    let S (p : Space × Space) := (p.1-p.2,p.2)
    have hS : MeasurePreserving S (V.prod V) (V.prod V) := measurePreserving_sub_prod V V
    have hRaw : Integrable (fun p : Space × Space => k (p.1-p.2)*f p.2) (V.prod V) :=
      hS.integrable_comp_of_integrable ((k.integrable (μ := V)).mul_prod (f.integrable (μ := V)))
    have hg : Continuous (fun p : Space × Space => conj (g p.1)) :=
      Complex.continuous_conj.comp (g.continuous.comp continuous_fst)
    simpa only [uncurry_apply_pair,F,mul_comm (f _)] using hRaw.bdd_mul hg.aestronglyMeasurable
      ⟨SchwartzMap.seminorm ℝ 0 0 g,fun p => by rw [Complex.norm_conj]; exact SchwartzMap.norm_le_seminorm ℝ g p.1⟩
  calc
    _ = ∫ y, ∫ z, F z y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [F]
      ring
    _ = ∫ z, ∫ y, F z y := (integral_integral_swap hProd).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hH z,← integral_const_mul]

/-- Synthesis of the actual Schwartz window as a Bochner integral of its
translated packets in the complete first-order jet closure. -/
theorem schwartzWaveletAction_coordinateH1_integral
    (θ : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) :
    let J (y : Space) := f y • schwartzIntoCoordinateH1 (centeredWavelet θ hθ s hs y)
    Integrable J ∧
      (∫ y, J y)=schwartzIntoCoordinateH1 (schwartzWaveletAction θ s hs f) := by
  intro J
  let w := centeredWavelet θ hθ s hs
  let k := w 0
  let H := schwartzWaveletAction θ s hs f
  let e (i : Fin 4) := coordinateDirection i
  have hw (y z : Space) : w y z=k (z-y) := by simp only [w,k,centeredWavelet_apply,sub_zero]
  have hC : Continuous (fun y => schwartzIntoCoordinateH1 (w y)) := by
    apply continuous_iff_continuousAt.2
    intro y
    apply tendsto_iff_norm_sub_tendsto_zero.2
    change Tendsto (fun x => ‖schwartzIntoCoordinateH1 (w x)-schwartzIntoCoordinateH1 (w y)‖) (𝓝 y) (𝓝 0)
    simpa only [map_sub] using ((centeredWavelet_coordinateH1_center θ hθ s hs y).1.congr
      fun x => (schwartzIntoCoordinateH1_norm (w x-w y)).symm)
  have hI : Integrable J := by
    let C := coordinateH1 k
    have hc : Continuous J := f.continuous.smul hC
    letI : SecondCountableTopologyEither Space complexCoordinateH1 := ⟨Or.inl inferInstance⟩
    refine (f.integrable.norm.const_mul C).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    change ‖f y • schwartzIntoCoordinateH1 (w y)‖≤C*‖f y‖
    rw [norm_smul,schwartzIntoCoordinateH1_norm,(centeredWavelet_coordinateH1_center θ hθ s hs y).2]
    exact (mul_comm _ _).le
  refine ⟨hI,?_⟩
  apply Subtype.ext
  apply PiLp.ext
  intro i
  have hProj := (coordinateH1_projection i).integral_comp_comm hI
  have hComp (i : Fin 5) := (coordinateH1_projection i).integrable_comp hI
  change coordinateH1_projection i (∫ y, J y)=coordinateH1_projection i (schwartzIntoCoordinateH1 H)
  rw [← hProj]
  refine Fin.cases ?_ (fun j => ?_) i
  · have hEq (y : Space) : coordinateH1_projection 0 (J y)=f y • (w y).toLp 2 volume := by
      change coordinateH1_projection 0 (f y • schwartzIntoCoordinateH1 (w y))=_
      rw [map_smul]
      rfl
    have hV (z : Space) : H z=∫ y, f y*k (z-y) := by
      change schwartzWaveletAction θ s hs f z=_
      rw [congrFun (schwartzWaveletAction_eq_actual θ s hs f) z]
      apply integral_congr_ae
      filter_upwards with y
      rw [← hw y z,centeredWavelet_apply,mul_comm]
    change (∫ y, coordinateH1_projection 0 (J y))=H.toLp 2 volume
    simp_rw [hEq]
    exact schwartz_toLp_integral_of_translate f k H w hw hV (by simpa only [Function.comp_apply,hEq] using hComp 0)
  · let D : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ := SchwartzMap.pderivCLM ℂ (e j)
    have hwD (y z : Space) : D (w y) z=D k (z-y) :=
      congrArg (fun L : Space →L[ℝ] ℂ => L (e j)) (centeredWavelet_fderiv_eq_translate θ hθ s hs y z)
    have hV (z : Space) : D H z=∫ y, f y*D k (z-y) := by
      obtain ⟨hEval,hDer⟩ := schwartzWaveletAction_fderiv_centered_integral θ hθ s hs f z
      let Ev : (Space →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (e j)
      have h := congrArg Ev hDer
      rw [← Ev.integral_comp_comm hEval] at h
      change D H z=∫ y, f y*D (w y) z at h
      simpa only [hwD] using h
    have hEq (y : Space) : coordinateH1_projection j.succ (J y)=f y • (D (w y)).toLp 2 volume := by
      change coordinateH1_projection j.succ (f y • schwartzIntoCoordinateH1 (w y))=_
      rw [map_smul]
      rfl
    change (∫ y, coordinateH1_projection j.succ (J y))=(D H).toLp 2 volume
    simp_rw [hEq]
    exact schwartz_toLp_integral_of_translate f (D k) (D H) (fun y => D (w y)) hwD hV
      (by simpa only [Function.comp_apply,hEq] using hComp j.succ)

end Burnett.Analysis.CarlesonEmbedding
