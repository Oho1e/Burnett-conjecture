import Burnett.Analysis.AngularCaps.ParabolicCapSupport
import Burnett.Analysis.AngularCaps.ParabolicProfileSmoothness

set_option autoImplicit false
set_option maxHeartbeats 13000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Metric
open scoped BigOperators ContDiff

section CompactDerivativeBounds

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem right_slice_iteratedFDeriv_le {f : P × E → ℝ} {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {p : P} {x : E} (hx : (p,x) ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y : E => f (p,y)) x‖ ≤ ‖iteratedFDeriv ℝ j f (p,x)‖ := by
  let L : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  let z : P × E := (p,0)
  let shift : P × E → P × E := fun y => z+y
  let V := shift ⁻¹' U
  have hZ (y : E) : shift (L y) = (p,y) := by simp [shift,z,L,ContinuousLinearMap.inr_apply]
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hVL : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hxV : L x ∈ V := by change shift (L x) ∈ U; rwa [hZ]
  have hShift : ContDiffOn ℝ ∞ (f ∘ shift) V :=
    hf.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun _ hy => hy)
  have hC := L.iteratedFDerivWithin_comp_right hShift hV.uniqueDiffOn hVL.uniqueDiffOn hxV
    (i := j) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen j hVL (x := x) hxV,
    iteratedFDerivWithin_of_isOpen j hV (x := L x) hxV] at hC
  have hF : (f ∘ shift) ∘ L = fun y : E => f (p,y) := by
    funext y
    exact congrArg f (hZ y)
  have hShiftDeriv : iteratedFDeriv ℝ j (f ∘ shift) (L x) = iteratedFDeriv ℝ j f (p,x) := by
    change iteratedFDeriv ℝ j (fun y => f (z+y)) (L x) = _
    rw [iteratedFDeriv_comp_add_left]
    exact congrArg (iteratedFDeriv ℝ j f) (hZ x)
  rw [hF,hShiftDeriv] at hC
  rw [hC]
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun y => by
    change ‖((0 : P),y)‖ ≤ 1*‖y‖
    simp [Prod.norm_def])
  have hProduct : (∏ _ : Fin j, ‖L‖) ≤ 1 := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) hL j
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hProduct)

/-- Smooth joint dependence on an open neighborhood gives uniform bounds for
each frequency derivative on any compact collection of parameter/frequency
pairs. The derivative acts only in the frequency variable. -/
theorem exists_uniform_right_slice_iteratedFDeriv {f : P × E → ℝ} {U K : Set (P × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hK : IsCompact K) (hKU : K ⊆ U) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖iteratedFDeriv ℝ j (fun y : E => f (z.1,y)) z.2‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ j f) U :=
    (hf.continuousOn_iteratedFDerivWithin (m := j) (WithTop.coe_le_coe.mpr le_top) hU.uniqueDiffOn).congr
      (fun z hz => (iteratedFDerivWithin_of_isOpen j hU (x := z) hz).symm)
  obtain ⟨C,hC,hB⟩ := (hK.image_of_continuousOn (hc.mono hKU)).isBounded.exists_pos_norm_le
  refine ⟨C,hC,fun z hz => ?_⟩
  exact (right_slice_iteratedFDeriv_le hU hf (hKU hz) j).trans
    (hB _ ⟨z,hz,rfl⟩)

end CompactDerivativeBounds

abbrev ParabolicProfileParameters := NullCoordinateMap × ℝ × ℝ
abbrev ParabolicProfileData := ParabolicProfileParameters × NullFrequencyCoordinates

def parabolicEnlargedDomain : Set ParabolicProfileData :=
  {z | z.1.2.1 ≠ 0 ∧ z.1.1 (parabolicDilation z.1.2.2 z.2) ≠ 0 ∧ z.1.1 nullAxis ≠ 0}

private theorem parameter_frame_contDiff : ContDiff ℝ ∞ (fun z : ParabolicProfileData => z.1.1) :=
  contDiff_fst.fst

private theorem parameter_coneScale_contDiff : ContDiff ℝ ∞ (fun z : ParabolicProfileData => z.1.2.1) :=
  contDiff_fst.snd.fst

private theorem parameter_capScale_contDiff : ContDiff ℝ ∞ (fun z : ParabolicProfileData => z.1.2.2) :=
  contDiff_fst.snd.snd

theorem parabolicEnlargedDomain_open : IsOpen parabolicEnlargedDomain := by
  have hFreq : ContDiff ℝ ∞ (fun z : ParabolicProfileData => z.1.1 (parabolicDilation z.1.2.2 z.2)) :=
    parameter_frame_contDiff.clm_apply (contDiffOn_univ.mp
      (parabolicDilation_contDiffOn parameter_capScale_contDiff.contDiffOn contDiff_snd.contDiffOn))
  have hAxis : ContDiff ℝ ∞ (fun z : ParabolicProfileData => z.1.1 nullAxis) :=
    parameter_frame_contDiff.clm_apply contDiff_const
  exact (isOpen_ne_fun parameter_coneScale_contDiff.continuous continuous_const).inter
    ((isOpen_ne_fun hFreq.continuous continuous_const).inter (isOpen_ne_fun hAxis.continuous continuous_const))

theorem parabolicEnlargedProfile_joint_contDiffOn (outer enlarged : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ParabolicProfileData =>
      parabolicEnlargedProfile z.1.1 z.1.2.1 z.1.2.2 outer enlarged z.2) parabolicEnlargedDomain := by
  have hC := parabolicConeRatio_contDiffOn (S := parabolicEnlargedDomain)
    parameter_frame_contDiff.contDiffOn parameter_coneScale_contDiff.contDiffOn
    parameter_capScale_contDiff.contDiffOn contDiff_snd.contDiffOn (fun _ h => ⟨h.1,h.2.1⟩)
  have hA := parabolicWedgeRatio_contDiffOn (S := parabolicEnlargedDomain)
    parameter_frame_contDiff.contDiffOn parameter_capScale_contDiff.contDiffOn
    contDiff_snd.contDiffOn (v := fun _ => nullAxis) contDiffOn_const (fun _ h =>
      ⟨h.2.1,by simpa only [parabolicDilation_nullAxis] using h.2.2⟩)
  exact ((descendingProfile_contDiff _ _).comp_contDiffOn (hC.pow 2)).mul
    ((descendingProfile_contDiff _ _).comp_contDiffOn hA)

/-- Bounded frames with a common inverse-norm bound form a compact set
of coordinate maps. -/
def boundedNullCoordinateMaps (B : ℝ) : Set NullCoordinateMap :=
  {F | ‖F‖ ≤ B ∧ ∀ u : NullFrequencyCoordinates, ‖u‖ ≤ B*‖F u‖}

theorem boundedNullCoordinateMaps_compact (B : ℝ) : IsCompact (boundedNullCoordinateMaps B) := by
  have hEq : boundedNullCoordinateMaps B =
      {F : NullCoordinateMap | ‖F‖ ≤ B} ∩ ⋂ u : NullFrequencyCoordinates, {F | ‖u‖ ≤ B*‖F u‖} := by
    ext F
    simp only [boundedNullCoordinateMaps,Set.mem_inter_iff,Set.mem_iInter,Set.mem_setOf_eq]
  have hClosed : IsClosed (boundedNullCoordinateMaps B) := by
    rw [hEq]
    refine (isClosed_le continuous_norm continuous_const).inter (isClosed_iInter fun u => ?_)
    exact isClosed_le continuous_const (continuous_const.mul
      ((ContinuousLinearMap.apply ℝ Vec u).continuous.norm))
  refine (isCompact_closedBall (0 : NullCoordinateMap) B).of_isClosed_subset hClosed ?_
  intro F hF
  exact (mem_closedBall_zero_iff).mpr hF.1

theorem chart_mem_boundedNullCoordinateMaps {m : Form} {w : Vec} (F : NullCapChart m w) {B : ℝ}
    (hF : ‖F.toFrequency.toContinuousLinearMap‖ ≤ B)
    (hI : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B) :
    F.toFrequency.toContinuousLinearMap ∈ boundedNullCoordinateMaps B := by
  refine ⟨hF,fun u => ?_⟩
  have h := F.toFrequency.symm.toContinuousLinearMap.le_opNorm (F.toFrequency u)
  change ‖F.toFrequency.symm (F.toFrequency u)‖ ≤
    ‖F.toFrequency.symm.toContinuousLinearMap‖ * ‖F.toFrequency u‖ at h
  rw [F.toFrequency.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_right hI (norm_nonneg _))

/-- For fixed positive cone scale and bounded frames, every frequency
derivative of the enlarged profile is uniformly bounded on the normalized
support region, including the parameter limit `δ=0`. -/
theorem parabolicEnlargedProfile_uniformJets (outer enlarged B : ℝ) {a s₀ : ℝ}
    (ha : a ≠ 0) (hs₀ : 0 < s₀) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F ∈ boundedNullCoordinateMaps B, ∀ δ ∈ Icc (0 : ℝ) 1,
      ∀ u : NullFrequencyCoordinates, ‖u‖ = 1 → s₀ ≤ |u.1| →
        ‖iteratedFDeriv ℝ j (parabolicEnlargedProfile F a δ outer enlarged) u‖ ≤ C := by
  let T := sphere (0 : NullFrequencyCoordinates) 1 ∩ {u | s₀ ≤ |u.1|}
  let K : Set ParabolicProfileData :=
    (boundedNullCoordinateMaps B ×ˢ (({a} : Set ℝ) ×ˢ Icc 0 1)) ×ˢ T
  have hT : IsCompact T := (isCompact_sphere _ _).inter_right
    (isClosed_le continuous_const continuous_fst.abs)
  have hK : IsCompact K :=
    ((boundedNullCoordinateMaps_compact B).prod (isCompact_singleton.prod isCompact_Icc)).prod hT
  have hDom : K ⊆ parabolicEnlargedDomain := by
    intro z hz
    obtain ⟨⟨F,b,δ⟩,u⟩ := z
    have hF : F ∈ boundedNullCoordinateMaps B := hz.1.1
    have hab : b = a := Set.mem_singleton_iff.mp hz.1.2.1
    have hs : 0 < |u.1| := hs₀.trans_le hz.2.2
    have hF0 (v : NullFrequencyCoordinates) (hv : v ≠ 0) : F v ≠ 0 := by
      intro he
      exact (not_le_of_gt (norm_pos_iff.mpr hv)) (by simpa only [he,norm_zero,mul_zero] using hF.2 v)
    have hAxis : nullAxis ≠ 0 := by
      intro h
      have h' := congrArg Prod.fst h
      norm_num [nullAxis] at h'
    exact ⟨hab.symm ▸ ha, hF0 _ (parabolicDilation_ne_zero_of_s (abs_pos.mp hs)),hF0 _ hAxis⟩
  obtain ⟨C,hC,hBound⟩ := exists_uniform_right_slice_iteratedFDeriv parabolicEnlargedDomain_open
    (parabolicEnlargedProfile_joint_contDiffOn outer enlarged) hK hDom j
  refine ⟨C,hC,fun F hF δ hδ u hu huS => ?_⟩
  exact hBound ((F,a,δ),u)
    ⟨⟨hF,Set.mem_singleton a,hδ⟩,by simpa only [mem_sphere,dist_zero_right] using hu,huS⟩

end Burnett.Analysis.ProjectiveNullCaps
