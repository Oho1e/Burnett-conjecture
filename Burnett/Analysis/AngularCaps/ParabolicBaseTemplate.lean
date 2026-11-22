import Burnett.Analysis.AngularCaps.ParabolicProfileJets

set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Metric
open scoped ContDiff BigOperators

abbrev CapNeighborParameters (N : ℕ) := Fin N → ℝ × NullFrequencyCoordinates
abbrev BaseCapParameters (N : ℕ) := ParabolicProfileParameters × CapNeighborParameters N
abbrev BaseCapProfileData (N : ℕ) := BaseCapParameters N × NullFrequencyCoordinates

def parabolicBaseAngularSum {N : ℕ} (F : NullCoordinateMap) (δ : ℝ)
    (v : CapNeighborParameters N) (u : NullFrequencyCoordinates) : ℝ :=
  ∑ i, (v i).1 * parabolicAngularFactor F δ (3/4) 1 u (v i).2

/-- The exact normalized base symbol after representing its local angular sum
by finitely many scaled centers. Zero coefficients allow padding. -/
def parabolicBaseProfile {N : ℕ} (F : NullCoordinateMap) (a δ inner outer : ℝ)
    (v : CapNeighborParameters N) (u : NullFrequencyCoordinates) : ℝ :=
  parabolicConeFactor F a δ inner outer u *
    (parabolicAngularFactor F δ (3/4) 1 u nullAxis /
      regularizedAngularSum (parabolicBaseAngularSum F δ v u))

private def forgetNeighbors {N : ℕ} (z : BaseCapProfileData N) : ParabolicProfileData := (z.1.1,z.2)

private def baseCapFrequencyDomain (N : ℕ) : Set (BaseCapProfileData N) :=
  forgetNeighbors ⁻¹' parabolicEnlargedDomain ∩
    ⋂ i : Fin N, {z | z.1.1.1 (parabolicDilation z.1.1.2.2 (z.1.2 i).2) ≠ 0}

private def profileDenominator {N : ℕ} (z : BaseCapProfileData N) : ℝ :=
  regularizedAngularSum (parabolicBaseAngularSum z.1.1.1 z.1.1.2.2 z.1.2 z.2)

def baseCapProfileDomain (N : ℕ) : Set (BaseCapProfileData N) :=
  baseCapFrequencyDomain N ∩ profileDenominator ⁻¹' {x | x ≠ 0}

private theorem baseFrame_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (fun z : BaseCapProfileData N => z.1.1.1) :=
  contDiff_fst.fst.fst

private theorem baseScale_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (fun z : BaseCapProfileData N => z.1.1.2.2) :=
  contDiff_fst.fst.snd.snd

private theorem baseConeScale_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (fun z : BaseCapProfileData N => z.1.1.2.1) :=
  contDiff_fst.fst.snd.fst

private theorem baseNeighbor_contDiff {N : ℕ} (i : Fin N) :
    ContDiff ℝ ∞ (fun z : BaseCapProfileData N => z.1.2 i) :=
  (contDiff_apply ℝ (ℝ × NullFrequencyCoordinates) i).comp contDiff_fst.snd

private theorem baseCapFrequencyDomain_open (N : ℕ) : IsOpen (baseCapFrequencyDomain N) := by
  have hForget : Continuous (forgetNeighbors : BaseCapProfileData N → ParabolicProfileData) :=
    continuous_fst.fst.prodMk continuous_snd
  refine (parabolicEnlargedDomain_open.preimage hForget).inter
    (isOpen_iInter_of_finite fun i => ?_)
  have h : ContDiff ℝ ∞ (fun z : BaseCapProfileData N =>
      z.1.1.1 (parabolicDilation z.1.1.2.2 (z.1.2 i).2)) :=
    (baseFrame_contDiff N).clm_apply (contDiffOn_univ.mp
      (parabolicDilation_contDiffOn (baseScale_contDiff N).contDiffOn (baseNeighbor_contDiff i).snd.contDiffOn))
  exact isOpen_ne_fun h.continuous continuous_const

private theorem baseCapAngularSum_contDiffOn (N : ℕ) :
    ContDiffOn ℝ ∞ (fun z : BaseCapProfileData N => parabolicBaseAngularSum z.1.1.1 z.1.1.2.2 z.1.2 z.2)
      (baseCapFrequencyDomain N) := by
  apply ContDiffOn.sum
  intro i _
  apply (baseNeighbor_contDiff i).fst.contDiffOn.mul
  apply (descendingProfile_contDiff _ _).comp_contDiffOn
  refine parabolicWedgeRatio_contDiffOn (baseFrame_contDiff N).contDiffOn
    (baseScale_contDiff N).contDiffOn contDiff_snd.contDiffOn (baseNeighbor_contDiff i).snd.contDiffOn ?_
  intro z hz
  have hProj : forgetNeighbors z ∈ parabolicEnlargedDomain := hz.1
  exact ⟨hProj.2.1,Set.mem_iInter.mp hz.2 i⟩

private theorem profileDenominator_contDiffOn (N : ℕ) :
    ContDiffOn ℝ ∞ (profileDenominator : BaseCapProfileData N → ℝ) (baseCapFrequencyDomain N) :=
  regularizedAngularSum_contDiff.comp_contDiffOn (baseCapAngularSum_contDiffOn N)

theorem baseCapProfileDomain_open (N : ℕ) : IsOpen (baseCapProfileDomain N) :=
  (profileDenominator_contDiffOn N).continuousOn.isOpen_inter_preimage
    (baseCapFrequencyDomain_open N) isOpen_ne

theorem parabolicBaseProfile_joint_contDiffOn (N : ℕ) (inner outer : ℝ) :
    ContDiffOn ℝ ∞ (fun z : BaseCapProfileData N =>
      parabolicBaseProfile z.1.1.1 z.1.1.2.1 z.1.1.2.2 inner outer z.1.2 z.2) (baseCapProfileDomain N) := by
  have hDen := (profileDenominator_contDiffOn N).mono
    (Set.inter_subset_left : baseCapProfileDomain N ⊆ baseCapFrequencyDomain N)
  have hC := parabolicConeRatio_contDiffOn (S := baseCapProfileDomain N)
    (baseFrame_contDiff N).contDiffOn (baseConeScale_contDiff N).contDiffOn
    (baseScale_contDiff N).contDiffOn contDiff_snd.contDiffOn (fun z hz => by
      have hp : forgetNeighbors z ∈ parabolicEnlargedDomain := hz.1.1
      exact ⟨hp.1,hp.2.1⟩)
  have hA := parabolicWedgeRatio_contDiffOn (S := baseCapProfileDomain N)
    (baseFrame_contDiff N).contDiffOn (baseScale_contDiff N).contDiffOn contDiff_snd.contDiffOn
    (v := fun _ => nullAxis) contDiffOn_const (fun z hz => by
      have hp : forgetNeighbors z ∈ parabolicEnlargedDomain := hz.1.1
      exact ⟨hp.2.1,by simpa only [parabolicDilation_nullAxis] using hp.2.2⟩)
  exact ((descendingProfile_contDiff _ _).comp_contDiffOn (hC.pow 2)).mul
    (((descendingProfile_contDiff _ _).comp_contDiffOn hA).div hDen (fun _ hz => hz.2))

/-- The neighbor coordinates and strengths of a zero-padded list lie in this
compact product. The radial bound keeps every term smooth, including the dummy
entries whose strength is zero. -/
def boundedCapNeighbors (N : ℕ) (M s₁ : ℝ) : Set (CapNeighborParameters N) :=
  {v | ∀ i, (v i).1 ∈ Icc (0 : ℝ) 1 ∧ ‖(v i).2‖ ≤ M ∧ s₁ ≤ |(v i).2.1|}

private theorem boundedCapNeighbors_compact (N : ℕ) (M s₁ : ℝ) :
    IsCompact (boundedCapNeighbors N M s₁) := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ
      (closedBall (0:NullFrequencyCoordinates) M ∩ {u | s₁ ≤ |u.1|})) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_fst.abs))
  convert isCompact_pi_infinite (fun _ : Fin N => hK) using 1
  ext v
  simp only [boundedCapNeighbors,Set.mem_setOf_eq,Set.mem_prod,Set.mem_inter_iff,mem_closedBall_zero_iff]

private theorem nonzero_frequency_of_boundedMap {F : NullCoordinateMap} {B : ℝ}
    (hF : F ∈ boundedNullCoordinateMaps B) {u : NullFrequencyCoordinates} (hu : u ≠ 0) : F u ≠ 0 := by
  intro hz
  exact (not_le_of_gt (norm_pos_iff.mpr hu)) (by simpa only [hz,norm_zero,mul_zero] using hF.2 u)

private theorem fixed_baseCapProfileDomain {N : ℕ} {F : NullCoordinateMap} {B a δ M s₀ s₁ : ℝ}
    {v : CapNeighborParameters N} {u : NullFrequencyCoordinates}
    (hF : F ∈ boundedNullCoordinateMaps B) (ha : a ≠ 0) (hu : s₀ ≤ |u.1|) (h₀ : 0 < s₀)
    (hv : v ∈ boundedCapNeighbors N M s₁) (h₁ : 0 < s₁) :
    (((F,a,δ),v),u) ∈ baseCapProfileDomain N := by
  have hU := nonzero_frequency_of_boundedMap hF
    (parabolicDilation_ne_zero_of_s (δ := δ) (abs_pos.mp (h₀.trans_le hu)))
  have hAxis0 : nullAxis ≠ 0 := by
    intro h
    have he := congrArg Prod.fst h
    norm_num [nullAxis] at he
  have hPre : (((F,a,δ),v),u) ∈ baseCapFrequencyDomain N := by
    refine ⟨⟨ha,hU,nonzero_frequency_of_boundedMap hF hAxis0⟩,?_⟩
    apply Set.mem_iInter.mpr
    intro i
    exact nonzero_frequency_of_boundedMap hF
      (parabolicDilation_ne_zero_of_s (abs_pos.mp (h₁.trans_le (hv i).2.2)))
  refine ⟨hPre,?_⟩
  apply ne_of_gt
  apply (show (0:ℝ) < 1/4 by norm_num).trans_le
  apply regularizedAngularSum_lower
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hv i).1.1 (descendingProfile_range _ _ _).1

/-- Each frequency derivative of the fixed-size base profile is uniformly
bounded on the compact rescaled support box, with a constant independent of δ.
This applies to the actual base symbol after local restriction and zero padding. -/
theorem parabolicBaseProfile_uniformJets (N : ℕ) (inner outer B M : ℝ) {a s₀ s₁ : ℝ}
    (ha : a ≠ 0) (h₀ : 0 < s₀) (h₁ : 0 < s₁) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F ∈ boundedNullCoordinateMaps B, ∀ δ ∈ Icc (0 : ℝ) 1,
      ∀ v ∈ boundedCapNeighbors N M s₁, ∀ u : NullFrequencyCoordinates, ‖u‖ = 1 → s₀ ≤ |u.1| →
        ‖iteratedFDeriv ℝ j (parabolicBaseProfile F a δ inner outer v) u‖ ≤ C := by
  let Q := sphere (0:NullFrequencyCoordinates) 1 ∩ {u | s₀ ≤ |u.1|}
  let K : Set (BaseCapProfileData N) :=
    (((boundedNullCoordinateMaps B) ×ˢ (({a}:Set ℝ) ×ˢ Icc 0 1)) ×ˢ boundedCapNeighbors N M s₁) ×ˢ Q
  have hQ : IsCompact Q := (isCompact_sphere _ _).inter_right (isClosed_le continuous_const continuous_fst.abs)
  have hK : IsCompact K :=
    (((boundedNullCoordinateMaps_compact B).prod (isCompact_singleton.prod isCompact_Icc)).prod
      (boundedCapNeighbors_compact N M s₁)).prod hQ
  have hKU : K ⊆ baseCapProfileDomain N := by
    intro z hz
    obtain ⟨⟨⟨F,b,δ⟩,v⟩,u⟩ := z
    have hEq : b = a := Set.mem_singleton_iff.mp hz.1.1.2.1
    exact fixed_baseCapProfileDomain hz.1.1.1 (hEq.symm ▸ ha) hz.2.2 h₀ hz.1.2 h₁
  obtain ⟨C,hC,hCS⟩ := exists_uniform_right_slice_iteratedFDeriv (baseCapProfileDomain_open N)
    (parabolicBaseProfile_joint_contDiffOn N inner outer) hK hKU j
  refine ⟨C,hC,fun F hF δ hδ v hv u hu hS => ?_⟩
  exact hCS (((F,a,δ),v),u)
    ⟨⟨⟨hF,Set.mem_singleton a,hδ⟩,hv⟩,by simpa only [mem_sphere,dist_zero_right] using hu,hS⟩

end Burnett.Analysis.ProjectiveNullCaps
