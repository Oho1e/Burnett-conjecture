import Burnett.Analysis.PrincipalEnergy.Quantization.CompactBaseFourier

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Metric Set
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped ContDiff Topology

private theorem norm_iteratedFDeriv_first_section_le
    {W : E × E → ℂ} (hW : ContDiff ℝ ∞ W) (n : ℕ) (x ξ : E) :
    ‖iteratedFDeriv ℝ n (fun y => W (y,ξ)) x‖ ≤ ‖iteratedFDeriv ℝ n W (x,ξ)‖ := by
  let e : E →ₗᵢ[ℝ] E × E := ⟨(ContinuousLinearMap.inl ℝ E E).toLinearMap, by
    intro y
    simp [Prod.norm_def]⟩
  let Wξ : E × E → ℂ := fun p => W (p + (0,ξ))
  have hWξ : ContDiff ℝ ∞ Wξ := hW.comp (contDiff_id.add contDiff_const)
  have hOrder : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have base := e.toContinuousLinearMap.iteratedFDeriv_comp_right hWξ x hOrder
  have he : Wξ ∘ e.toContinuousLinearMap = fun y => W (y,ξ) := by
    funext y
    change W ((y, 0) + (0, ξ)) = W (y,ξ)
    simp
  rw [he] at base
  have hShift : iteratedFDeriv ℝ n Wξ (e x) = iteratedFDeriv ℝ n W (x,ξ) := by
    change iteratedFDeriv ℝ n (fun p => W (p + (0,ξ))) (x,0) = _
    rw [iteratedFDeriv_comp_add_right]
    simp
  change iteratedFDeriv ℝ n (fun y => W (y,ξ)) x =
    (iteratedFDeriv ℝ n Wξ (e x)).compContinuousLinearMap (fun _ => e.toContinuousLinearMap) at base
  rw [base, hShift]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ _

private def angularUnitCutoff (ξ : E) : ℝ := 1 - radialCore ((4 : ℝ) • ξ)

private theorem contDiff_angularUnitCutoff : ContDiff ℝ ∞ angularUnitCutoff :=
  contDiff_const.sub (radialCore_contDiff.comp (contDiff_const.smul contDiff_id))

private theorem contDiff_cutoff_homogeneousAngular
    (p : E → E → ℂ) (hJoint : ContDiffOn ℝ ∞ (Function.uncurry p) (univ ×ˢ ({0}ᶜ : Set E))) :
    ContDiff ℝ ∞ (fun z : E × E => angularUnitCutoff z.2 • p z.1 z.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.2 = 0
  · have hn : ‖z.2‖ < (1 : ℝ) / 4 := by simp [hz]
    have hb : ∀ᶠ q : E × E in 𝓝 z, ‖q.2‖ < (1 : ℝ) / 4 :=
      (continuous_snd.norm.tendsto z).eventually (Iio_mem_nhds hn)
    refine (show ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) z from contDiffAt_const)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hb] with q hq
    have h4 : ‖(4 : ℝ) • q.2‖ ≤ 1 := by
      rw [norm_smul]
      norm_num
      linarith
    simp [angularUnitCutoff, radialCore_eq_one _ h4]
  · have hOpen : IsOpen ((univ : Set E) ×ˢ ({0}ᶜ : Set E)) :=
      isOpen_univ.prod isOpen_compl_singleton
    exact (contDiff_angularUnitCutoff.comp
      (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E × E → E))).contDiffAt.smul
      (hJoint.contDiffAt (hOpen.mem_nhds ⟨mem_univ _, hz⟩))

/-- Joint regularity and positive degree zero control every pure base
derivative uniformly in the angular variable on a fixed compact base. -/
theorem exists_uniform_baseDerivative_of_homogeneousAngular
    (p : E → E → ℂ) (K : Set E) (hK : IsCompact K)
    (hSupport : ∀ ξ, tsupport (fun x => p x ξ) ⊆ K)
    (hJoint : ContDiffOn ℝ ∞ (Function.uncurry p) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => p x 0)) (hDegree : ∀ x, DegreeZero (p x))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C := by
  let S := sphere (0 : E) 1
  have hOrder : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  let W : E × E → ℂ := fun q => angularUnitCutoff q.2 • p q.1 q.2
  have hW : ContDiff ℝ ∞ W := contDiff_cutoff_homogeneousAngular p hJoint
  have hWDer : Continuous (iteratedFDeriv ℝ n W) := hW.continuous_iteratedFDeriv hOrder
  have hZeroDer : Continuous (iteratedFDeriv ℝ n (fun x => p x 0)) :=
    hZero.continuous_iteratedFDeriv hOrder
  have hKS : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere (0 : E) 1)
  obtain ⟨D, hD⟩ := (hKS.image hWDer).isBounded.exists_norm_le
  obtain ⟨B, hB⟩ := (hK.image hZeroDer).isBounded.exists_norm_le
  let C := max 0 (max B D)
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro x ξ
  by_cases hx : x ∈ K
  · by_cases hξ : ξ = 0
    · rw [hξ]
      have hb := hB _ (mem_image_of_mem (iteratedFDeriv ℝ n (fun x => p x 0)) hx)
      exact hb.trans (le_trans (le_max_left B D) (le_max_right 0 (max B D)))
    · have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      let η := ‖ξ‖⁻¹ • ξ
      have hη : ‖η‖ = 1 := by
        rw [show η = ‖ξ‖⁻¹ • ξ from rfl, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
      have hηS : η ∈ S := by simpa only [S, mem_sphere, dist_zero_right] using hη
      have hCut : angularUnitCutoff η = 1 := by
        unfold angularUnitCutoff
        rw [radialCore_eq_zero]
        · exact sub_zero _
        · rw [norm_smul, hη]; norm_num
      have hSlice : (fun y => p y ξ) = fun y => W (y,η) := by
        funext y
        simp only [W, hCut, one_smul]
        exact (hDegree y _ (inv_pos.mpr hpos) _).symm
      rw [hSlice]
      have hIn : (x,η) ∈ K ×ˢ S := ⟨hx,hηS⟩
      have hd := hD _ (mem_image_of_mem (iteratedFDeriv ℝ n W) hIn)
      exact (norm_iteratedFDeriv_first_section_le hW n x η).trans
        (hd.trans (le_trans (le_max_right B D) (le_max_right 0 (max B D))))
  · have hz : iteratedFDeriv ℝ n (fun y => p y ξ) x = 0 := by
      by_contra h
      exact hx (hSupport ξ (support_iteratedFDeriv_subset n h))
    simpa only [hz, norm_zero] using hC

end Burnett.Microlocal.Overlap
