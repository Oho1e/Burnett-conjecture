import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy
import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletOperator
import Burnett.Analysis.Fourier.L2Extension

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Fourier
open Burnett.Analysis.SymmetricEnergy (coordinateDirection coordinateH1)
open scoped BigOperators Topology

abbrev ComplexCoordinateJet := PiLp 2 (fun _ : Fin 5 => ComplexL2 Space)

def schwartzCoordinateJet : SchwartzMap Space ℂ →ₗ[ℂ] ComplexCoordinateJet :=
  let P := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
  let K (i : Fin 4) := P.toLinearMap.comp (SchwartzMap.pderivCLM ℂ (coordinateDirection i)).toLinearMap
  (WithLp.linearEquiv 2 ℂ (Fin 5 → ComplexL2 Space)).symm.toLinearMap.comp
    (LinearMap.pi (Fin.cases P.toLinearMap K))

@[simp] theorem schwartzCoordinateJet_zero_component (f : SchwartzMap Space ℂ) :
    schwartzCoordinateJet f 0=f.toLp 2 volume := rfl

@[simp] theorem schwartzCoordinateJet_succ_component (f : SchwartzMap Space ℂ) (i : Fin 4) :
    schwartzCoordinateJet f i.succ=(SchwartzMap.pderivCLM ℂ (coordinateDirection i) f).toLp 2 volume := rfl

theorem schwartzCoordinateJet_norm (f : SchwartzMap Space ℂ) :
    ‖schwartzCoordinateJet f‖=coordinateH1 f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ,schwartzCoordinateJet_zero_component]
  simp only [schwartzCoordinateJet_succ_component]
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))]

private theorem schwartzCoordinateJet_injective : Function.Injective schwartzCoordinateJet := by
  intro f g h
  apply SchwartzMap.injective_toLp 2 volume
  exact congrArg (fun v : ComplexCoordinateJet => v 0) h

def complexCoordinateH1 : Submodule ℂ ComplexCoordinateJet :=
  (LinearMap.range schwartzCoordinateJet).topologicalClosure

instance : CompleteSpace complexCoordinateH1 := by
  unfold complexCoordinateH1
  infer_instance

def schwartzIntoCoordinateH1 : SchwartzMap Space ℂ →ₗ[ℂ] complexCoordinateH1 where
  toFun f := ⟨schwartzCoordinateJet f,(LinearMap.range schwartzCoordinateJet).le_topologicalClosure ⟨f,rfl⟩⟩
  map_add' f g := Subtype.ext (schwartzCoordinateJet.map_add f g)
  map_smul' c f := Subtype.ext (schwartzCoordinateJet.map_smul c f)

theorem schwartzIntoCoordinateH1_norm (f : SchwartzMap Space ℂ) :
    ‖schwartzIntoCoordinateH1 f‖=coordinateH1 f := schwartzCoordinateJet_norm f

def coordinateH1_projection (i : Fin 5) : complexCoordinateH1 →L[ℂ] ComplexL2 Space :=
  (PiLp.proj 2 (fun _ : Fin 5 => ComplexL2 Space) i).comp complexCoordinateH1.subtypeL

private def jetRangeInclusion : LinearMap.range schwartzCoordinateJet →L[ℂ] complexCoordinateH1 :=
  (Submodule.inclusion (LinearMap.range schwartzCoordinateJet).le_topologicalClosure).mkContinuous 1
    (fun x => by rw [one_mul]; exact le_rfl)

private theorem jetRangeInclusion_dense : DenseRange jetRangeInclusion := by
  exact (denseRange_inclusion_iff subset_closure).2 subset_rfl

private theorem jetRangeInclusion_uniform : IsUniformInducing jetRangeInclusion := by
  have h : Isometry jetRangeInclusion := Isometry.of_dist_eq fun _ _ => rfl
  exact h.isUniformInducing

/-- For each fixed Schwartz output, the input pairing extends along the
actual first-order Schwartz jet to its complete closure. -/
theorem exists_schwartzPair_left_coordinateH1_form
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (D : ℝ) (hR : ∀ f g, ‖R f g‖≤D*coordinateH1 f*coordinateH1 g)
    (g : SchwartzMap Space ℂ) :
    ∃ L : complexCoordinateH1 →L[ℂ] ℂ, ∀ f, L (schwartzIntoCoordinateH1 f)=R f g := by
  let F : SchwartzMap Space ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => R f g
      map_add' := fun f u => by
        simpa only [neg_one_smul,sub_neg_eq_add,neg_one_mul] using hLin f u g (-1)
      map_smul' := fun c u => by
        have hZero : R 0 g=0 := by simpa using hLin u u g 1
        simpa only [neg_smul,zero_sub,neg_neg,hZero,neg_mul,smul_eq_mul] using hLin 0 u g (-c) }
  let e := LinearEquiv.ofInjective schwartzCoordinateJet schwartzCoordinateJet_injective
  let H := F.comp e.symm.toLinearMap
  have hH (x : LinearMap.range schwartzCoordinateJet) : ‖H x‖≤(D*coordinateH1 g)*‖x‖ := by
    obtain ⟨f,rfl⟩ := e.surjective x
    change ‖F (e.symm (e f))‖≤_
    rw [LinearEquiv.symm_apply_apply]
    change ‖R f g‖≤(D*coordinateH1 g)*‖schwartzCoordinateJet f‖
    rw [schwartzCoordinateJet_norm]
    exact (hR f g).trans_eq (by ring)
  let L := (H.mkContinuous (D*coordinateH1 g) hH).extend
    jetRangeInclusion jetRangeInclusion_dense jetRangeInclusion_uniform
  refine ⟨L,fun f => ?_⟩
  have hE := ContinuousLinearMap.extend_eq (H.mkContinuous (D*coordinateH1 g) hH)
    jetRangeInclusion jetRangeInclusion_dense jetRangeInclusion_uniform (e f)
  change L (schwartzIntoCoordinateH1 f)=F (e.symm (e f)) at hE
  rw [LinearEquiv.symm_apply_apply] at hE
  exact hE

end Burnett.Analysis.CarlesonEmbedding
