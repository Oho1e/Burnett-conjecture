import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCoordinateMiddleTerm
import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy

set_option autoImplicit false
set_option maxHeartbeats 5200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (Op coordinateDirection IsSkew)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

/-- The finite family of compactly supported Schwartz components. -/
def compactSchwartzComponents (ι : Type*) : Submodule ℂ (ι → SchwartzMap Space ℂ) where
  carrier := {f | ∀ i, HasCompactSupport (f i : Space → ℂ)}
  zero_mem' := fun _ => HasCompactSupport.zero
  add_mem' := fun hf hg i => (hf i).add (hg i)
  smul_mem' := fun c _ hf i => (hf i).comp_left (smul_zero c)

abbrev CompactSchwartzComponents (ι : Type*) := ↥(compactSchwartzComponents ι)

def compactComponentsToL2 (ι : Type*) [Fintype ι] :
    CompactSchwartzComponents ι →ₗ[ℂ] PiLp 2 (fun _ : ι => ComplexL2 Space) :=
  ((WithLp.linearEquiv 2 ℂ (ι → ComplexL2 Space)).symm.toLinearMap.comp
    (LinearMap.pi fun i => (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)).toLinearMap.comp
      (LinearMap.proj i))).comp (compactSchwartzComponents ι).subtype

abbrev CompactMatrixTest (ι : Type*) [Fintype ι] := ↥(LinearMap.range (compactComponentsToL2 ι))

private theorem compactComponentsToL2_injective (ι : Type*) [Fintype ι] :
    Injective (compactComponentsToL2 ι) := by
  intro f g h
  apply Subtype.ext
  funext i
  exact SchwartzMap.injective_toLp 2 volume (congrArg (fun v : PiLp 2 (fun _ : ι => ComplexL2 Space) => v i) h)

def compactMatrixTestEquiv (ι : Type*) [Fintype ι] : CompactSchwartzComponents ι ≃ₗ[ℂ] CompactMatrixTest ι :=
  LinearEquiv.ofInjective (compactComponentsToL2 ι) (compactComponentsToL2_injective ι)

@[simp] theorem compactMatrixTestEquiv_inner {ι : Type*} [Fintype ι] (f g : CompactSchwartzComponents ι) :
    ⟪compactMatrixTestEquiv ι f, compactMatrixTestEquiv ι g⟫_ℂ =
      ∑ i, ∫ x, conj (f.val i x) * g.val i x := by
  change ⟪compactComponentsToL2 ι f, compactComponentsToL2 ι g⟫_ℂ = _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪(f.val i).toLp 2 volume, (g.val i).toLp 2 volume⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(f.val i).coeFn_toLp 2 volume, (g.val i).coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg, RCLike.inner_apply']

@[simp] theorem compactMatrixTestEquiv_norm {ι : Type*} [Fintype ι] (f : CompactSchwartzComponents ι) :
    ‖compactMatrixTestEquiv ι f‖ = matrixSchwartzL2Norm f.val := rfl

def compactTransportOp {ι : Type*} [Fintype ι]
    (A : CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι) :
    Op (CompactMatrixTest ι) :=
  (compactMatrixTestEquiv ι).toLinearMap.comp (A.comp (compactMatrixTestEquiv ι).symm.toLinearMap)

@[simp] theorem compactTransportOp_apply {ι : Type*} [Fintype ι]
    (A : CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι) (f : CompactSchwartzComponents ι) :
    compactTransportOp A (compactMatrixTestEquiv ι f) = compactMatrixTestEquiv ι (A f) := by
  simp [compactTransportOp]

def compactComponentDerivative {ι : Type*} (b : Fin 4) :
    CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι where
  toFun f := ⟨fun i => SchwartzMap.pderivCLM ℂ (coordinateDirection b) (f.val i), fun i =>
    (f.property i).of_isClosed_subset isClosed_closure (coordinateSchwartzDerivative_support_subset (f.val i) b)⟩
  map_add' f g := by
    apply Subtype.ext
    funext i
    exact map_add (SchwartzMap.pderivCLM ℂ (coordinateDirection b)) (f.val i) (g.val i)
  map_smul' c f := by
    apply Subtype.ext
    funext i
    exact map_smul (SchwartzMap.pderivCLM ℂ (coordinateDirection b)) c (f.val i)

theorem compactMatrixDerivative_isSkew {ι : Type*} [Fintype ι] (b : Fin 4) :
    IsSkew (compactTransportOp (compactComponentDerivative (ι := ι) b)) := by
  intro u v
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  obtain ⟨g, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_inner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let e := coordinateDirection b
  have h := Burnett.Analysis.SymmetricEnergy.schwartz_derivative_isSkew e
    (Burnett.Analysis.SymmetricEnergy.schwartzTestEquiv (f.val i))
    (Burnett.Analysis.SymmetricEnergy.schwartzTestEquiv (g.val i))
  simp only [Burnett.Analysis.SymmetricEnergy.schwartzDerivative,
    Burnett.Analysis.SymmetricEnergy.transportSchwartzOp_on_equiv,
    Burnett.Analysis.SymmetricEnergy.schwartzTestEquiv_inner, ContinuousLinearMap.coe_coe] at h
  simpa only [RCLike.inner_apply', compactComponentDerivative, e] using h

end Burnett.Analysis.CarlesonEmbedding
