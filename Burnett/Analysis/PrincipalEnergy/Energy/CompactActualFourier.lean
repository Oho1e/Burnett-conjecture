import Burnett.Analysis.PrincipalEnergy.Energy.CompactSchwartzDomain
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalOrderOneSmoothAction
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCoordinateActionBounds
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalFiniteMatrixCoefficient

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection coordinateH1)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff

/-- The global symbol hypotheses needed by the actual compact test action. -/
structure GlobalMatrixSymbolData {ι : Type*} (a : ι → ι → Space → Space → ℂ) : Prop where
  frequency : ∀ i j, FirstBaseFrequencyOrderOne (a i j)
  smooth : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j))
  pureBase : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖)
  proper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j))

private theorem actualMatrixOutput_hasCompactSupport {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (f : CompactSchwartzComponents ι) (i : ι) : HasCompactSupport (matrixFirstOrderAction a f.val i) := by
  choose K hK _ hOut using fun j => exists_firstOrderAction_support_of_properSupport
    (ha.frequency i j).frequency (ha.proper i j) (f.val j) (f.property j)
  let S := ⋃ j, K j
  have hS : IsCompact S := isCompact_iUnion hK
  refine hS.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => ?_) hS.isClosed)
  by_contra hOutS
  apply hx
  refine Finset.sum_eq_zero fun j _ => ?_
  by_contra hne
  exact hOutS (mem_iUnion.mpr ⟨j, hOut j (subset_closure hne)⟩)

private theorem actualMatrixOutput_smooth {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (f : CompactSchwartzComponents ι) (i : ι) : ContDiff ℝ ∞ (matrixFirstOrderAction a f.val i) :=
  ContDiff.sum fun j _ => firstOrderAction_contDiff_of_pureBaseOrder (ha.smooth i j) (ha.pureBase i j) (f.val j)

private def actualMatrixOutput {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (f : CompactSchwartzComponents ι) : CompactSchwartzComponents ι :=
  ⟨fun i => (actualMatrixOutput_hasCompactSupport ha f i).toSchwartzMap (actualMatrixOutput_smooth ha f i),
    fun i => actualMatrixOutput_hasCompactSupport ha f i⟩

private theorem actualFirstOrderAction_add {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (u v : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction a (u+v : SchwartzMap Space ℂ) x = firstOrderAction a u x+firstOrderAction a v x := by
  simpa only [neg_one_smul, neg_one_mul, sub_neg_eq_add] using (firstOrderAction_sub_smul a ha x u v (-1))

private theorem actualFirstOrderAction_smul {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (u : SchwartzMap Space ℂ) (c : ℂ) (x : Space) :
    firstOrderAction a (c • u : SchwartzMap Space ℂ) x = c*firstOrderAction a u x := by
  have hZero : firstOrderAction a (0 : SchwartzMap Space ℂ) x = 0 := by
    simpa only [smul_zero, sub_self, one_mul] using firstOrderAction_sub_smul a ha x (0 : SchwartzMap Space ℂ) 0 1
  simpa only [neg_smul, sub_neg_eq_add, zero_add, neg_mul, hZero] using
    (firstOrderAction_sub_smul a ha x (0 : SchwartzMap Space ℂ) u (-c))

/-- The exact original matrix Fourier quantization on compact Schwartz data. -/
def compactActualFourierOp {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a) :
    CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι where
  toFun := actualMatrixOutput ha
  map_add' f g := by
    apply Subtype.ext
    funext i
    ext x
    change (∑ j, firstOrderAction (a i j) (f.val j+g.val j : SchwartzMap Space ℂ) x) =
      (∑ j, firstOrderAction (a i j) (f.val j) x)+(∑ j, firstOrderAction (a i j) (g.val j) x)
    simp only [actualFirstOrderAction_add (ha.frequency i _).frequency, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    funext i
    ext x
    change (∑ j, firstOrderAction (a i j) (c • f.val j : SchwartzMap Space ℂ) x) =
      c*(∑ j, firstOrderAction (a i j) (f.val j) x)
    simp only [actualFirstOrderAction_smul (ha.frequency i _).frequency, Finset.mul_sum]

@[simp] theorem compactActualFourierOp_apply {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    (compactActualFourierOp ha f).val i x = matrixFirstOrderAction a f.val i x := rfl

theorem compactActualFourierOp_isSymmetric {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : GlobalMatrixSymbolData a)
    (hSym : MatrixFirstOrderFormalSymmetry a) :
    (compactTransportOp (compactActualFourierOp ha)).IsSymmetric := by
  intro u v
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  obtain ⟨g, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_inner, compactActualFourierOp_apply]
  exact (hSym g.val f.val).symm

end Burnett.Analysis.CarlesonEmbedding
