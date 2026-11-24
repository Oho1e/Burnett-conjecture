import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeCoordinates
import Burnett.Geometry.ContravariantTensor

set_option autoImplicit false
set_option maxRecDepth 2300
set_option maxHeartbeats 1500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Module Matrix Burnett.RicciSymbol
open Burnett.Geometry
open Burnett.Geometry.ContravariantTensor (dualBilinearContraction dualBilinearContraction_eq_sum)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeTensor)
open scoped BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real bilinear form with complex values. -/
abbrev ComplexBilinearForm (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] V →ₗ[ℝ] ℂ

/-- The two free covariant slots of an amplitude with its last two slots fixed. -/
def amplitudeSlice (A : AmplitudeTensor V) (s t : V) : ComplexBilinearForm V :=
  LinearMap.mk₂ ℝ (fun u w => A ![u, w, s, t])
    (fun u u' w => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        A.map_update_add ![0, w, s, t] (0 : Fin 4) u u')
    (fun a u w => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        A.map_update_smul ![0, w, s, t] (0 : Fin 4) a u)
    (fun u w w' => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        A.map_update_add ![u, 0, s, t] (0 : Fin 3).succ w w')
    (fun a u w => by
      simpa only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
        A.map_update_smul ![u, 0, s, t] (0 : Fin 3).succ a w)

theorem amplitudeSlice_apply (A : AmplitudeTensor V) (s t u w : V) :
    amplitudeSlice A s t u w = A ![u, w, s, t] := rfl

variable [FiniteDimensional ℝ V]

/-- Contract the real and imaginary parts against the same inverse metric tensor. -/
def complexFiberTrace (Q : LinearMap.BilinForm ℝ (Dual ℝ V)) (k : ComplexBilinearForm V) : ℂ :=
  ⟨dualBilinearContraction Q (k.compr₂ Complex.reLm),
    dualBilinearContraction Q (k.compr₂ Complex.imLm)⟩

theorem complexFiberTrace_eq_complexMetricTrace (b : Basis Index ℝ V)
    (Q : LinearMap.BilinForm ℝ (Dual ℝ V)) (k : ComplexBilinearForm V) :
    complexFiberTrace Q k =
      complexMetricTrace (fun i j => Q (b.dualBasis i) (b.dualBasis j)) (fun i j => k (b i) (b j)) := by
  apply Complex.ext <;>
    simp [complexFiberTrace, dualBilinearContraction_eq_sum b, metricTrace, tensorRe, tensorIm]

/-- The inverse bilinear form on the algebraic dual from the metric's lowering equivalence. -/
def fiberInverseForm (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate) :
    LinearMap.BilinForm ℝ (Dual ℝ V) :=
  let s := (g.toDual hg).symm.toLinearMap
  g.compl₁₂ s s

theorem fiberInverseForm_eq_contravariant (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (b : Basis Index ℝ V) (i j : Index) :
    fiberInverseForm g hg (b.dualBasis i) (b.dualBasis j) = FiberMetric.contravariant g hg b i j := by
  simp only [fiberInverseForm, FiberMetric.contravariant, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearMap.BilinForm.dualBasis, Basis.map_apply]

/-- The intrinsic complexified Ricci principal symbol at an actual fiber covector. -/
def complexFiberRicciSymbol (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (η : Dual ℝ V) (k : ComplexBilinearForm V) : ComplexBilinearForm V :=
  let v := (g.toDual hg).symm η
  let tr := complexFiberTrace (fiberInverseForm g hg) k
  let f (u w : V) : ℂ := ((η v : ℂ) * k u w + (η u : ℂ) * η w * tr -
      (η u : ℂ) * k v w - (η w : ℂ) * k v u) / 2
  LinearMap.mk₂ ℝ f
    (fun u u' w => by
      simp only [f, map_add, LinearMap.add_apply, Complex.ofReal_add]
      ring)
    (fun a u w => by
      simp only [f, map_smul, LinearMap.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
      ring)
    (fun u w w' => by
      simp only [f, map_add, Complex.ofReal_add]
      ring)
    (fun a u w => by
      simp only [f, map_smul, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
      ring)

theorem complexFiberRicciSymbol_apply (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (η : Dual ℝ V) (k : ComplexBilinearForm V) (u w : V) :
    let v := (g.toDual hg).symm η
    complexFiberRicciSymbol g hg η k u w =
      ((η v : ℂ) * k u w + (η u * η w) • complexFiberTrace (fiberInverseForm g hg) k -
        (η u : ℂ) * k v w - (η w : ℂ) * k v u) / 2 := by
  intro v
  simp only [Complex.real_smul, Complex.ofReal_mul]
  rfl

private theorem complexContracted_eq_sharp (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (η : Dual ℝ V) (k : ComplexBilinearForm V) (b : Basis Index ℝ V) (j : Index) :
    complexContracted (FiberMetric.contravariant g hg b) (FiberMetric.covector b η)
      (fun i j => k (b i) (b j)) j = k ((g.toDual hg).symm η) (b j) := by
  have h := congrArg (fun x => k x (b j)) (b.sum_repr ((g.toDual hg).symm η))
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Complex.real_smul] at h
  rw [complexContracted, FiberMetric.raiseCovector_eq_sharp]
  exact h

/-- The old coordinate symbol and the actual fiber symbol have exactly the same entries. -/
theorem complexFiberRicciSymbol_eq_basis (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (η : Dual ℝ V) (k : ComplexBilinearForm V) (b : Basis Index ℝ V) (i j : Index) :
    complexFiberRicciSymbol g hg η k (b i) (b j) =
      complexRicciSymbol (FiberMetric.contravariant g hg b) (FiberMetric.covector b η)
        (fun a c => k (b a) (b c)) i j := by
  rw [complexFiberRicciSymbol_apply, complexRicciSymbol,
    FiberMetric.symbolNorm_eq_eval_sharp, complexFiberTrace_eq_complexMetricTrace b]
  simp only [fiberInverseForm_eq_contravariant, complexContracted_eq_sharp, FiberMetric.covector,
    FiberMetric.sharp, Complex.real_smul, Complex.ofReal_mul]

end Burnett.Microlocal.Overlap
