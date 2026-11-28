import Burnett.Analysis.TransportWard.Weyl.ComplexEulerFormalSymmetry
import Burnett.Analysis.TransportWard.Weyl.ActualEulerWeylCoefficientPacket
import Burnett.Analysis.PrincipalEnergy.Commutator.RenormalizedKernel
import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2500

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Burnett.Geometry ConnectionDifference Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Analysis.FirstOrderDyadic (scalarSchwartzProduct scalarSchwartzProduct_apply)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff BigOperators

local notation "E₀" => CoordinateSpace
local notation "J" => Fin 4 × Fin 4
local notation "D" => fun j : Fin 4 => SchwartzMap.pderivCLM ℂ (coordinateDirection j)

/-- The three differential orders of the same actual linearized Euler
action, represented on the Schwartz field components. -/
def schwartzComplexEulerCoefficientAction {ι : Type*} [Fintype ι]
    (c₀ : ι → ι → SchwartzMap E₀ ℂ) (c₁ : ι → ActionSlot ι → SchwartzMap E₀ ℂ)
    (c₂ : ι → ι → J → SchwartzMap E₀ ℂ) (u : ι → SchwartzMap E₀ ℂ) (i : ι) :
    SchwartzMap E₀ ℂ :=
  ((∑ j, scalarSchwartzProduct (c₀ i j) (u j)) +
    ∑ s : ActionSlot ι, scalarSchwartzProduct (c₁ i s) (D s.1 (u s.2))) -
    ∑ a, ∑ s : ActionSlot ι, scalarSchwartzProduct (c₂ i s.2 (a,s.1)) (D a (D s.1 (u s.2)))

private theorem continuous_coordinateProjection_derivative (L : ℂ →L[ℝ] ℝ)
    (f : SchwartzMap E₀ ℂ) (x : E₀) (j : Fin 4) :
    fderiv ℝ (fun y => L (f y)) x (coordinateBasis j) = L (D j f x) := by
  have h := (L.hasFDerivAt.comp x (f.differentiable x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => L (f y)) x = _ at h
  rw [h,ContinuousLinearMap.comp_apply,SchwartzMap.pderivCLM_apply]
  exact congrArg (fun e => L (fderiv ℝ (f : E₀ → ℂ) x e)) (EuclideanSpace.basisFun_apply _ _ j)

private theorem coordinateMetricFirstJet_schwartzProjection {ι : Type*} [Fintype ι]
    (L : ℂ →L[ℝ] ℝ) (u : ι → SchwartzMap E₀ ℂ) (x : E₀) (s : ActionSlot ι) :
    coordinateMetricFirstJet (fun y j => L (u j y)) x s = L (D s.1 (u s.2) x) := by
  let f (y : E₀) (j : ι) := L (u j y)
  let R : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj s.2
  have hf : ContDiff ℝ ∞ f :=
    contDiff_pi.mpr (fun j => L.contDiff.comp (u j).smooth')
  have h := (R.hasFDerivAt.comp x ((hf.differentiable (by simp)) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => L (u s.2 y)) x = R.comp (fderiv ℝ f x) at h
  change R (fderiv ℝ f x (coordinateBasis s.1)) = _
  rw [← ContinuousLinearMap.comp_apply,← h]
  exact continuous_coordinateProjection_derivative L (u s.2) x s.1

private theorem coordinateMetricSecondJet_schwartzProjection {ι : Type*} [Fintype ι]
    (L : ℂ →L[ℝ] ℝ) (u : ι → SchwartzMap E₀ ℂ) (x : E₀) (a : Fin 4) (s : ActionSlot ι) :
    coordinateMetricSecondJet (fun y j => L (u j y)) x a s = L (D a (D s.1 (u s.2)) x) := by
  have he : (fun y => coordinateMetricFirstJet (fun z j => L (u j z)) y s) =
      fun y => L (D s.1 (u s.2) y) :=
    funext (fun y => coordinateMetricFirstJet_schwartzProjection L u y s)
  rw [coordinateMetricSecondJet,he]
  exact continuous_coordinateProjection_derivative L (D s.1 (u s.2)) x a

private theorem evaluate_schwartz_finset_sum {κ : Type*} (s : Finset κ)
    (F : κ → SchwartzMap E₀ ℂ) (x : E₀) :
    ((∑ j ∈ s, F j : SchwartzMap E₀ ℂ) x) = ∑ j ∈ s, F j x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [Finset.sum_insert,hj,SchwartzMap.add_apply,ih]

private theorem coefficient_sum_complex_of_re_im {κ : Type*} [Fintype κ]
    (c z : κ → ℂ) :
    (∑ j, c j * z j) = (∑ j, c j * ((z j).re : ℂ)) +
      Complex.I * ∑ j, c j * ((z j).im : ℂ) := by
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  linear_combination c j * (Complex.re_add_im (z j)).symm

/-- On the actual chart neighborhood the Schwartz coefficient action
represents the complexification of the same intrinsic Euler variation. -/
theorem schwartzComplexEulerCoefficientAction_eq_complexified {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) (U : Set E₀) (x : E₀) (i : ι)
    (c₀ : ι → ι → SchwartzMap E₀ ℂ) (c₁ : ι → ActionSlot ι → SchwartzMap E₀ ℂ)
    (c₂ : ι → ι → J → SchwartzMap E₀ ℂ)
    (hAt : ∀ h : E₀ → ι → ℝ, ContDiffOn ℝ ∞ h U →
      (linearizedCoordinateDensityEuler S g h x i : ℂ) =
        ((∑ j, (h x j : ℂ) * c₀ i j x) + ∑ s : ActionSlot ι, (coordinateMetricFirstJet h x s : ℂ) * c₁ i s x) -
          ∑ a, ∑ s : ActionSlot ι, c₂ i s.2 (a,s.1) x * (coordinateMetricSecondJet h x a s : ℂ))
    (u : ι → SchwartzMap E₀ ℂ) :
    schwartzComplexEulerCoefficientAction c₀ c₁ c₂ u i x =
      complexLinearizedCoordinateDensityEuler S g (fun y j => u j y) x i := by
  let r (y : E₀) (j : ι) := (u j y).re
  let q (y : E₀) (j : ι) := (u j y).im
  have hr : ContDiff ℝ ∞ r := contDiff_pi.mpr (fun j => Complex.reCLM.contDiff.comp (u j).smooth')
  have hq : ContDiff ℝ ∞ q := contDiff_pi.mpr (fun j => Complex.imCLM.contDiff.comp (u j).smooth')
  have hR := hAt r hr.contDiffOn
  have hQ := hAt q hq.contDiffOn
  have hJ (L : ℂ →L[ℝ] ℝ) (s : ActionSlot ι) := coordinateMetricFirstJet_schwartzProjection L u x s
  have hK (L : ℂ →L[ℝ] ℝ) (a : Fin 4) (s : ActionSlot ι) := coordinateMetricSecondJet_schwartzProjection L u x a s
  rw [show complexLinearizedCoordinateDensityEuler S g (fun y j => u j y) x i =
      (linearizedCoordinateDensityEuler S g r x i : ℂ) +
        Complex.I * (linearizedCoordinateDensityEuler S g q x i : ℂ) by
    apply Complex.ext <;> simp [complexLinearizedCoordinateDensityEuler,r,q,Complex.mul_re,Complex.mul_im]]
  rw [hR,hQ]
  have hJr (s : ActionSlot ι) : coordinateMetricFirstJet r x s = (D s.1 (u s.2) x).re :=
    hJ Complex.reCLM s
  have hJq (s : ActionSlot ι) : coordinateMetricFirstJet q x s = (D s.1 (u s.2) x).im :=
    hJ Complex.imCLM s
  have hKr (a : Fin 4) (s : ActionSlot ι) : coordinateMetricSecondJet r x a s = (D a (D s.1 (u s.2)) x).re :=
    hK Complex.reCLM a s
  have hKq (a : Fin 4) (s : ActionSlot ι) : coordinateMetricSecondJet q x a s = (D a (D s.1 (u s.2)) x).im :=
    hK Complex.imCLM a s
  simp only [hJr,hJq,hKr,hKq,schwartzComplexEulerCoefficientAction,SchwartzMap.sub_apply,
    SchwartzMap.add_apply,evaluate_schwartz_finset_sum,scalarSchwartzProduct_apply,r,q]
  have h₀ := coefficient_sum_complex_of_re_im (fun j => c₀ i j x) (fun j => u j x)
  have h₁ := coefficient_sum_complex_of_re_im (fun s : ActionSlot ι => c₁ i s x)
    (fun s => D s.1 (u s.2) x)
  have h₂ (a : Fin 4) := coefficient_sum_complex_of_re_im (fun s : ActionSlot ι => c₂ i s.2 (a,s.1) x)
    (fun s => D a (D s.1 (u s.2)) x)
  simp_rw [h₀,h₁,h₂]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hSwap (z : E₀ → ι → ℝ) : (∑ j, (z x j : ℂ) * c₀ i j x) =
      ∑ j, c₀ i j x * (z x j : ℂ) :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have h₁r : (∑ s : ActionSlot ι, ((D s.1 (u s.2) x).re : ℂ) * c₁ i s x) =
      ∑ s : ActionSlot ι, c₁ i s x * ((D s.1 (u s.2) x).re : ℂ) :=
    Finset.sum_congr rfl (fun s _ => mul_comm _ _)
  have h₁q : (∑ s : ActionSlot ι, ((D s.1 (u s.2) x).im : ℂ) * c₁ i s x) =
      ∑ s : ActionSlot ι, c₁ i s x * ((D s.1 (u s.2) x).im : ℂ) :=
    Finset.sum_congr rfl (fun s _ => mul_comm _ _)
  rw [show (∑ j, ((u j x).re : ℂ) * c₀ i j x) = _ from hSwap r,
    show (∑ j, ((u j x).im : ℂ) * c₀ i j x) = _ from hSwap q,h₁r,h₁q]
  ring

end Burnett.V03.Palatini
