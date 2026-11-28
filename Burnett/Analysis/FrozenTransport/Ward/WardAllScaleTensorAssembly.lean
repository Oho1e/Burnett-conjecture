import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualPhasePatch
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 11900000

noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Set Burnett.Fourier Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ContDiff Topology

open private wardTensorBasis_expand from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensor

abbrev WardTensorTrilinear := MultilinearMap ℂ (fun _ : Fin 3 => ComplexComponents) ℂ

/-- Expand all ordered entries of each of the three actual Fourier slots. -/
theorem wardTensorTrilinear_expand (A : WardTensorTrilinear) (H : Fin 3 → ComplexComponents) :
    A H = ∑ k : Fin 3 → OrderedPair,
      A (fun j => wardTensorBasis (k j)) * ∏ j, H j (k j).1 (k j).2 := by
  calc
    _ = A (fun j => ∑ a : OrderedPair, H j a.1 a.2 • wardTensorBasis a) := by
      congr 1
      funext j
      exact wardTensorBasis_expand (H j)
    _ = _ := by
      rw [MultilinearMap.map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]

def wardActualTensorWeight (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (x : Joint) : ℂ :=
  A x (fun j a b => radianFourier (wardActualLowSlots m wi wo hm hη i o z physical (fun _ => (a,b)) j)
    (wardPhaseCovector x j))

def wardActualTensorForm (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) : ℂ :=
  (tau^8)⁻¹ • (∫ x, wardActualTensorWeight m physical A wi wo hm hη i o z x)

private theorem wardActualTensorWeight_eq_sum (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (x : Joint) :
    wardActualTensorWeight m physical A wi wo hm hη i o z x =
      ∑ k : Fin 3 → OrderedPair,
        let f := wardActualLowSlots m wi wo hm hη i o z physical k
        radianTrilinearWeight (fun y => A y (fun j => wardTensorBasis (k j))) (f 0) (f 1) (f 2) x := by
  rw [wardActualTensorWeight, wardTensorTrilinear_expand]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fin.prod_univ_three, radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul,
    wardPhaseCovector, Matrix.cons_val_zero, Matrix.cons_val_one, wardActualLowSlots]
  rfl

/-- The tensor form is exactly the finite integral sum of the same scalar
component forms, with the original Fourier normalization. -/
theorem wardActualTensorForm_eq_sum (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (C : (Fin 3 → OrderedPair) → ℝ)
    (hA : ∀ k, WardActualLowComponentBound m physical k (fun y => A y (fun j => wardTensorBasis (k j))) (C k))
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    Integrable (wardActualTensorWeight m physical A wi wo hm hη i o z) ∧
    wardActualTensorForm m physical A wi wo hm hη i o z =
      ∑ k : Fin 3 → OrderedPair, let f := wardActualLowSlots m wi wo hm hη i o z physical k
        radianTrilinearForm (fun y => A y (fun j => wardTensorBasis (k j))) (f 0) (f 1) (f 2) := by
  let W k :=
    let f := wardActualLowSlots m wi wo hm hη i o z physical k
    radianTrilinearWeight (fun y => A y (fun j => wardTensorBasis (k j))) (f 0) (f 1) (f 2)
  have hInt (k : Fin 3 → OrderedPair) : Integrable (W k) := (hA k wi wo hm η hη i o z).1
  have hW : wardActualTensorWeight m physical A wi wo hm hη i o z = fun x => ∑ k, W k x :=
    funext (wardActualTensorWeight_eq_sum m physical A wi wo hm hη i o z)
  refine ⟨hW.symm ▸ integrable_finset_sum Finset.univ (fun k _ => hInt k), ?_⟩
  change (tau^8)⁻¹ • (∫ x, wardActualTensorWeight m physical A wi wo hm hη i o z x) =
    ∑ k : Fin 3 → OrderedPair, (tau^8)⁻¹ • (∫ x, W k x)
  rw [hW, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun k _ => hInt k)]

/-- The finite ordered tensor sum has the original patch volume and the
same two C02 physical differences and genuine C03 input bound. -/
theorem wardActualTensorForm_patch_bound (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (C : (Fin 3 → OrderedPair) → ℝ)
    (hC : ∀ k, 0 ≤ C k)
    (hA : ∀ k, WardActualLowComponentBound m physical k (fun y => A y (fun j => wardTensorBasis (k j))) (C k))
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
    (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E) (value : ℕ → ℝ) (grad Ce ell alpha : ℝ)
    (hCe : 0 ≤ Ce) (hEll : 0 < ell) (hEll₁ : ell ≤ 1) (hAlpha : 0 ≤ alpha)
    (hv : Tendsto value atTop (𝓝 0)) (hSource : ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) :
    let mass := ((volume : Measure E) P).toReal
    let M := mass ^ (1 / 3 : ℝ)
    let T := actualThinScreenMultiplier m wi wo hm hη i o
    let diff (n : ℕ) (b : Index × OrderedPair) :=
      multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b.1 b.2 -
        multiplierCoordinateDerivative T (z n) b.1 b.2
    let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar m)
      (multiplierCoordinateDerivative T (z n) b.1 b.2)
    (∀ ε > 0, ∀ᶠ n in atTop,
      (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε ∧
      (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε) →
    ∀ ε > 0, ∀ᶠ n in atTop,
      ‖wardActualTensorForm m physical A wi wo hm hη i o (z n)‖ ≤
        ((∑ k, C k) * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  classical
  intro mass M T diff phase hRate ε hε
  let g := Ce * (128 * grad + Ce)^2 * ell ^ alpha * mass
  let D : ℝ := Fintype.card (Fin 3 → OrderedPair)
  have hD : 0 < D := Nat.cast_pos.mpr Fintype.card_pos
  let f (n : ℕ) (k : Fin 3 → OrderedPair) := wardActualLowSlots m wi wo hm hη i o (z n) physical k
  let F (k : Fin 3 → OrderedPair) (y : Joint) := A y (fun j => wardTensorBasis (k j))
  have hLocal : ∀ᶠ n in atTop, ∀ k : Fin 3 → OrderedPair,
    ‖radianTrilinearForm (F k) (f n k 0) (f n k 1) (f n k 2)‖ ≤ C k * g + ε / D := by
    rw [Filter.eventually_all]
    intro k
    simpa only [F, f, g, mul_assoc] using
      wardActualPhaseComponent_patch_bound m physical k (F k) (C k) (hC k) (hA k)
        wi wo hm η hη i o z P value grad Ce ell alpha hCe hEll hEll₁ hAlpha hv hSource hRate (ε / D) (div_pos hε hD)
  filter_upwards [hLocal] with n hn
  rw [(wardActualTensorForm_eq_sum m physical A C hA wi wo hm hη i o (z n)).2]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hn k).trans_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (∑ k, C k) * g + D * (ε / D) = _
  rw [mul_div_cancel₀ _ hD.ne']
  simp only [g, mul_assoc]

end Burnett.C02
