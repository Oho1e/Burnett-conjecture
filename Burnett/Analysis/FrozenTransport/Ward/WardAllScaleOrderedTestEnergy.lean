import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleScalarTestPlacements
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleOrderedVertex
import Burnett.Analysis.FrozenTransport.FrozenCubicOddTest

set_option autoImplicit false
set_option maxRecDepth 6800
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V08 (signedCyclicPhase)
open scoped ComplexConjugate FourierTransform

def wardRealEnergySpectrum (u : RealEnergyField OrderedPair) (p : E) : ComplexTensor2 :=
  fun i j => radianFourier (u.1 (i,j)) p

private def wardEntryTestWeight (b : E → ℝ) (u : RealEnergyField OrderedPair)
    (k : WardActionEntry) (x : Joint) : ℂ :=
  let p := x.1
  let q := x.2
  let r := -(p+q)
  Complex.I * (signedCyclicPhase b p q : ℂ) * radianFourier (u.1 k.1) p *
    ((q k.2.1.1 : ℂ) * radianFourier (u.1 k.2.1.2) q) *
    ((r k.2.2.1 : ℂ) * radianFourier (u.1 k.2.2.2) r)

private def wardEntryPositionTest (b : E → ℝ) (u : RealEnergyField OrderedPair) (k : WardActionEntry) : ℝ :=
  let f := u.1 k.1
  let g := energyPartial k.2.1.1 (u.1 k.2.1.2)
  let h := energyPartial k.2.2.1 (u.1 k.2.2.2)
  (∫ x, (g x * h x) * (-Complex.I * radianAction b f x)).re +
    (∫ x, (f x * h x) * (-Complex.I * radianAction b g x)).re +
    (∫ x, (f x * g x) * (-Complex.I * radianAction b h x)).re

private theorem wardEntryTestWeight_eq_position (b : E → ℝ)
    (u : RealEnergyField OrderedPair) (k : WardActionEntry)
    (hInt : ∀ f : SchwartzMap E ℂ, Integrable (radianActionSpectrum b f)) :
    Integrable (wardEntryTestWeight b u k) ∧
      (((tau^8)⁻¹ : ℝ) • (∫ p, wardEntryTestWeight b u k p)).re = wardEntryPositionTest b u k := by
  let f := u.1 k.1
  let g := energyPartial k.2.1.1 (u.1 k.2.1.2)
  let h := energyPartial k.2.2.1 (u.1 k.2.2.2)
  let A (p : Joint) := (signedCyclicPhase b p.1 p.2 : ℂ)
  have hC := wardScalarActionCyclicPlacements b f g h (hInt f) (hInt g) (hInt h)
  have hg (ξ : E) : radianFourier g ξ =
      Complex.I * (ξ k.2.1.1 : ℂ) * radianFourier (u.1 k.2.1.2) ξ :=
    Burnett.A07.radianFourier_coordinateDerivative _ _ _
  have hh (ξ : E) : radianFourier h ξ =
      Complex.I * (ξ k.2.2.1 : ℂ) * radianFourier (u.1 k.2.2.2) ξ :=
    Burnett.A07.radianFourier_coordinateDerivative _ _ _
  have hW : wardEntryTestWeight b u k =
      fun p => -Complex.I * radianTrilinearWeight A f g h p := by
    funext p
    let r := -(p.1+p.2)
    let P := radianFourier f p.1
    let Q := (p.2 k.2.1.1 : ℂ) * radianFourier (u.1 k.2.1.2) p.2
    let R := (r k.2.2.1 : ℂ) * radianFourier (u.1 k.2.2.2) r
    simp only [radianTrilinearWeight, radianWeight, Complex.ofReal_one, one_mul]
    change Complex.I * A p * P * Q * R =
      -Complex.I * (A p * (P * radianFourier g p.2 * radianFourier h r))
    rw [hg,hh]
    calc
      _ = (-Complex.I) * (Complex.I * Complex.I) * A p * P * Q * R := by rw [Complex.I_mul_I]; ring
      _ = _ := by dsimp only [Q,R]; ring
  refine ⟨hW.symm ▸ hC.1.const_mul _, ?_⟩
  have hForm : ((tau^8)⁻¹ : ℝ) • (∫ p, wardEntryTestWeight b u k p) =
      -Complex.I * radianTrilinearForm A f g h := by
    rw [hW, integral_const_mul, radianTrilinearForm]
    simp only [Complex.real_smul]
    ring
  have place (F G H : SchwartzMap E ℂ) :
      (∫ x, G x * H x * (-Complex.I * radianAction b F x)) =
        -Complex.I * (∫ x, radianAction b F x * G x * H x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => by ring
  have place' (F G H : SchwartzMap E ℂ) :
      (∫ x, H x * G x * (-Complex.I * radianAction b F x)) =
        -Complex.I * (∫ x, radianAction b F x * G x * H x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => by ring
  rw [hForm, ← hC.2]
  change _ = (∫ x, g x * h x * (-Complex.I * radianAction b f x)).re +
    (∫ x, f x * h x * (-Complex.I * radianAction b g x)).re +
    (∫ x, f x * g x * (-Complex.I * radianAction b h x)).re
  rw [place f g h, place' g h f, place h f g]
  rw [mul_add, mul_add, Complex.add_re, Complex.add_re]

private def wardPositionEntryEquiv : WardActionEntry ≃ CubicLinearIndex OrderedPair where
  toFun k := (((k.2.1.1,k.2.2.1),(k.2.1.2,k.2.2.2)),k.1)
  invFun k := (k.2, (k.1.1.1,k.1.2.1), (k.1.1.2,k.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual coordinate-array weight with the undifferentiated
amplitude in the first slot and all three exact test placements. -/
def wardOrderedCyclicTestWeight (G : Mat) (b : E → ℝ) (U : E → ComplexTensor2)
    (x : Joint) : ℂ :=
  let p := x.1
  let q := x.2
  let r := -(p+q)
  Complex.I * (signedCyclicPhase b p q : ℂ) *
    wardOrderedPrincipalLeg G (U p) (fun i => q i) (fun i => r i) (U q) (U r)

theorem wardOrderedCyclicTestWeight_eq_position (G : Mat) (b : E → ℝ) (u : RealEnergyField OrderedPair)
    (hInt : ∀ f : SchwartzMap E ℂ, Integrable (radianActionSpectrum b f)) :
    let W := wardOrderedCyclicTestWeight G b (wardRealEnergySpectrum u)
    Integrable W ∧
      (((tau^8)⁻¹ : ℝ) • (∫ x, W x)).re = frozenActionCyclicOddTestEnergy G b u := by
  intro W
  let C (k : WardActionEntry) := wardActionEntryCoefficient G k
  let F (k : WardActionEntry) (p : Joint) := (C k : ℂ) * wardEntryTestWeight b u k p
  have hF (k : WardActionEntry) : Integrable (F k) :=
    (wardEntryTestWeight_eq_position b u k hInt).1.const_mul _
  have hW : W = fun p => ∑ k, F k p := by
    funext p
    simp only [W, wardOrderedCyclicTestWeight, wardOrderedPrincipalLeg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [F, C, wardEntryTestWeight, wardRealEnergySpectrum]
    ring
  refine ⟨hW.symm ▸ integrable_finset_sum Finset.univ (fun k _ => hF k), ?_⟩
  rw [hW, integral_finset_sum _ (fun k _ => hF k), Finset.smul_sum, Complex.re_sum]
  have term (k : WardActionEntry) :
      (((tau^8)⁻¹ : ℝ) • (∫ p, F k p)).re = C k * wardEntryPositionTest b u k := by
    simp only [F, integral_const_mul, Complex.real_smul]
    rw [mul_left_comm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (fun r : ℝ => C k * r) (wardEntryTestWeight_eq_position b u k hInt).2
  simp only [term]
  unfold frozenActionCyclicOddTestEnergy
  exact Fintype.sum_equiv wardPositionEntryEquiv _ _ (fun _ => rfl)

end Burnett.C02
