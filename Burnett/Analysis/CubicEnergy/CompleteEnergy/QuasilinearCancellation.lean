import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutator

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff

/-- Two coordinate indices and two indices of the finite field space. -/
abbrev EnergyIndex (J : Type*) := (Index × Index) × (J × J)

private def energySwap (J : Type*) : EnergyIndex J ≃ EnergyIndex J :=
  Equiv.prodCongr (Equiv.prodComm Index Index) (Equiv.prodComm J J)

private theorem energy_conj_integrable {F : E → ℂ} (hF : Integrable F) :
    Integrable (fun x => conj (F x)) :=
  hF.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hF.1)
    (Filter.Eventually.of_forall fun _ => by simp)

/-- The quasilinear pairing with both differentiations on the field. -/
def quasilinearPairing {J : Type*} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ) : ℂ :=
  ∑ k : EnergyIndex J, ∫ x, A k x *
    energyPartial k.1.1 (energyPartial k.1.2 (u k.2.2)) x *
    conj (radianAction b (u k.2.1) x)

/-- The term where one coordinate derivative falls on the coefficient. -/
def quasilinearCoefficientPairing {J : Type*} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ) : ℂ :=
  ∑ k : EnergyIndex J, ∫ x, energyPartial k.1.1 (A k) x *
    energyPartial k.1.2 (u k.2.2) x * conj (radianAction b (u k.2.1) x)

/-- The first-order commutator with one coordinate derivative on each field. -/
def quasilinearCommutatorPairing {J : Type*} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ) : ℂ :=
  ∑ k : EnergyIndex J, ∫ x, radianCommutator b (A k) (energyPartial k.1.2 (u k.2.2)) x *
    conj (energyPartial k.1.1 (u k.2.1) x)

private def derivativePairing {J : Type*} (b : E → ℝ) (A : EnergyIndex J → SchwartzMap E ℂ)
    (u : J → SchwartzMap E ℂ) (k : EnergyIndex J) (x : E) : ℂ :=
  A k x * energyPartial k.1.2 (u k.2.2) x *
    conj (radianAction b (energyPartial k.1.1 (u k.2.1)) x)

private theorem derivativePairing_integrable {J : Type*} (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ) (k : EnergyIndex J) :
    Integrable (derivativePairing b A u k) := by
  simpa only [derivativePairing, energyProduct_apply] using
    radian_order_one_test_integrable b hb hom (energyProduct (A k) (energyPartial k.1.2 (u k.2.2)))
      (energyPartial k.1.1 (u k.2.1))

private theorem commutatorPairing_component {J : Type*} (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ)
    (hA : ∀ a d i j x, conj (A ((a,d),(i,j)) x) = A ((d,a),(j,i)) x)
    (k : EnergyIndex J) :
    (∫ x, radianCommutator b (A k) (energyPartial k.1.2 (u k.2.2)) x *
      conj (energyPartial k.1.1 (u k.2.1) x)) =
      (∫ x, derivativePairing b A u k x) -
        conj (∫ x, derivativePairing b A u (energySwap J k) x) := by
  rcases k with ⟨⟨a,d⟩,i,j⟩
  let U := energyPartial d (u j)
  let V := energyPartial a (u i)
  let F := energyProduct (A ((a,d),(i,j))) U
  let w := derivativePairing b A u ((a,d),(i,j))
  let wSwap := derivativePairing b A u ((d,a),(j,i))
  change (∫ x, radianCommutator b (A ((a,d),(i,j))) U x * conj (V x)) =
    (∫ x, w x) - conj (∫ x, wSwap x)
  have hwSwap (x : E) :
      conj (wSwap x) = A ((a,d),(i,j)) x * radianAction b U x * conj (V x) := by
    simp only [wSwap, derivativePairing, map_mul, hA d a j i, starRingEnd_self_apply, U, V]
    ring
  have hF : Integrable (fun x => radianAction b F x * conj (V x)) := by
    have hc := energy_conj_integrable (radian_order_one_test_integrable b hb hom V F)
    simpa only [map_mul, starRingEnd_self_apply, mul_comm] using hc
  have hSwap : Integrable (fun x => A ((a,d),(i,j)) x * radianAction b U x * conj (V x)) := by
    have hc := energy_conj_integrable
      (derivativePairing_integrable b hb hom A u ((d,a),(j,i)))
    simpa only [← hwSwap] using hc
  calc
    _ = (∫ x, radianAction b F x * conj (V x) -
        A ((a,d),(i,j)) x * radianAction b U x * conj (V x)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (radianAction b F x - A ((a,d),(i,j)) x * radianAction b U x) *
          conj (V x) = _
        exact sub_mul _ _ _
    _ = _ := by
      rw [integral_sub hF hSwap, radian_order_one_self_adjoint b hb hom,
        ← integral_conj]
      simp only [hwSwap]
      rfl

/-- In the complete paired sum, the Hermitian symmetry of the coefficient
converts the imaginary part into a first-order commutator and a single
coefficient derivative. The real symmetric coefficient is a special case. -/
theorem quasilinear_imaginary_identity {J : Type*} [Fintype J] (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ)
    (hA : ∀ a d i j x, conj (A ((a,d),(i,j)) x) = A ((d,a),(j,i)) x) :
    2 * (quasilinearPairing b A u).im =
      -(quasilinearCommutatorPairing b A u).im - 2 * (quasilinearCoefficientPairing b A u).im := by
  classical
  let w (k : EnergyIndex J) := ∫ x, derivativePairing b A u k x
  let W := ∑ k : EnergyIndex J, w k
  have ibp : quasilinearPairing b A u = -W - quasilinearCoefficientPairing b A u := by
    unfold quasilinearPairing quasilinearCoefficientPairing W
    simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact quasilinear_component_ibp b hb hom k.1.1 k.1.2 (A k) (u k.2.2) (u k.2.1)
  have reindex : (∑ k : EnergyIndex J, conj (w (energySwap J k))) = ∑ k, conj (w k) :=
    Fintype.sum_equiv (energySwap J) _ _ (fun _ => rfl)
  have comm : quasilinearCommutatorPairing b A u = W - conj W := by
    unfold quasilinearCommutatorPairing W
    rw [map_sum, ← reindex, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact commutatorPairing_component b hb hom A u hA k
  rw [ibp, comm, Complex.sub_im, Complex.neg_im, Complex.sub_im, Complex.conj_im]
  ring

end Burnett.A02.FrequencySplit
