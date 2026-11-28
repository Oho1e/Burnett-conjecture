import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators Burnett.A03

open private principal_variation_density_add from Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

/-- Terms in which a derivative lands on a spatial cutoff in the three
actual placements of the principal third variation. -/
def principalCubicCutoffJetError {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (χ : SchwartzMap E ℂ) (x : E) : ℂ :=
  let t := χ x
  let d (a : Index) := energyPartial a χ x
  let u (i : J) := z i x
  let v (i : J) := w i x
  let Du (a : Index) (i : J) := energyPartial a (z i) x
  let Dv (a : Index) (i : J) := fderiv ℝ (w i) x (EuclideanSpace.single a 1)
  ∑ a : Index, ∑ b : Index, ∑ i : J, ∑ j : J, ∑ k : J, C a b i j k x *
    (t * v i * (t * Du a j * (d b * u k) + d a * u j * (t * Du b k) + d a * u j * (d b * u k)) +
      t * u i * (t * Dv a j * (d b * u k) + d a * v j * (t * Du b k) + d a * v j * (d b * u k)) +
      t * u i * (t * Du a j * (d b * v k) + d a * u j * (t * Dv b k) + d a * u j * (d b * v k)))

/-- Localizing the two input fields and the tested field by the same
cutoff gives exactly its cube and the differentiated cutoff placements. -/
theorem principalCubicVariation_cutoff_product {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hw : ∀ i, Differentiable ℝ (w i)) (χ : SchwartzMap E ℂ) (x : E) :
    principalVariationDensity C (fun i => energyProduct χ (z i)) (fun i y => χ y * w i y) x =
      (χ x)^3 * principalVariationDensity C z w x + principalCubicCutoffJetError C z w χ x := by
  have hZ (a : Index) (i : J) : energyPartial a (energyProduct χ (z i)) x =
      energyPartial a χ x * z i x + χ x * energyPartial a (z i) x := by
    change fderiv ℝ ((χ : E → ℂ) * (z i : E → ℂ)) x (EuclideanSpace.single a 1) = _
    rw [fderiv_mul (χ.differentiable x) ((z i).differentiable x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change χ x * energyPartial a (z i) x + z i x * energyPartial a χ x = _
    ring
  have hW (a : Index) (i : J) : fderiv ℝ (fun y => χ y * w i y) x (EuclideanSpace.single a 1) =
      energyPartial a χ x * w i x + χ x * fderiv ℝ (w i) x (EuclideanSpace.single a 1) := by
    change fderiv ℝ ((χ : E → ℂ) * w i) x (EuclideanSpace.single a 1) = _
    rw [fderiv_mul (χ.differentiable x) (hw i x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change χ x * fderiv ℝ (w i) x _ + w i x * energyPartial a χ x = _
    ring
  simp only [principalVariationDensity, principalCubicCutoffJetError, energyProduct_apply, hZ, hW,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

/-- The difference between applying the original test after a cutoff and
localizing its output enters only in its three actual cubic placements. -/
theorem principalCubicVariation_cutoff_commutator {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (hQ : ∀ u, Differentiable ℝ (Q u))
    (χ : SchwartzMap E ℂ) (x : E) :
    let zχ := fun i => energyProduct χ (z i)
    let w := fun i => Q (z i)
    let e (i : J) := Q (zχ i) - fun y => χ y * w i y
    let d := fun a b i j k => (C a b i j k : E → ℂ)
    principalVariationDensity d zχ (fun i => Q (zχ i)) x =
      (χ x)^3 * principalVariationDensity d z w x +
        principalCubicCutoffJetError d z w χ x + principalVariationDensity d zχ e x := by
  intro zχ w e d
  let v (i : J) := fun y => χ y * w i y
  have hv (i : J) : Differentiable ℝ (v i) := χ.differentiable.mul (hQ (z i))
  have he (i : J) : Differentiable ℝ (e i) := (hQ (zχ i)).sub (hv i)
  have heq : (fun i => Q (zχ i)) = v + e := by
    funext i y
    change Q (zχ i) y = χ y * w i y + (Q (zχ i) y - χ y * w i y)
    ring
  rw [heq, principal_variation_density_add C zχ v e hv he]
  change principalVariationDensity d zχ v x + _ = _
  rw [principalCubicVariation_cutoff_product d z w (fun i => hQ (z i)) χ x]

end Burnett.A03
