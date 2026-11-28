import Burnett.Analysis.TransportWard.Weyl.FixedInfraredTestDerivative
import Burnett.Analysis.TransportWard.Weyl.LocalizedPrincipalCoefficient
import Burnett.Analysis.TransportWard.Weyl.FrozenEulerQuadraticJet

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03.Palatini

open MeasureTheory Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol Burnett.C02
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise

local notation "J" => OrderedPair
local notation "Lin" => CubicLinearIndex J

private theorem reindex_frozen_principal_tests {I : Type} [Fintype I]
    (P : CubicLinearIndex I → ℂ) :
    (∑ a : Index, ∑ d : Index, ∑ i : I, ∑ j : I, ∑ k : I, P (((a,d),(j,k)),i)) =
      ∑ k : CubicLinearIndex I, P k := by
  let π : (Index × Index × I × I × I) ≃ CubicLinearIndex I :=
    { toFun := fun k => (((k.1,k.2.1),(k.2.2.2.1,k.2.2.2.2)),k.2.2.1)
      invFun := fun k => (k.1.1.1,k.1.1.2,k.2,k.1.2.1,k.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.sum_equiv π (fun k => P (π k)) P (fun _ => rfl)
  simpa only [Fintype.sum_prod_type, π] using he

/-- Freezing the actual A03 coefficient and test gives the original complete
C02 energy with the same fixed infrared test and the positive real pairing. -/
private theorem frozenPrincipalVariation_fixedInfrared_integrable_and_eq_completeCubicEnergy
    (G : Mat) (hG : G ∈ nonsingularMetricDomain)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (hJets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (hOdd : ∀ ξ, fixedInfraredSymbol cut 0 b (-ξ) = -fixedInfraredSymbol cut 0 b ξ)
    (u : RealEnergyField J) :
    let β := fixedInfraredSymbol cut 0 b
    let g (_ : E) (i : J) := G i.1 i.2
    let w (i : J) (x : E) := (-Complex.I) * radianAction β (u.val i) x
    let F := principalVariationDensity (eulerPrincipalVariationCoefficient frozenActionOrderedBasis g) u.val w
    Integrable F ∧ (∫ x, (F x).re) =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) β u := by
  classical
  intro β g w Q₀
  let c := frozenActionCubicLinear G
  let Q (f : SchwartzMap E ℂ) (x : E) := (-Complex.I) * radianAction β f x
  let A (k : Lin) := energyProduct (energyPartial k.1.1.1 (u.val k.1.2.1))
    (energyPartial k.1.1.2 (u.val k.1.2.2))
  let B (k : Lin) := energyProduct (u.val k.2) (energyPartial k.1.1.2 (u.val k.1.2.2))
  let C (k : Lin) := energyProduct (u.val k.2) (energyPartial k.1.1.1 (u.val k.1.2.1))
  let F₀ (k : Lin) (x : E) := A k x * Q (u.val k.2) x
  let F₁ (k : Lin) (x : E) := B k x * Q (energyPartial k.1.1.1 (u.val k.1.2.1)) x
  let F₂ (k : Lin) (x : E) := C k x * Q (energyPartial k.1.1.2 (u.val k.1.2.2)) x
  let ψ (x : E) (k : Lin) := (c k.1 k.2 : ℂ) * (F₀ k x + F₁ k x + F₂ k x)
  have hMat (x : E) : assembleMetricComponents frozenActionOrderedBasis (g x) = G := by
    rw [assembleMetricComponents_orderedBasis]
  have hCoeff (a d : Index) (i j k : J) (x : E) :
      eulerPrincipalVariationCoefficient frozenActionOrderedBasis g a d i j k x =
        (c ((a,d),(j,k)) i : ℂ) := by
    unfold eulerPrincipalVariationCoefficient
    rw [hMat x, ← frozenActionCubicLinear_eq_metricActionCoefficient_fderiv G hG a d j k i]
  have hDer (i : J) (x : E) (a : Index) :
      fderiv ℝ (w i) x (EuclideanSpace.single a 1) = Q (energyPartial a (u.val i)) x :=
    (fixedInfraredTest_coordinateDerivative cut hcut b hb hom (u.val i) x).2 a
  have hPoint (x : E) :
      principalVariationDensity (eulerPrincipalVariationCoefficient frozenActionOrderedBasis g) u.val w x =
        ∑ k : Lin, ψ x k := by
    calc
      _ = ∑ a : Index, ∑ d : Index, ∑ i : J, ∑ j : J, ∑ k : J, ψ x (((a,d),(j,k)),i) := by
        simp only [principalVariationDensity, hCoeff, hDer]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        simp only [ψ, F₀, F₁, F₂, A, B, C, energyProduct_apply]
        change (c ((a,d),(j,k)) i : ℂ) *
          (Q (u.val i) x * energyPartial a (u.val j) x * energyPartial d (u.val k) x +
            u.val i x * Q (energyPartial a (u.val j)) x * energyPartial d (u.val k) x +
            u.val i x * energyPartial a (u.val j) x * Q (energyPartial d (u.val k)) x) = _
        ring
      _ = _ := reindex_frozen_principal_tests (ψ x)
  obtain ⟨_, _, _, _, _, _, hLp⟩ := fixedInfraredSymbol_W1p_bound cut 0 hcut (fun _ => by simp) 2 (by norm_num)
  have hMem (f : SchwartzMap E ℂ) : MemLp (Q f) 2 volume := by
    have he : MemLp (radianAction β f) 2 volume := by
      simpa only [ENNReal.ofReal_ofNat] using (hLp b hb hom D hD hJets f).1
    exact he.const_mul (-Complex.I)
  have h₀ (k : Lin) : Integrable (F₀ k) := ((A k).memLp 2 volume).integrable_mul (hMem (u.val k.2))
  have h₁ (k : Lin) : Integrable (F₁ k) :=
    ((B k).memLp 2 volume).integrable_mul (hMem (energyPartial k.1.1.1 (u.val k.1.2.1)))
  have h₂ (k : Lin) : Integrable (F₂ k) :=
    ((C k).memLp 2 volume).integrable_mul (hMem (energyPartial k.1.1.2 (u.val k.1.2.2)))
  have hψ (k : Lin) : Integrable (fun x => ψ x k) :=
    (((h₀ k).add (h₁ k)).add (h₂ k)).const_mul (c k.1 k.2 : ℂ)
  have hDensity : Integrable (principalVariationDensity
      (eulerPrincipalVariationCoefficient frozenActionOrderedBasis g) u.val w) := by
    rw [funext hPoint]
    exact integrable_finset_sum Finset.univ (fun k _ => hψ k)
  have hCyclic :
      (∫ x, (principalVariationDensity (eulerPrincipalVariationCoefficient frozenActionOrderedBasis g) u.val w x).re) =
        frozenActionCyclicOddTestEnergy G β u := by
    have hRe : (∫ x, (Q₀ x).re) = (∫ x, Q₀ x).re := integral_re hDensity
    have hI : (∫ x, Q₀ x) = ∫ x, ∑ k : Lin, ψ x k :=
      integral_congr_ae (Filter.Eventually.of_forall hPoint)
    change (∫ x, (Q₀ x).re) = _
    rw [hRe, hI, integral_finset_sum _ (fun k _ => hψ k), Complex.re_sum]
    unfold frozenActionCyclicOddTestEnergy
    apply Finset.sum_congr rfl
    intro k _
    change (∫ x, (c k.1 k.2 : ℂ) * (F₀ k x + F₁ k x + F₂ k x)).re = _
    have hAdd := integral_add ((h₀ k).add (h₁ k)) (h₂ k)
    simp only [Pi.add_apply, integral_add (h₀ k) (h₁ k)] at hAdd
    rw [integral_const_mul, hAdd]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, c, F₀, F₁, F₂, A, B, C, Q, energyProduct_apply]
  exact ⟨hDensity, hCyclic.trans (frozenActionCyclicOddTestEnergy_fixedInfrared_eq_complete
    G cut 0 hcut (fun _ => by simp) b hb hom D hD hJets hOdd u)⟩

theorem frozenPrincipalVariation_fixedInfrared_eq_completeCubicEnergy
    (G : Mat) (hG : G ∈ nonsingularMetricDomain)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (hJets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (hOdd : ∀ ξ, fixedInfraredSymbol cut 0 b (-ξ) = -fixedInfraredSymbol cut 0 b ξ)
    (u : RealEnergyField J) :
    let β := fixedInfraredSymbol cut 0 b
    let g (_ : E) (i : J) := G i.1 i.2
    let w (i : J) (x : E) := (-Complex.I) * radianAction β (u.val i) x
    (∫ x, (principalVariationDensity (eulerPrincipalVariationCoefficient frozenActionOrderedBasis g) u.val w x).re) =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) β u :=
  (frozenPrincipalVariation_fixedInfrared_integrable_and_eq_completeCubicEnergy
    G hG cut hcut b hb hom D hD hJets hOdd u).2

theorem frozenPrincipalVariation_fixedInfrared_integral_re_eq_completeCubicEnergy
    (G : Mat) (hG : G ∈ nonsingularMetricDomain)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (hJets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (hOdd : ∀ ξ, fixedInfraredSymbol cut 0 b (-ξ) = -fixedInfraredSymbol cut 0 b ξ)
    (u : RealEnergyField J) :
    let β := fixedInfraredSymbol cut 0 b
    let g (_ : E) (i : J) := G i.1 i.2
    let w (i : J) (x : E) := (-Complex.I) * radianAction β (u.val i) x
    (∫ x, principalVariationDensity (eulerPrincipalVariationCoefficient frozenActionOrderedBasis g) u.val w x).re =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) β u := by
  obtain ⟨hInt, hEq⟩ := frozenPrincipalVariation_fixedInfrared_integrable_and_eq_completeCubicEnergy
    G hG cut hcut b hb hom D hD hJets hOdd u
  exact (integral_re hInt).symm.trans hEq

/-- At a patch center on the plateau, freezing the very same compactly
extended coefficient is exactly the previous frozen energy. -/
theorem localizedEulerPrincipalVariation_frozen_fixedInfrared_eq_completeCubicEnergy
    (g : E → J → ℝ) (ρ : E → ℝ) (c₀ : E) (hρ : ρ c₀ = 1)
    (hG : assembleMetricComponents frozenActionOrderedBasis (g c₀) ∈ nonsingularMetricDomain)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (hJets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (hOdd : ∀ ξ, fixedInfraredSymbol cut 0 b (-ξ) = -fixedInfraredSymbol cut 0 b ξ)
    (u : RealEnergyField J) :
    let G := assembleMetricComponents frozenActionOrderedBasis (g c₀)
    let β := fixedInfraredSymbol cut 0 b
    let w (i : J) (x : E) := (-Complex.I) * radianAction β (u.val i) x
    let C₀ (a d : Index) (i j k : J) (_ : E) :=
      Complex.ofReal (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis g ρ a d i j k c₀)
    (∫ x, (principalVariationDensity C₀ u.val w x).re) =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) β u := by
  intro G β w C₀
  let g₀ (_ : E) (i : J) := G i.1 i.2
  have hMat (x : E) : assembleMetricComponents frozenActionOrderedBasis (g₀ x) = G := by
    rw [assembleMetricComponents_orderedBasis]
  have hC : C₀ = eulerPrincipalVariationCoefficient frozenActionOrderedBasis g₀ := by
    funext a d i j k x
    dsimp only [C₀, localizedEulerPrincipalVariationCoefficient]
    rw [hρ, one_mul]
    unfold eulerPrincipalVariationCoefficient
    rw [Complex.ofReal_re, hMat x]
  rw [hC]
  exact frozenPrincipalVariation_fixedInfrared_eq_completeCubicEnergy
    G hG cut hcut b hb hom D hD hJets hOdd u

end Burnett.V03.Palatini
