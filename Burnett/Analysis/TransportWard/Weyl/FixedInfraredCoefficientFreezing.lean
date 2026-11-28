import Burnett.Analysis.PrincipalEnergy.Freezing.FixedInfraredCubicCoefficients
import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity
import Burnett.Analysis.TransportWard.Weyl.FrozenPrincipalCompleteCubic

set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol Burnett.A03
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Analysis.TransportWardSymbol Burnett.C02
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ENNReal BigOperators ContDiff ComplexConjugate Burnett.A03

open private principal_variation_density_integrable from Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

private theorem principalVariationDensity_congr_on_field_support {J : Type} [Fintype J]
    (C D : Index → Index → J → J → J → E → ℂ)
    (z : J → SchwartzMap E ℂ) (w : J → E → ℂ) (U : Set E)
    (hz : tsupport (fieldValueArray z) ⊆ U)
    (hC : ∀ a d i j k x, x ∈ U → C a d i j k x = D a d i j k x) :
    principalVariationDensity C z w = principalVariationDensity D z w := by
  have hSupport (i : J) : tsupport (z i : E → ℂ) ⊆ U := by
    apply (closure_mono ?_).trans hz
    intro x hx
    change z i x ≠ 0 at hx
    change fieldValueArray z x ≠ 0
    intro h
    exact hx (congrArg (fun v => v i) h)
  funext x
  by_cases hx : x ∈ U
  · simp only [principalVariationDensity, fun a d i j k => hC a d i j k x hx]
  · have hOff (i : J) : x ∉ tsupport (z i : E → ℂ) := fun hi => hx (hSupport i hi)
    have hv (i : J) : z i x = 0 := image_eq_zero_of_notMem_tsupport (hOff i)
    have hd (i : J) (a : Index) : energyPartial a (z i) x = 0 := by
      change fderiv ℝ (z i : E → ℂ) x (EuclideanSpace.single a 1) = 0
      rw [fderiv_of_notMem_tsupport ℝ (hOff i), ContinuousLinearMap.zero_apply]
    simp only [principalVariationDensity, hv, hd, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]

private theorem principalVariationDensity_add_smooth_test {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (u v : J → E → ℂ) (hu : ∀ i, Differentiable ℝ (u i)) (hv : ∀ i, Differentiable ℝ (v i)) :
    principalVariationDensity C z (u + v) =
      principalVariationDensity C z u + principalVariationDensity C z v := by
  funext x
  have hD (i : J) (a : Index) :
      fderiv ℝ (u i + v i) x (EuclideanSpace.single a 1) =
        fderiv ℝ (u i) x (EuclideanSpace.single a 1) +
          fderiv ℝ (v i) x (EuclideanSpace.single a 1) := by
    rw [fderiv_add (hu i x) (hv i x), ContinuousLinearMap.add_apply]
  simp only [principalVariationDensity, Pi.add_apply, hD, add_mul, mul_add, Finset.sum_add_distrib]
  abel

private def compactRealCoefficient (q : E → ℝ)
    (hs : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) : SchwartzMap E ℂ :=
  (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs)

/-- The coefficient compared with its center is the compact extension of the
Euler action coefficient. At the center the same test is exactly C02's energy. -/
theorem exists_localizedEulerPrincipalVariation_fixedInfrared_freezing_bound
    (g : E → OrderedPair → ℝ) (ρ : E → ℝ) {U K : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hMetric : ∀ x ∈ U, assembleMetricComponents frozenActionOrderedBasis (g x) ∈ nonsingularMetricDomain)
    (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ)
    (hOne : ∀ x ∈ K, ρ x = 1)
    (a : E → E → ℝ) (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (R D : ℝ) (hR : 0 < R) (hD : 0 ≤ D)
    (hb : ∀ c ∈ K, ContDiffOn ℝ ∞ (a c) {ξ | ξ ≠ 0})
    (hom : ∀ c ∈ K, ∀ t : ℝ, 0 < t → ∀ ξ, a c (t • ξ) = t * a c ξ)
    (odd : ∀ c ∈ K, ∀ ξ, a c (-ξ) = -a c ξ)
    (hJets : ∀ c ∈ K, ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (a c) ξ‖ ≤ D)
    (hβOdd : ∀ c ∈ K, ∀ ξ, fixedInfraredSymbol cut 0 (a c) (-ξ) = -fixedInfraredSymbol cut 0 (a c) ξ) :
    ∃ A B : ℝ≥0∞, A < ⊤ ∧ B < ⊤ ∧
      ∀ c ∈ K, ∀ (ℓ : ℝ), 0 < ℓ → ∀ z : RealEnergyField OrderedPair,
        tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        let G := assembleMetricComponents frozenActionOrderedBasis (g c)
        let β := fixedInfraredSymbol cut 0 (a c)
        let w (i : OrderedPair) (x : E) := (-Complex.I) * radianAction β (z.val i) x
        let C (d e : Index) (i j k : OrderedPair) (x : E) :=
          Complex.ofReal (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis g ρ d e i j k x)
        let F := principalVariationDensity C z.val w
        let X := euclideanFieldGradientNorm z.val
        let Y := eLpNorm (fieldValueArray z.val) (ENNReal.ofReal 3) volume
        Integrable F ∧
          ‖(∫ x, (F x).re) - completeCubicEnergy (frozenActionCubicLinear G)
            (frozenActionCubicQuadratic G) β z‖ₑ ≤ A * ENNReal.ofReal ℓ * X ^ 3 + B * Y * X ^ 2 := by
  let C := localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis g ρ
  obtain ⟨hSmooth, hSupport, hSymm, _, L, hL, hGrad⟩ :=
    localizedEulerPrincipalVariationCoefficient_properties frozenActionOrderedBasis g ρ hU hg hMetric hρ hρU hρc hOne
  let J := Index × Index × OrderedPair × OrderedPair × OrderedPair
  let F (q : J) := C q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  have hCompact (q : J) : HasCompactSupport (F q) :=
    hρc.of_isClosed_subset isClosed_closure (hSupport _ _ _ _ _)
  let S (q : J) := compactRealCoefficient (F q) (hSmooth _ _ _ _ _) (hCompact q)
  let M : ℝ := ∑ q : J, SchwartzMap.seminorm ℝ 0 0 (S q)
  have hBound (d e : Index) (i j k : OrderedPair) (x : E) : ‖C d e i j k x‖ ≤ M := by
    let q : J := (d,e,i,j,k)
    have hEq : ‖C d e i j k x‖ = ‖S q x‖ := (Complex.norm_real _).symm
    rw [hEq]
    have hSem : ‖S q x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (S q) := by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℝ 0 0 (S q) x
    exact hSem.trans (Finset.single_le_sum (f := fun p : J => SchwartzMap.seminorm ℝ 0 0 (S p))
      (fun _ _ => apply_nonneg _ _) (Finset.mem_univ q))
  obtain ⟨A, B, hA, hB, freeze⟩ := exists_fixedInfrared_coefficient_freezing_bound C hSmooth hSymm
    R L M hR hL hGrad hBound cut hcut D hD
  refine ⟨A, B, hA, hB, ?_⟩
  intro c hc ℓ hℓ z hz G β w Cvar Fvar X Y
  have hcU : c ∈ U := hρU (subset_tsupport _ (show ρ c ≠ 0 by rw [hOne c hc]; exact one_ne_zero))
  obtain ⟨hInt, _, hError⟩ := freeze c (a c) (hb c hc) (hom c hc) (odd c hc) (hJets c hc) ℓ hℓ z hz
  have hIdentity := localizedEulerPrincipalVariation_frozen_fixedInfrared_eq_completeCubicEnergy
    g ρ c (hOne c hc) (hMetric c hcU) cut hcut (a c) (hb c hc) (hom c hc) D hD
    (fun n hn => hJets c hc n (hn.trans (by decide))) (hβOdd c hc) z
  refine ⟨hInt, ?_⟩
  rw [← hIdentity]
  exact hError

end Burnett.V03.Palatini
