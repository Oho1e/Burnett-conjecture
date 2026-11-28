import Burnett.Analysis.TransportWard.Weyl.PrincipalVariationDensityBridge
import Burnett.Analysis.TransportWard.Weyl.EulerRemainderPairing

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.V03.Palatini

open Set MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

def localizedEulerPrincipalVariationCoefficient {J : Type*} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (ρ : E → ℝ)
    (a d : Index) (i j k : J) (x : E) : ℝ :=
  ρ x * (eulerPrincipalVariationCoefficient S g a d i j k x).re

/-- Multiplying by the fixed chart cutoff gives the actual coefficient array
for A03 with a global derivative bound. On the plateau its value is the
literal unlocalized coefficient, including at every patch center there. -/
theorem localizedEulerPrincipalVariationCoefficient_properties {J : Type*} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (ρ : E → ℝ) {U K : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hnd : ∀ x ∈ U, assembleMetricComponents S (g x) ∈ nonsingularMetricDomain)
    (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U)
    (hρc : HasCompactSupport ρ) (hOne : ∀ x ∈ K, ρ x = 1) :
    let C := localizedEulerPrincipalVariationCoefficient S g ρ
    (∀ a d i j k, ContDiff ℝ ∞ (C a d i j k)) ∧
    (∀ a d i j k, tsupport (C a d i j k) ⊆ tsupport ρ) ∧
    (∀ a d i j k, C a d i j k = C d a i k j) ∧
    (∀ a d i j k x, x ∈ K → Complex.ofReal (C a d i j k x) =
      eulerPrincipalVariationCoefficient S g a d i j k x) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a d i j k x, ‖fderiv ℝ (C a d i j k) x‖ ≤ L := by
  intro C
  have hG : ContDiffOn ℝ ∞ (fun x => assembleMetricComponents S (g x)) U :=
    (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hD (a d : Index) (i j k : J) : ContDiffOn ℝ ∞
      (fun x => (eulerPrincipalVariationCoefficient S g a d i j k x).re) U := by
    change ContDiffOn ℝ ∞ (fun x =>
      fderiv ℝ (metricActionCoefficient S (a,j) (d,k)) (assembleMetricComponents S (g x)) (S i)) U
    have hc : ContDiffOn ℝ ∞ (fderiv ℝ (metricActionCoefficient S (a,j) (d,k))) nonsingularMetricDomain :=
      (contDiffOn_metricActionCoefficient S (a,j) (d,k)).fderiv_of_isOpen
        isOpen_nonsingularMetricDomain (by simp)
    exact (hc.comp hG hnd).clm_apply contDiffOn_const
  have hC (a d : Index) (i j k : J) : ContDiff ℝ ∞ (C a d i j k) :=
    Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hρ hρU (hD a d i j k)
  have hCS (a d : Index) (i j k : J) : tsupport (C a d i j k) ⊆ tsupport ρ :=
    tsupport_mul_subset_left
  refine ⟨hC, hCS, ?_, ?_, ?_⟩
  · intro a d i j k
    funext x
    unfold C localizedEulerPrincipalVariationCoefficient eulerPrincipalVariationCoefficient
    rw [metricActionCoefficient_swap S (a,j) (d,k)]
  · intro a d i j k x hx
    let D := fderiv ℝ (metricActionCoefficient S (a,j) (d,k)) (assembleMetricComponents S (g x)) (S i)
    change Complex.ofReal (ρ x * D) = Complex.ofReal D
    rw [hOne x hx, one_mul]
  · let F (κ : Index × Index × J × J × J) := C κ.1 κ.2.1 κ.2.2.1 κ.2.2.2.1 κ.2.2.2.2
    have hFc (κ : Index × Index × J × J × J) : Continuous (fderiv ℝ (F κ)) :=
      (hC _ _ _ _ _).continuous_fderiv (by simp)
    choose N hN using fun κ => hρc.isCompact.exists_bound_of_continuousOn (hFc κ).continuousOn
    let L := ∑ κ, max 0 (N κ)
    have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => le_max_left _ _
    refine ⟨L, hL, fun a d i j k x => ?_⟩
    let κ : Index × Index × J × J × J := (a,d,i,j,k)
    change ‖fderiv ℝ (F κ) x‖ ≤ L
    by_cases hx : x ∈ tsupport ρ
    · exact (hN κ x hx).trans ((le_max_right _ _).trans
        (Finset.single_le_sum (f := fun κ => max 0 (N κ))
          (fun _ _ => le_max_left _ _) (Finset.mem_univ κ)))
    · have hz : x ∉ tsupport (F κ) := fun h => hx (hCS a d i j k h)
      rw [fderiv_of_notMem_tsupport ℝ hz, norm_zero]
      exact hL

/-- The coefficient extension agrees in all three test placements, including
at points where the actual test and its derivatives vanish. -/
theorem principalVariationDensity_eq_localizedEulerCoefficient {J : Type} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (ρ : E → ℝ)
    (z : J → SchwartzMap E ℂ) (w : J → E → ℂ)
    {K : Set E} (hOne : ∀ x ∈ K, ρ x = 1) (hW : ∀ i, tsupport (w i) ⊆ K) :
    principalVariationDensity (eulerPrincipalVariationCoefficient S g) z w =
      principalVariationDensity
        (fun a d i j k x => Complex.ofReal (localizedEulerPrincipalVariationCoefficient S g ρ a d i j k x)) z w := by
  funext x
  by_cases hx : x ∈ K
  · have hC (a d : Index) (i j k : J) :
        Complex.ofReal (localizedEulerPrincipalVariationCoefficient S g ρ a d i j k x) =
          eulerPrincipalVariationCoefficient S g a d i j k x := by
      unfold localizedEulerPrincipalVariationCoefficient eulerPrincipalVariationCoefficient
      rw [hOne x hx, one_mul, Complex.ofReal_re]
    simp only [principalVariationDensity, hC]
  · have hOut (i : J) : x ∉ tsupport (w i) := fun h => hx (hW i h)
    have hz (i : J) : w i x = 0 := image_eq_zero_of_notMem_tsupport (hOut i)
    have hd (i : J) : fderiv ℝ (w i) x = 0 := fderiv_of_notMem_tsupport ℝ (hOut i)
    simp only [principalVariationDensity, hz, hd, ContinuousLinearMap.zero_apply,
      zero_mul, mul_zero, add_zero, Finset.sum_const_zero]

theorem setIntegral_principalVariationDensity_re_eq_localizedEulerCoefficient {J : Type} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (ρ : E → ℝ)
    (z : J → SchwartzMap E ℂ) (w : J → E → ℂ)
    {K : Set E} (hOne : ∀ x ∈ K, ρ x = 1) (hW : ∀ i, tsupport (w i) ⊆ K) :
    (∫ x in K, (principalVariationDensity (eulerPrincipalVariationCoefficient S g) z w x).re) =
      ∫ x, (principalVariationDensity
        (fun a d i j k x => Complex.ofReal (localizedEulerPrincipalVariationCoefficient S g ρ a d i j k x))
        z w x).re := by
  rw [principalVariationDensity_eq_localizedEulerCoefficient S g ρ z w hOne hW]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hOut (i : J) : x ∉ tsupport (w i) := fun h => hx (hW i h)
  have hz (i : J) : w i x = 0 := image_eq_zero_of_notMem_tsupport (hOut i)
  have hd (i : J) : fderiv ℝ (w i) x = 0 := fderiv_of_notMem_tsupport ℝ (hOut i)
  simp only [principalVariationDensity, hz, hd, ContinuousLinearMap.zero_apply,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero, Complex.zero_re]

end Burnett.V03.Palatini
