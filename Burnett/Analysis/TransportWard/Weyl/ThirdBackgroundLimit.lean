import Burnett.Analysis.TransportWard.Weyl.CubicBackgroundCompactLimits
import Burnett.Analysis.TransportWard.Weyl.ThirdBackgroundProducts

set_option autoImplicit false
set_option maxHeartbeats 8200000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open scoped ContDiff BigOperators Topology Matrix.Norms.Elementwise

open private contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

private theorem compact_integral_sum_tendsto_zero
    {I : Type*} [Fintype I] {K : Set E} (hK : IsCompact K) (F : I → ℕ → E → ℝ)
    (hF : ∀ i n, ContinuousOn (F i n) K)
    (hLim : ∀ i, Tendsto (fun n => ∫ x in K, F i n x) atTop (𝓝 0)) :
    (∀ n, IntegrableOn (fun x => ∑ i, F i n x) K) ∧
    Tendsto (fun n => ∫ x in K, ∑ i, F i n x) atTop (𝓝 0) := by
  have hInt (i : I) (n : ℕ) : IntegrableOn (F i n) K :=
    (hF i n).integrableOn_compact hK
  refine ⟨fun n => integrable_finset_sum _ (fun i _ => hInt i n), ?_⟩
  have h := tendsto_finset_sum Finset.univ (fun i _ => hLim i)
  simp only [Finset.sum_const_zero] at h
  exact h.congr fun n => (integral_finset_sum _ (fun i _ => hInt i n)).symm

/-- The actual background-cutoff third variation differs from its principal
density by a sequence tending to zero. Only the test value is bounded in
L². Its derivative in the one remaining term is transferred by integration
by parts to the background coefficient and the two small fields. -/
theorem tendsto_thirdVariation_sub_localizedPrincipal_zero
    {J : Type} [Fintype J] (S : J → Mat) (g : E → J → ℝ) {U K : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hnd : ∀ x ∈ U,
      assembleMetricComponents S (g x) ∈ nonsingularMetricDomain)
    (hK : IsCompact K) (hKU : K ⊆ U) (ρ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ)
    (hOne : ∀ x ∈ K, ρ x = 1)
    (z w : ℕ → RealEnergyField J) (hwS : ∀ n i, tsupport ((w n).val i : E → ℂ) ⊆ K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (hSmall : ∀ n i x, ‖(z n).val i x‖ ≤ ε n)
    (M : ℝ) (hM : 0 ≤ M)
    (hZ : ∀ n i, ‖((z n).val i).toLp 2 volume‖ ≤ M)
    (hDZ : ∀ (n : ℕ) (s : ActionSlot J), ‖(energyPartial s.1 ((z n).val s.2)).toLp 2 volume‖ ≤ M)
    (hW : ∀ n i, ‖((w n).val i).toLp 2 volume‖ ≤ M) :
    let C (a d : Index) (i j k : J) (x : E) :=
      Complex.ofReal (localizedEulerPrincipalVariationCoefficient S g ρ a d i j k x)
    Tendsto (fun n => (∫ x in K, coordinateActionThirdVariationDensity S g
      (fun y i => ((z n).val i y).re) (fun y i => ((w n).val i y).re) x) -
      ∫ x, (principalVariationDensity C (z n).val (fun i => (w n).val i) x).re) atTop (𝓝 0) := by
  classical
  intro C
  let h (n : ℕ) (x : E) (i : J) := ((z n).val i x).re
  let k (n : ℕ) (x : E) (i : J) := ((w n).val i x).re
  let p (s : ActionSlot J) (x : E) := coordinateMetricFirstJet g x s
  let dz (n : ℕ) (x : E) (s : ActionSlot J) := (energyPartial s.1 ((z n).val s.2) x).re
  let dw (n : ℕ) (x : E) (s : ActionSlot J) := (energyPartial s.1 ((w n).val s.2) x).re
  let G (x : E) := assembleMetricComponents S (g x)
  let A := ActionSlot J × ActionSlot J × J × J
  let B := ActionSlot J × ActionSlot J × J × J × J
  let R₀ (v : A) (x : E) := eulerThirdVariationCoefficientOrderTwo S g v.1 v.2.1
    v.2.2.1 v.2.2.2 x * p v.2.1 x
  let R₁ (v : A) (x : E) := eulerThirdVariationCoefficientOrderTwo S g v.1 v.2.1
    v.2.2.1 v.2.2.2 x * p v.1 x
  let R₂ (v : B) (x : E) := (1 / 2 : ℝ) * eulerThirdVariationCoefficientOrderThree S g v.1 v.2.1
    v.2.2.1 v.2.2.2.1 v.2.2.2.2 x * p v.1 x * p v.2.1 x
  let F₀ (v : A) (n : ℕ) (x : E) :=
    R₀ v x * h n x v.2.2.1 * h n x v.2.2.2 * dw n x v.1
  let F₁ (v : A) (n : ℕ) (x : E) :=
    R₀ v x * h n x v.2.2.1 * dz n x v.1 * k n x v.2.2.2
  let F₂ (v : A) (n : ℕ) (x : E) :=
    R₁ v x * h n x v.2.2.1 * dz n x v.2.1 * k n x v.2.2.2
  let F₃ (v : B) (n : ℕ) (x : E) :=
    R₂ v x * h n x v.2.2.1 * h n x v.2.2.2.1 * k n x v.2.2.2.2
  let Q (n : ℕ) (x : E) := (principalVariationDensity C (z n).val (fun i => (w n).val i) x).re
  have hG : ContDiffOn ℝ ∞ G U := (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hp (s : ActionSlot J) : ContDiffOn ℝ ∞ (p s) U :=
    contDiffOn_coordinateMetricFirstJet hU g hg s
  have hC₂ (s t : ActionSlot J) (i j : J) :
      ContDiffOn ℝ ∞ (eulerThirdVariationCoefficientOrderTwo S g s t i j) U := by
    let D := fderiv ℝ (metricActionCoefficient S s t)
    have hD : ContDiffOn ℝ ∞ D nonsingularMetricDomain :=
      (contDiffOn_metricActionCoefficient S s t).fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)
    change ContDiffOn ℝ ∞ (fun x => fderiv ℝ D (G x) (S i) (S j)) U
    exact ((((hD.fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)).comp hG hnd).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const)
  have hC₃ (s t : ActionSlot J) (i j l : J) :
      ContDiffOn ℝ ∞ (eulerThirdVariationCoefficientOrderThree S g s t i j l) U := by
    let D := fderiv ℝ (metricActionCoefficient S s t)
    have hD : ContDiffOn ℝ ∞ D nonsingularMetricDomain :=
      (contDiffOn_metricActionCoefficient S s t).fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)
    have hD₂ : ContDiffOn ℝ ∞ (fderiv ℝ D) nonsingularMetricDomain :=
      hD.fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)
    change ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fderiv ℝ D) (G x) (S i) (S j) (S l)) U
    exact (((((hD₂.fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)).comp hG hnd).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hR₀ (v : A) : ContDiffOn ℝ ∞ (R₀ v) U := (hC₂ _ _ _ _).mul (hp _)
  have hR₁ (v : A) : ContDiffOn ℝ ∞ (R₁ v) U := (hC₂ _ _ _ _).mul (hp _)
  have hR₂ (v : B) : ContDiffOn ℝ ∞ (R₂ v) U :=
    ((contDiffOn_const.mul (hC₃ _ _ _ _ _)).mul (hp _)).mul (hp _)
  have hzr (n : ℕ) (i : J) (x : E) : Complex.ofReal (h n x i) = (z n).val i x :=
    coe_re_eq_of_conj_eq _ ((z n).property i x)
  have hz₁ (n : ℕ) (x : E) (s : ActionSlot J) :
      coordinateMetricFirstJet (h n) x s = dz n x s := by
    exact (congrArg Complex.re ((realEnergyField_jets (z n)).1 x s))
  have hw₁ (n : ℕ) (x : E) (s : ActionSlot J) :
      coordinateMetricFirstJet (k n) x s = dw n x s := by
    exact (congrArg Complex.re ((realEnergyField_jets (w n)).1 x s))
  have hdzr (n : ℕ) (s : ActionSlot J) (x : E) :
      Complex.ofReal (dz n x s) = energyPartial s.1 ((z n).val s.2) x := by
    rw [← hz₁ n x s]
    exact (realEnergyField_jets (z n)).1 x s
  have hcZ (n : ℕ) (i : J) : Continuous (fun x => h n x i) :=
    Complex.continuous_re.comp ((z n).val i).continuous
  have hcW (n : ℕ) (i : J) : Continuous (fun x => k n x i) :=
    Complex.continuous_re.comp ((w n).val i).continuous
  have hcDZ (n : ℕ) (s : ActionSlot J) : Continuous (fun x => dz n x s) :=
    Complex.continuous_re.comp (energyPartial s.1 ((z n).val s.2)).continuous
  have hcDW (n : ℕ) (s : ActionSlot J) : Continuous (fun x => dw n x s) :=
    Complex.continuous_re.comp (energyPartial s.1 ((w n).val s.2)).continuous
  have hL₀ (v : A) : Tendsto (fun n => ∫ x in K, F₀ v n x) atTop (𝓝 0) :=
    tendsto_compact_cubicBackground_derivativePair_zero hU hK (EuclideanSpace.single v.1.1 1)
      (R₀ v) ρ (hR₀ v) hρ hρU hρc hOne (fun n => (z n).val v.2.2.1)
      (fun n => (z n).val v.2.2.2) (fun n => (w n).val v.1.2)
      (fun n => hzr n _) (fun n => hzr n _) (fun n => hwS n _) ε hε hLim
      (fun n => hSmall n _) (fun n => hSmall n _) M hM (fun n => hZ n _)
      (fun n => hDZ n (v.1.1, v.2.2.1)) (fun n => hDZ n (v.1.1, v.2.2.2)) (fun n => hW n _)
  have hL₁ (v : A) : Tendsto (fun n => ∫ x in K, F₁ v n x) atTop (𝓝 0) :=
    tendsto_compact_cubicBackground_valuePair_zero hU hK
      (R₀ v) ρ (hR₀ v) hρ hρU hρc hOne (fun n => (z n).val v.2.2.1)
      (fun n => energyPartial v.1.1 ((z n).val v.1.2)) (fun n => (w n).val v.2.2.2)
      (fun n => hzr n _) (fun n => hdzr n _) (fun n => hwS n _) ε hε hLim
      (fun n => hSmall n _) M hM (fun n => hDZ n _) (fun n => hW n _)
  have hL₂ (v : A) : Tendsto (fun n => ∫ x in K, F₂ v n x) atTop (𝓝 0) :=
    tendsto_compact_cubicBackground_valuePair_zero hU hK
      (R₁ v) ρ (hR₁ v) hρ hρU hρc hOne (fun n => (z n).val v.2.2.1)
      (fun n => energyPartial v.2.1.1 ((z n).val v.2.1.2)) (fun n => (w n).val v.2.2.2)
      (fun n => hzr n _) (fun n => hdzr n _) (fun n => hwS n _) ε hε hLim
      (fun n => hSmall n _) M hM (fun n => hDZ n _) (fun n => hW n _)
  have hL₃ (v : B) : Tendsto (fun n => ∫ x in K, F₃ v n x) atTop (𝓝 0) :=
    tendsto_compact_cubicBackground_valuePair_zero hU hK
      (R₂ v) ρ (hR₂ v) hρ hρU hρc hOne (fun n => (z n).val v.2.2.1)
      (fun n => (z n).val v.2.2.2.1) (fun n => (w n).val v.2.2.2.2)
      (fun n => hzr n _) (fun n => hzr n _) (fun n => hwS n _) ε hε hLim
      (fun n => hSmall n _) M hM (fun n => hZ n _) (fun n => hW n _)
  obtain ⟨hI₀, hT₀⟩ := compact_integral_sum_tendsto_zero hK F₀
    (fun v n => ((((hR₀ v).continuousOn.mul (hcZ n _).continuousOn).mul
      (hcZ n _).continuousOn).mul (hcDW n _).continuousOn).mono hKU) hL₀
  obtain ⟨hI₁, hT₁⟩ := compact_integral_sum_tendsto_zero hK F₁
    (fun v n => ((((hR₀ v).continuousOn.mul (hcZ n _).continuousOn).mul
      (hcDZ n _).continuousOn).mul (hcW n _).continuousOn).mono hKU) hL₁
  obtain ⟨hI₂, hT₂⟩ := compact_integral_sum_tendsto_zero hK F₂
    (fun v n => ((((hR₁ v).continuousOn.mul (hcZ n _).continuousOn).mul
      (hcDZ n _).continuousOn).mul (hcW n _).continuousOn).mono hKU) hL₂
  obtain ⟨hI₃, hT₃⟩ := compact_integral_sum_tendsto_zero hK F₃
    (fun v n => ((((hR₂ v).continuousOn.mul (hcZ n _).continuousOn).mul
      (hcZ n _).continuousOn).mul (hcW n _).continuousOn).mono hKU) hL₃
  have hQT (n : ℕ) : Continuous (Q n) := by
    have hCs := (localizedEulerPrincipalVariationCoefficient_properties S g ρ hU hg hnd hρ hρU hρc hOne).1
    have hCW (i : J) (a : Index) :
        Continuous (fun x => fderiv ℝ ((w n).val i : E → ℂ) x (EuclideanSpace.single a 1)) :=
      (energyPartial a ((w n).val i)).continuous
    apply Complex.continuous_re.comp
    unfold principalVariationDensity
    refine continuous_finset_sum _ (fun a _ => continuous_finset_sum _ (fun d _ =>
      continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
        continuous_finset_sum _ (fun k _ => ?_)))))
    refine (Complex.continuous_ofReal.comp (hCs a d i j k).continuous).mul ?_
    exact (((((w n).val i).continuous.mul (energyPartial a ((z n).val j)).continuous).mul
      (energyPartial d ((z n).val k)).continuous).add
      ((((z n).val i).continuous.mul (hCW j a)).mul (energyPartial d ((z n).val k)).continuous)).add
      ((((z n).val i).continuous.mul (energyPartial a ((z n).val j)).continuous).mul (hCW k d))
  have hI (n : ℕ) : IntegrableOn (Q n) K := (hQT n).continuousOn.integrableOn_compact hK
  have hEq (n : ℕ) (x : E) (hx : x ∈ K) :
      coordinateActionThirdVariationDensity S g (h n) (k n) x =
        ((((Q n x + ∑ v : A, F₀ v n x) + ∑ v : A, F₁ v n x) +
          ∑ v : A, F₂ v n x) + ∑ v : B, F₃ v n x) := by
    have he := coordinateActionThirdVariationDensity_eq_A03_principal_add_componentProducts
      S g (z n) (w n) hU hg x (hKU hx) (hnd x (hKU hx))
    dsimp only at he
    rw [he, principalVariationDensity_eq_localizedEulerCoefficient S g ρ (z n).val
      (fun i => (w n).val i) hOne (hwS n)]
    have hF₀ : (∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, ∑ j : J,
        eulerThirdVariationCoefficientOrderTwo S g s t i j x * p t x *
          h n x i * h n x j * dw n x s) = ∑ v : A, F₀ v n x := by
      simp only [A, F₀, R₀, Fintype.sum_prod_type]
    have hD : (∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, ∑ j : J,
        eulerThirdVariationCoefficientOrderTwo S g s t i j x * h n x i * k n x j *
          (dz n x s * p t x + p s x * dz n x t)) =
        (∑ v : A, F₁ v n x) + ∑ v : A, F₂ v n x := by
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ v : A, eulerThirdVariationCoefficientOrderTwo S g v.1 v.2.1 v.2.2.1 v.2.2.2 x *
            h n x v.2.2.1 * k n x v.2.2.2 * (dz n x v.1 * p v.2.1 x + p v.1 x * dz n x v.2.1) := by
          simp only [A, Fintype.sum_prod_type]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro v _
          dsimp only [F₁, F₂, R₀, R₁]
          ring
    have hF₃ : (∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, ∑ j : J, ∑ l : J,
        (1 / 2 : ℝ) * eulerThirdVariationCoefficientOrderThree S g s t i j l x * p s x * p t x *
          h n x i * h n x j * k n x l) = ∑ v : B, F₃ v n x := by
      simp only [B, F₃, R₂, Fintype.sum_prod_type]
    have hzJet : coordinateMetricFirstJet (fun y i => ((z n).val i y).re) x = dz n x :=
      funext (hz₁ n x)
    have hwJet : coordinateMetricFirstJet (fun y i => ((w n).val i y).re) x = dw n x :=
      funext (hw₁ n x)
    rw [hzJet, hwJet]
    change Q n x +
        (∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, ∑ j : J,
          eulerThirdVariationCoefficientOrderTwo S g s t i j x * p t x *
            h n x i * h n x j * dw n x s) +
        (∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, ∑ j : J,
          eulerThirdVariationCoefficientOrderTwo S g s t i j x * h n x i * k n x j *
            (dz n x s * p t x + p s x * dz n x t)) +
        (∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, ∑ j : J, ∑ l : J,
          (1 / 2 : ℝ) * eulerThirdVariationCoefficientOrderThree S g s t i j l x * p s x * p t x *
            h n x i * h n x j * k n x l) = _
    rw [hF₀, hD, hF₃]
    ring
  have hTail := (((hT₀.add hT₁).add hT₂).add hT₃)
  simp only [add_zero] at hTail
  refine hTail.congr fun n => ?_
  let J₀ (x : E) := ∑ v : A, F₀ v n x
  let J₁ (x : E) := ∑ v : A, F₁ v n x
  let J₂ (x : E) := ∑ v : A, F₂ v n x
  let J₃ (x : E) := ∑ v : B, F₃ v n x
  change (((∫ x in K, J₀ x) + ∫ x in K, J₁ x) + ∫ x in K, J₂ x) + ∫ x in K, J₃ x =
    (∫ x in K, coordinateActionThirdVariationDensity S g (h n) (k n) x) - ∫ x, Q n x
  have hPair : (∫ x in K, coordinateActionThirdVariationDensity S g (h n) (k n) x) =
      ∫ x in K, (Q n + J₀ + J₁ + J₂ + J₃) x := setIntegral_congr_fun hK.measurableSet (hEq n)
  have e₀ : (∫ x in K, (Q n + J₀) x) = (∫ x in K, Q n x) + ∫ x in K, J₀ x :=
    integral_add (hI n) (hI₀ n)
  have e₁ : (∫ x in K, (Q n + J₀ + J₁) x) = (∫ x in K, (Q n + J₀) x) + ∫ x in K, J₁ x :=
    integral_add ((hI n).add (hI₀ n)) (hI₁ n)
  have e₂ : (∫ x in K, (Q n + J₀ + J₁ + J₂) x) =
      (∫ x in K, (Q n + J₀ + J₁) x) + ∫ x in K, J₂ x :=
    integral_add (((hI n).add (hI₀ n)).add (hI₁ n)) (hI₂ n)
  have e₃ : (∫ x in K, (Q n + J₀ + J₁ + J₂ + J₃) x) =
      (∫ x in K, (Q n + J₀ + J₁ + J₂) x) + ∫ x in K, J₃ x :=
    integral_add ((((hI n).add (hI₀ n)).add (hI₁ n)).add (hI₂ n)) (hI₃ n)
  rw [hPair, e₃, e₂, e₁, e₀]
  have hQP := setIntegral_principalVariationDensity_re_eq_localizedEulerCoefficient
    S g ρ (z n).val (fun i => (w n).val i) hOne (hwS n)
  rw [principalVariationDensity_eq_localizedEulerCoefficient S g ρ (z n).val
    (fun i => (w n).val i) hOne (hwS n)] at hQP
  change (∫ x in K, Q n x) = ∫ x, Q n x at hQP
  rw [← hQP]
  ring

end Burnett.V03.Palatini
