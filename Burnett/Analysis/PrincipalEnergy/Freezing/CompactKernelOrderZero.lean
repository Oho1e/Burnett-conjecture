import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedTestComparison
import Burnett.Analysis.PrincipalEnergy.Freezing.EnergyHolder
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactKernelOrderZero

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff

/-- The true base derivative of a two-point kernel, keeping the input
point fixed. -/
def compactKernelDx (K : E → E → ℂ) (x y : E) : E →L[ℝ] ℂ :=
  (fderiv ℝ (Function.uncurry K) (x,y)).comp (ContinuousLinearMap.inl ℝ E E)

private theorem compact_kernel_section_hasFDerivAt (K : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry K)) (x y : E) :
    HasFDerivAt (fun s => K s y) (compactKernelDx K x y) x := by
  have hK : HasFDerivAt (Function.uncurry K) (fderiv ℝ (Function.uncurry K) (x,y)) (x,y) :=
    (smooth.differentiable le_rfl (x,y)).hasFDerivAt
  have hpair : HasFDerivAt (fun q : E => (q,y)) (ContinuousLinearMap.inl ℝ E E) x :=
    hasFDerivAt_prodMk_left x y
  exact hK.comp x hpair

private theorem compact_kernel_dx_continuous (K : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry K)) :
    Continuous (Function.uncurry (compactKernelDx K)) :=
  (smooth.continuous_fderiv le_rfl).clm_comp_const _

private theorem compact_kernel_pointwise_integral_bound (K : E → E → ℂ)
    (ρ u : SchwartzMap E ℂ) (A : ℝ) (A0 : 0 ≤ A)
    (bound : ∀ x y, ‖K x y‖ ≤ A * ‖ρ x‖ * ‖ρ y‖) (x : E) :
    ‖compactKernelAction K u x‖ₑ ≤
      ENNReal.ofReal A * eLpNorm (ρ : E → ℂ) (ENNReal.ofReal (3 / 2)) volume *
        eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume * ‖ρ x‖ₑ := by
  let q := ENNReal.ofReal (3 / 2)
  let p := ENNReal.ofReal 3
  have localI (y : E) :
      ‖K x y * u y‖ₑ ≤ (ENNReal.ofReal A * ‖ρ x‖ₑ) * ‖u y * ρ y‖ₑ := by
    rw [← ofReal_norm_eq_enorm, norm_mul, ← ofReal_norm_eq_enorm (ρ x),
      ← ofReal_norm_eq_enorm (u y * ρ y), norm_mul,
      ← ENNReal.ofReal_mul A0, ← ENNReal.ofReal_mul (mul_nonneg A0 (norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_right (bound x y) (norm_nonneg (u y))])
  have conj : ENNReal.HolderTriple p q 1 := by
    constructor
    rw [show p = ENNReal.ofReal 3 from rfl, show q = ENNReal.ofReal (3 / 2) from rfl,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num), inv_one, ← ENNReal.ofReal_one]
    exact congrArg ENNReal.ofReal (by norm_num)
  letI := conj
  have hM : Measurable (fun y : E => ‖u y * ρ y‖ₑ) :=
    (u.continuous.mul ρ.continuous).enorm.measurable
  have hN : (∫⁻ y : E, ‖u y * ρ y‖ₑ) ≤
      eLpNorm (u : E → ℂ) p volume * eLpNorm (ρ : E → ℂ) q volume := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_smul_le_mul_eLpNorm (φ := (u : E → ℂ)) (f := (ρ : E → ℂ))
      (p := p) (q := q) (r := 1) ρ.continuous.aestronglyMeasurable u.continuous.aestronglyMeasurable
  calc
    _ ≤ ∫⁻ y : E, ‖K x y * u y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y : E, (ENNReal.ofReal A * ‖ρ x‖ₑ) * ‖u y * ρ y‖ₑ := lintegral_mono localI
    _ = (ENNReal.ofReal A * ‖ρ x‖ₑ) * ∫⁻ y : E, ‖u y * ρ y‖ₑ := lintegral_const_mul _ hM
    _ ≤ (ENNReal.ofReal A * ‖ρ x‖ₑ) *
        (eLpNorm (u : E → ℂ) p volume * eLpNorm (ρ : E → ℂ) q volume) := mul_le_mul_left' hN _
    _ = _ := by ac_rfl

/-- Genuine \(W^{1,3}\) bound for a compactly weighted physical
correction. Its first output derivatives are order minus infinity in
this estimate, with cost measured only against the original value. -/
theorem compact_weighted_kernel_action_W13 (K : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry K))
    (ρ : SchwartzMap E ℂ) (A : ℝ) (A0 : 0 ≤ A)
    (bounds : ∀ x y, ‖K x y‖ ≤ A * ‖ρ x‖ * ‖ρ y‖ ∧
      ‖compactKernelDx K x y‖ ≤ A * ‖ρ x‖ * ‖ρ y‖)
    (u : SchwartzMap E ℂ) :
    let p := ENNReal.ofReal 3
    let C := ENNReal.ofReal A * eLpNorm (ρ : E → ℂ) (ENNReal.ofReal (3 / 2)) volume *
      eLpNorm (ρ : E → ℂ) p volume
    let W := compactKernelAction K u
    MemLp W p volume ∧ eLpNorm W p volume ≤ C * eLpNorm (u : E → ℂ) p volume ∧
      Differentiable ℝ W ∧
      ∀ j : Index, let d (x : E) := fderiv ℝ W x (EuclideanSpace.single j 1)
        MemLp d p volume ∧ eLpNorm d p volume ≤ C * eLpNorm (u : E → ℂ) p volume := by
  intro p C W
  let S := (SchwartzMap.seminorm ℝ 0 0) ρ
  have S0 : 0 ≤ S := apply_nonneg _ _
  let M := A * S ^ 2
  have M0 : 0 ≤ M := mul_nonneg A0 (sq_nonneg _)
  have unif (x y : E) :
      ‖K x y‖ ≤ M ∧ ‖compactKernelDx K x y‖ ≤ M := by
    have B : A * ‖ρ x‖ * ‖ρ y‖ ≤ M := by
      unfold M
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ρ.norm_le_seminorm ℝ x) A0) (norm_nonneg (ρ y)),
        mul_le_mul_of_nonneg_left (ρ.norm_le_seminorm ℝ y) (mul_nonneg A0 S0)]
    exact ⟨(bounds x y).1.trans B, (bounds x y).2.trans B⟩
  let F (x y : E) := K x y * u y
  let G (x y : E) := u y • compactKernelDx K x y
  have FC (x : E) : Continuous (F x) :=
    (smooth.continuous.comp (continuous_const.prodMk continuous_id)).mul u.continuous
  have GC (x : E) : Continuous (G x) :=
    u.continuous.smul ((compact_kernel_dx_continuous K smooth).comp (continuous_const.prodMk continuous_id))
  have GX (y : E) : Continuous (fun x => G x y) :=
    continuous_const.smul ((compact_kernel_dx_continuous K smooth).comp (continuous_id.prodMk continuous_const))
  let m (y : E) := M * ‖u y‖
  have mI : Integrable m volume := u.integrable.norm.const_mul M
  have FB (x y : E) : ‖F x y‖ ≤ m y := by
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (unif x y).1 (norm_nonneg _))
  have GB (x y : E) : ‖G x y‖ ≤ m y := by
    rw [show G x y = u y • compactKernelDx K x y from rfl, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (unif x y).2 (norm_nonneg _)
  have GI (x : E) : Integrable (G x) volume :=
    mI.mono' (GC x).aestronglyMeasurable (Eventually.of_forall (GB x))
  have hd (x : E) : HasFDerivAt W (∫ y, G x y) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F := F) (F' := G) (bound := m)
      (ε := 1) (by norm_num)
    · exact Eventually.of_forall fun q => (FC q).aestronglyMeasurable
    · exact mI.mono' (FC x).aestronglyMeasurable (Eventually.of_forall (FB x))
    · exact (GC x).aestronglyMeasurable
    · exact Eventually.of_forall fun y q _ => GB q y
    · exact mI
    · exact Eventually.of_forall fun y q _ => (compact_kernel_section_hasFDerivAt K smooth q y).mul_const (u y)
  have WD : Differentiable ℝ W := fun x => (hd x).differentiableAt
  have WC : Continuous W := WD.continuous
  have gradC : Continuous (fun x : E => ∫ y, G x y) :=
    continuous_of_dominated (fun x => (GC x).aestronglyMeasurable)
      (fun x => Eventually.of_forall (GB x)) mI (Eventually.of_forall GX)
  let V := ENNReal.ofReal A * eLpNorm (ρ : E → ℂ) (ENNReal.ofReal (3 / 2)) volume *
    eLpNorm (u : E → ℂ) p volume
  have Vfin : V < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ρ.memLp _ volume).eLpNorm_lt_top) (u.memLp _ volume).eLpNorm_lt_top
  have lp (Z : E → ℂ) (ZC : Continuous Z) (ZB : ∀ x, ‖Z x‖ₑ ≤ V * ‖ρ x‖ₑ) :
      MemLp Z p volume ∧ eLpNorm Z p volume ≤ C * eLpNorm (u : E → ℂ) p volume := by
    have L : eLpNorm Z p volume ≤ V * eLpNorm (ρ : E → ℂ) p volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p ρ.continuous.aestronglyMeasurable (Eventually.of_forall ZB)
    refine ⟨⟨ZC.aestronglyMeasurable, L.trans_lt
        (ENNReal.mul_lt_top Vfin (ρ.memLp _ volume).eLpNorm_lt_top)⟩, L.trans_eq ?_⟩
    unfold V C
    ac_rfl
  have value := lp W WC (compact_kernel_pointwise_integral_bound K ρ u A A0 fun x y => (bounds x y).1)
  refine ⟨value.1,value.2,fun x => (hd x).differentiableAt,?_⟩
  intro j d
  let e : E := EuclideanSpace.single j 1
  let J (x y : E) := compactKernelDx K x y e
  have normE : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_single]
  have Jb (x y : E) : ‖J x y‖ ≤ A * ‖ρ x‖ * ‖ρ y‖ := by
    exact ((ContinuousLinearMap.le_opNorm (compactKernelDx K x y) e).trans_eq
      (by rw [normE, mul_one])).trans (bounds x y).2
  have dEq (x : E) : d x = compactKernelAction J u x := by
    change fderiv ℝ W x e = _
    rw [(hd x).fderiv, ContinuousLinearMap.integral_apply (GI x)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by simp [G, J, mul_comm]
  have dC : Continuous d := by
    have eq : d = fun x => (∫ y, G x y) e :=
      funext fun x => congrArg (fun L : E →L[ℝ] ℂ => L e) (hd x).fderiv
    rw [eq]
    exact gradC.clm_apply continuous_const
  exact lp d dC fun x => (dEq x).symm ▸ compact_kernel_pointwise_integral_bound J ρ u A A0 Jb x

private theorem compact_kernel_dx_zero_outside (K : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry K)) (R : ℝ)
    (support : ∀ x y, x ∉ closedBall (0 : E) R ∨ y ∉ closedBall (0 : E) R → K x y = 0)
    (x y : E) (outside : x ∉ closedBall (0 : E) R ∨ y ∉ closedBall (0 : E) R) :
    compactKernelDx K x y = 0 := by
  rw [← (compact_kernel_section_hasFDerivAt K smooth x y).fderiv]
  apply fderiv_of_notMem_tsupport
  rcases outside with hx | hy
  · have sub : tsupport (fun s => K s y) ⊆ closedBall (0 : E) R := by
      apply closure_minimal _ isClosed_closedBall
      intro s hs
      by_contra bad
      exact hs (support s y (.inl bad))
    exact fun h => hx (sub h)
  · have eq : (fun s => K s y) = 0 := funext fun s => support s y (.inr hy)
    rw [eq, tsupport]
    simp [Function.support]

/-- A single fixed continuous first kernel jet on a fixed compact product
gives an order-zero correction uniformly for every input. -/
theorem exists_compact_kernel_action_W13 (K : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry K)) (R : ℝ)
    (support : ∀ x y, x ∉ closedBall (0 : E) R ∨ y ∉ closedBall (0 : E) R → K x y = 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ u : SchwartzMap E ℂ,
      let p := ENNReal.ofReal 3
      let W := compactKernelAction K u
      MemLp W p volume ∧ eLpNorm W p volume ≤ C * eLpNorm (u : E → ℂ) p volume ∧
        Differentiable ℝ W ∧
        ∀ j : Index, let d (x : E) := fderiv ℝ W x (EuclideanSpace.single j 1)
          MemLp d p volume ∧ eLpNorm d p volume ≤ C * eLpNorm (u : E → ℂ) p volume := by
  let D := closedBall (0 : E) R ×ˢ closedBall (0 : E) R
  have hD : IsCompact D := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  let b (p : E × E) := max ‖K p.1 p.2‖ ‖compactKernelDx K p.1 p.2‖
  have hb : Continuous b := smooth.continuous.norm.max (compact_kernel_dx_continuous K smooth).norm
  obtain ⟨A', bound⟩ := (hD.image hb).bddAbove
  let A := max 0 A'
  have A0 : 0 ≤ A := le_max_left _ _
  have hh (q : E × E) (hq : q ∈ D) : b q ≤ A :=
    (bound (mem_image_of_mem b hq)).trans (le_max_right _ _)
  let bump : ContDiffBump (0 : E) :=
    ⟨max 1 R, max 1 R + 1, lt_of_lt_of_le zero_lt_one (le_max_left _ _), by linarith⟩
  let ρf (x : E) := ((bump x : ℝ) : ℂ)
  have ρsupport : HasCompactSupport ρf := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  let ρ := ρsupport.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have ρone (x : E) (hx : x ∈ closedBall (0 : E) R) : ‖ρ x‖ = 1 := by
    have mem : x ∈ closedBall (0 : E) bump.rIn :=
      (closedBall_subset_closedBall (le_max_right 1 R)) hx
    change ‖((bump x : ℝ) : ℂ)‖ = 1
    simp [bump.one_of_mem_closedBall mem]
  let C := ENNReal.ofReal A * eLpNorm (ρ : E → ℂ) (ENNReal.ofReal (3 / 2)) volume *
    eLpNorm (ρ : E → ℂ) (ENNReal.ofReal 3) volume
  have Cf : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ρ.memLp _ volume).eLpNorm_lt_top)
    (ρ.memLp _ volume).eLpNorm_lt_top
  refine ⟨C, Cf, compact_weighted_kernel_action_W13 K smooth ρ A A0 ?_⟩
  intro x y
  by_cases both : (x,y) ∈ D
  · rw [ρone x both.1, ρone y both.2, mul_one, mul_one]
    have h : max ‖K x y‖ ‖compactKernelDx K x y‖ ≤ A := hh (x,y) both
    exact ⟨(le_max_left ‖K x y‖ ‖compactKernelDx K x y‖).trans h,
      (le_max_right ‖K x y‖ ‖compactKernelDx K x y‖).trans h⟩
  · have outside : x ∉ closedBall (0 : E) R ∨ y ∉ closedBall (0 : E) R := by
      simpa only [D, mem_prod, not_and_or] using both
    rw [support x y outside, compact_kernel_dx_zero_outside K smooth R support x y outside, norm_zero, norm_zero]
    exact ⟨by positivity, by positivity⟩


end Burnett.A03
