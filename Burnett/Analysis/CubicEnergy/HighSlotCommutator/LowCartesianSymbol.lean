import Burnett.Analysis.CubicEnergy.FourierPairing
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

open Set Metric Filter
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Topology

namespace Burnett.A06

/-- The two independent variables left after separating the low angle. -/
def normalizedHighPair (x : Joint) : Joint :=
  (‖x.2‖⁻¹ • x.1, ‖x.2‖⁻¹ • x.2)

/-- The Cartesian order-one symbol, with its cutoff in the squared low ratio. -/
def lowCartesianSymbol (χ : ℝ → ℝ) (c : Joint → ℂ) (x : Joint) : ℂ :=
  ‖x.2‖ • (χ (‖(normalizedHighPair x).1‖ ^ 2) • c (normalizedHighPair x))

/-- The fixed infrared multiplier acts on the high radius only. -/
def regularizedLowCartesianSymbol (η χ : ℝ → ℝ) (c : Joint → ℂ) (x : Joint) : ℂ :=
  η ‖x.2‖ • lowCartesianSymbol χ c x

theorem normalizedHighPair_smul (a : ℝ) (ha : 0 < a) (x : Joint) :
    normalizedHighPair (a • x) = normalizedHighPair x := by
  have scale : ‖a • x.2‖⁻¹ * a = ‖x.2‖⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg ha.le, mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ ha.ne', mul_one]
  change (‖a • x.2‖⁻¹ • (a • x.1), ‖a • x.2‖⁻¹ • (a • x.2)) = _
  rw [smul_smul, smul_smul, scale]
  rfl

theorem lowCartesianSymbol_smul (χ : ℝ → ℝ) (c : Joint → ℂ)
    (a : ℝ) (ha : 0 < a) (x : Joint) :
    lowCartesianSymbol χ c (a • x) = a • lowCartesianSymbol χ c x := by
  unfold lowCartesianSymbol
  rw [normalizedHighPair_smul a ha x]
  change ‖a • x.2‖ • _ = a • (‖x.2‖ • _)
  rw [norm_smul, Real.norm_of_nonneg ha.le]
  exact mul_smul a ‖x.2‖ _

private theorem norm_normalizedHighPair_fst (x : Joint) :
    ‖(normalizedHighPair x).1‖ = ‖x.1‖ / ‖x.2‖ := by
  change ‖‖x.2‖⁻¹ • x.1‖ = _
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), div_eq_mul_inv, mul_comm]

private theorem norm_normalizedHighPair_snd {x : Joint} (hx : x.2 ≠ 0) :
    ‖(normalizedHighPair x).2‖ = 1 := by
  exact norm_smul_inv_norm (𝕜 := ℝ) hx

private theorem contDiffAt_normalizedHighPair {n : WithTop ℕ∞} {x : Joint} (hx : x.2 ≠ 0) :
    ContDiffAt ℝ n normalizedHighPair x := by
  have hsize : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖) x :=
    (contDiffAt_norm ℝ hx).comp x contDiffAt_snd
  have hi : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖⁻¹) x :=
    hsize.inv (norm_ne_zero_iff.mpr hx)
  exact (hi.smul contDiffAt_fst).prodMk (hi.smul contDiffAt_snd)

theorem lowCartesianSymbol_eq_zero_outside (χ : ℝ → ℝ) (c : Joint → ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hχ : ∀ s ≥ ρ^2, χ s = 0) {x : Joint}
    (h : ρ * ‖x.2‖ ≤ ‖x.1‖) : lowCartesianSymbol χ c x = 0 := by
  by_cases hx : x.2 = 0
  · simp [lowCartesianSymbol, hx]
  have hnorm : ρ ≤ ‖(normalizedHighPair x).1‖ := by
    rw [norm_normalizedHighPair_fst]
    exact (le_div_iff₀ (norm_pos_iff.mpr hx)).mpr h
  have hsq := pow_le_pow_left₀ hρ hnorm 2
  simp only [lowCartesianSymbol, hχ _ hsq, zero_smul, smul_zero]

theorem lowCartesianSymbol_contDiffAt {n : WithTop ℕ∞} (χ : ℝ → ℝ) (c : Joint → ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hχ : ContDiff ℝ n χ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ n c V) {x : Joint} (hx : x.2 ≠ 0) :
    ContDiffAt ℝ n (lowCartesianSymbol χ c) x := by
  by_cases hin : ‖x.1‖ ≤ ρ * ‖x.2‖
  · have hnorm : ‖(normalizedHighPair x).1‖ ≤ ρ := by
      rw [norm_normalizedHighPair_fst]
      exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr hin
    have hxV : normalizedHighPair x ∈ V :=
      hContains ⟨mem_closedBall_zero_iff.mpr hnorm,
        mem_sphere_zero_iff_norm.mpr (norm_normalizedHighPair_snd hx)⟩
    have hpair := contDiffAt_normalizedHighPair (n := n) hx
    have hc' : ContDiffAt ℝ n (fun y => c (normalizedHighPair y)) x :=
      ((hc _ hxV).contDiffAt (hV.mem_nhds hxV)).comp x hpair
    have hsquare : ContDiffAt ℝ n (fun y => ‖(normalizedHighPair y).1‖ ^ 2) x :=
      (contDiff_norm_sq ℝ).contDiffAt.comp x (contDiffAt_fst.comp x hpair)
    have hmask := hχ.contDiffAt.comp x hsquare
    have hsize : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖) x :=
      (contDiffAt_norm ℝ hx).comp x contDiffAt_snd
    exact hsize.smul (hmask.smul hc')
  · have near : ∀ᶠ y : Joint in 𝓝 x, ρ * ‖y.2‖ < ‖y.1‖ :=
      (isOpen_lt (continuous_const.mul continuous_snd.norm) continuous_fst.norm).mem_nhds
        (lt_of_not_ge hin)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    exact lowCartesianSymbol_eq_zero_outside χ c hρ hcut hy.le

theorem regularizedLowCartesianSymbol_contDiff {n : WithTop ℕ∞}
    (η χ : ℝ → ℝ) (c : Joint → ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ)
    (hη : ContDiff ℝ n η) (hηzero : ∀ s ≤ r, η s = 0)
    (hχ : ContDiff ℝ n χ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ n c V) :
    ContDiff ℝ n (regularizedLowCartesianSymbol η χ c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x.2 = 0
  · have near : ∀ᶠ y : Joint in 𝓝 x, ‖y.2‖ < r :=
      (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simpa [hx] using hr)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [near] with y hy
    simp only [regularizedLowCartesianSymbol, hηzero _ hy.le, zero_smul]
  · have hsize : ContDiffAt ℝ n (fun y : Joint => ‖y.2‖) x :=
      (contDiffAt_norm ℝ hx).comp x contDiffAt_snd
    exact (hη.contDiffAt.comp x hsize).smul
      (lowCartesianSymbol_contDiffAt χ c hρ hχ hcut hV hContains hc hx)

theorem lowCartesianSymbol_iteratedFDeriv_smul (n : ℕ) (χ : ℝ → ℝ) (c : Joint → ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hχ : ContDiff ℝ n χ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ n c V) (a : ℝ) (ha : 0 < a) (x : Joint) (hx : x.2 ≠ 0) :
    (a^n) • iteratedFDeriv ℝ n (lowCartesianSymbol χ c) (a • x) =
      a • iteratedFDeriv ℝ n (lowCartesianSymbol χ c) x := by
  let b := lowCartesianSymbol χ c
  let U : Set Joint := {y | y.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hb : ContDiffOn ℝ n b U := fun _ hy =>
    (lowCartesianSymbol_contDiffAt χ c hρ hχ hcut hV hContains hc hy).contDiffWithinAt
  let T : Joint →L[ℝ] Joint := a • ContinuousLinearMap.id ℝ Joint
  have hT (y : Joint) : T y = a • y := rfl
  have hTx : T x ∈ U := smul_ne_zero ha.ne' hx
  have hpre : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
  have hcomp : b ∘ T = fun y => a • b y := funext (lowCartesianSymbol_smul χ c a ha)
  have hd := T.iteratedFDerivWithin_comp_right hb hU.uniqueDiffOn hpre.uniqueDiffOn
    (x := x) hTx (le_rfl : (n : WithTop ℕ∞) ≤ n)
  rw [iteratedFDerivWithin_of_isOpen n hpre (show x ∈ T ⁻¹' U from hTx),
    iteratedFDerivWithin_of_isOpen n hU hTx, hcomp] at hd
  have hbAt : ContDiffAt ℝ n b x :=
    lowCartesianSymbol_contDiffAt χ c hρ hχ hcut hV hContains hc hx
  rw [iteratedFDeriv_const_smul_apply' (a := a) hbAt] at hd
  apply ContinuousMultilinearMap.ext
  intro v
  have eq := DFunLike.congr_fun hd.symm v
  change (iteratedFDeriv ℝ n b (a • x)) (fun i => a • v i) =
    a • (iteratedFDeriv ℝ n b x) v at eq
  simpa only [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ContinuousMultilinearMap.smul_apply] using eq

end Burnett.A06
