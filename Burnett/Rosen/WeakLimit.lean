import Burnett.Rosen.Screen
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# General Rosen plane waves

The vacuum trace equation and weak lower semicontinuity of the screen energy.
-/

set_option autoImplicit false

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Burnett.RosenGeneralLSC
open Filter MeasureTheory Set
open scoped BigOperators Topology ContDiff

variable {ι : Type*} [Fintype ι]

def frameEnergy (A : Matrix ι ι ℝ) : ℝ := ∑ k : ι × ι, (A k.1 k.2)^2

def framePair (A B : Matrix ι ι ℝ) : ℝ := ∑ k : ι × ι, A k.1 k.2 * B k.1 k.2

theorem frameEnergy_eq_nested (A : Matrix ι ι ℝ) :
    frameEnergy A = ∑ i, ∑ j, A i j ^ 2 := by
  simp [frameEnergy, Fintype.sum_prod_type]

theorem frameEnergy_nonneg (A : Matrix ι ι ℝ) : 0 ≤ frameEnergy A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem frameEnergy_sub (A B : Matrix ι ι ℝ) :
    frameEnergy (A - B) = frameEnergy A - 2 * framePair A B + frameEnergy B := by
  unfold frameEnergy framePair
  simp only [Matrix.sub_apply, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  ring

def LocalMatrixWeakStar (U : Set ℝ) (A : ℕ → ℝ → Matrix ι ι ℝ)
    (B : ℝ → Matrix ι ι ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ U → ∀ w : ℝ → ℝ,
    IntegrableOn w K → ∀ i j : ι,
      Tendsto (fun n => ∫ u in K, w u * A n u i j) atTop
        (𝓝 (∫ u in K, w u * B u i j))

theorem continuousOn_frameEnergy {U : Set ℝ} (A : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun u => A u i j) U) :
    ContinuousOn (fun u => frameEnergy (A u)) U := by
  unfold frameEnergy
  exact continuousOn_finset_sum _ (fun k _ => (hA k.1 k.2).pow 2)

theorem continuousOn_framePair {U : Set ℝ} (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun u => A u i j) U)
    (hB : ∀ i j, ContinuousOn (fun u => B u i j) U) :
    ContinuousOn (fun u => framePair (A u) (B u)) U := by
  unfold framePair
  exact continuousOn_finset_sum _ (fun k _ => (hA k.1 k.2).mul (hB k.1 k.2))

theorem weighted_frame_lsc_of_cross_pairings {U K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ U)
    (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContinuousOn (fun u => A n u i j) U)
    (hB : ∀ i j, ContinuousOn (fun u => B u i j) U)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ K) (hθ0 : ∀ u ∈ K, 0 ≤ θ u)
    (hLimitCross : ∀ k : ι × ι,
      Tendsto (fun n => ∫ u in K, θ u * B u k.1 k.2 * A n u k.1 k.2) atTop
        (𝓝 (∫ u in K, θ u * B u k.1 k.2 * B u k.1 k.2)))
    (q : ℝ) (hq : Tendsto (fun n => ∫ u in K, θ u * frameEnergy (A n u)) atTop (𝓝 q)) :
    (∫ u in K, θ u * frameEnergy (B u)) ≤ q := by
  have hBK (i j : ι) := (hB i j).mono hKU
  have hAK (n : ℕ) (i j : ι) := (hA n i j).mono hKU
  have hCross (n : ℕ) (k : ι × ι) :
      IntegrableOn (fun u => θ u * B u k.1 k.2 * A n u k.1 k.2) K :=
    ((hθ.mul (hBK k.1 k.2)).mul (hAK n k.1 k.2)).integrableOn_compact hK
  have hE : IntegrableOn (fun u => θ u * frameEnergy (B u)) K :=
    (hθ.mul (continuousOn_frameEnergy B hBK)).integrableOn_compact hK
  have hCn (n : ℕ) :
      IntegrableOn (fun u => θ u * framePair (A n u) (B u)) K :=
    (hθ.mul (continuousOn_framePair (A n) B (hAK n) hBK)).integrableOn_compact hK
  have hCrossSum (n : ℕ) :
      (∫ u in K, θ u * framePair (A n u) (B u)) =
        ∑ k : ι × ι, ∫ u in K, θ u * B u k.1 k.2 * A n u k.1 k.2 := by
    simp only [framePair, Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards with u
      ring
    · intro k _
      exact (hCross n k).congr (by filter_upwards with u; ring)
  have hLimitSum : (∑ k : ι × ι, ∫ u in K, θ u * B u k.1 k.2 * B u k.1 k.2) =
      ∫ u in K, θ u * frameEnergy (B u) := by
    simp only [frameEnergy, Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards with u
      ring
    · intro k _
      exact ((hθ.mul (hBK k.1 k.2)).mul (hBK k.1 k.2)).integrableOn_compact hK
        |>.congr (by filter_upwards with u; ring)
  have hC : Tendsto (fun n => ∫ u in K, θ u * framePair (A n u) (B u)) atTop
      (𝓝 (∫ u in K, θ u * frameEnergy (B u))) := by
    simp_rw [hCrossSum]
    rw [← hLimitSum]
    exact tendsto_finset_sum _ (fun k _ => hLimitCross k)
  have hNonneg (n : ℕ) : 0 ≤
      (∫ u in K, θ u * frameEnergy (A n u)) -
        2 * (∫ u in K, θ u * framePair (A n u) (B u)) +
          (∫ u in K, θ u * frameEnergy (B u)) := by
    have hEA : IntegrableOn (fun u => θ u * frameEnergy (A n u)) K :=
      (hθ.mul (continuousOn_frameEnergy (A n) (hAK n))).integrableOn_compact hK
    have hIdent : (fun u => θ u * frameEnergy (A n u - B u)) =
        fun u => θ u * frameEnergy (A n u) - 2 * (θ u * framePair (A n u) (B u)) +
          θ u * frameEnergy (B u) := by
      funext u
      rw [frameEnergy_sub]
      ring
    have hPos : 0 ≤ ∫ u in K, θ u * frameEnergy (A n u - B u) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with u hu
      exact mul_nonneg (hθ0 u hu) (frameEnergy_nonneg _)
    rw [hIdent] at hPos
    have hAdd := integral_add (hEA.sub ((hCn n).const_mul 2)) hE
    have hSub := integral_sub hEA ((hCn n).const_mul 2)
    simp only [Pi.sub_def] at hAdd hSub
    rw [hAdd, hSub, integral_const_mul] at hPos
    exact hPos
  have hLim : Tendsto (fun n =>
      (∫ u in K, θ u * frameEnergy (A n u)) -
        2 * (∫ u in K, θ u * framePair (A n u) (B u)) +
          (∫ u in K, θ u * frameEnergy (B u))) atTop
      (𝓝 (q - 2 * (∫ u in K, θ u * frameEnergy (B u)) +
        (∫ u in K, θ u * frameEnergy (B u)))) :=
    (hq.sub (tendsto_const_nhds.mul hC)).add tendsto_const_nhds
  have hh := ge_of_tendsto hLim (Filter.Eventually.of_forall hNonneg)
  linarith

theorem weighted_frame_lsc_on_compact {U K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ U)
    (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContinuousOn (fun u => A n u i j) U)
    (hB : ∀ i j, ContinuousOn (fun u => B u i j) U)
    (hw : LocalMatrixWeakStar U A B) (θ : ℝ → ℝ)
    (hθ : ContinuousOn θ K) (hθ0 : ∀ u ∈ K, 0 ≤ θ u)
    (q : ℝ) (hq : Tendsto (fun n => ∫ u in K, θ u * frameEnergy (A n u)) atTop (𝓝 q)) :
    (∫ u in K, θ u * frameEnergy (B u)) ≤ q := by
  apply weighted_frame_lsc_of_cross_pairings hK hKU A B hA hB θ hθ hθ0 _ q hq
  intro k
  exact hw K hK hKU _
    ((hθ.mul ((hB k.1 k.2).mono hKU)).integrableOn_compact hK) k.1 k.2

def LocalC1MatrixPairings (U : Set ℝ) (A : ℕ → ℝ → Matrix ι ι ℝ)
    (B : ℝ → Matrix ι ι ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → ∀ w : ℝ → ℝ,
    ContDiffOn ℝ 1 w U → ∀ i j : ι,
      Tendsto (fun n => ∫ u in Icc a b, w u * A n u i j) atTop
        (𝓝 (∫ u in Icc a b, w u * B u i j))

theorem weighted_frame_lsc_on_interval {U : Set ℝ} (a b : ℝ) (hab : a ≤ b)
    (hKU : Icc a b ⊆ U) (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContinuousOn (fun u => A n u i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun u => B u i j) U)
    (hw : LocalC1MatrixPairings U A B) (θ : ℝ → ℝ)
    (hθ : ContDiffOn ℝ 1 θ U) (hθ0 : ∀ u ∈ Icc a b, 0 ≤ θ u)
    (q : ℝ) (hq : Tendsto (fun n => ∫ u in Icc a b, θ u * frameEnergy (A n u)) atTop (𝓝 q)) :
    (∫ u in Icc a b, θ u * frameEnergy (B u)) ≤ q := by
  apply weighted_frame_lsc_of_cross_pairings isCompact_Icc hKU A B hA
    (fun i j => (hB i j).continuousOn) θ (hθ.continuousOn.mono hKU) hθ0 _ q hq
  intro k
  exact hw a b hab hKU _ (hθ.mul ((hB k.1 k.2).of_le (by simp))) k.1 k.2

end Burnett.RosenGeneralLSC

namespace Burnett.RosenGeneralLSC
open Filter MeasureTheory Set
open scoped BigOperators Topology ContDiff

theorem continuous_test_mul_local {U : Set ℝ} (hU : IsOpen U) (f θ : ℝ → ℝ)
    (hf : ContinuousOn f U) (hθ : Continuous θ) (hs : tsupport θ ⊆ U) :
    Continuous (fun u => θ u * f u) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hθ.continuousAt.mul (hf.continuousAt (hU.mem_nhds hx))
  · have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    have hp : (fun u => θ u * f u) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      hz.mono (fun u hu => by simp [hu])
    exact continuousAt_const.congr_of_eventuallyEq hp

theorem contDiff_test_mul_local {U : Set ℝ} (hU : IsOpen U) (f θ : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (hθ : ContDiff ℝ ∞ θ) (hs : tsupport θ ⊆ U) :
    ContDiff ℝ ∞ (fun u => θ u * f u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hθ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    have hp : (fun u => θ u * f u) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      hz.mono (fun u hu => by simp [hu])
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x)
      |>.congr_of_eventuallyEq hp

theorem tsupport_deriv_subset (f : ℝ → ℝ) : tsupport (deriv f) ⊆ tsupport f :=
  closure_minimal support_deriv_subset isClosed_closure

theorem integral_deriv_compact_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : (∫ u, deriv f u) = 0 := by
  have hD : Continuous (fun u => fderiv ℝ f u (1 : ℝ)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiD : Integrable (fun u => fderiv ℝ f u (1 : ℝ)) :=
    hD.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ 1)
  have hi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℝ)) (f := fun _ : ℝ => (1 : ℝ)) (g := f) (v := 1)
    (by simp) (by simpa using hiD) (by simpa using hi)
    (differentiable_const (1 : ℝ)) (hf.differentiable (by simp))
  simpa only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul,
    integral_zero, neg_zero, fderiv_deriv] using hh

theorem local_test_integration_by_parts {U : Set ℝ} (hU : IsOpen U)
    (f θ : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f U) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ U) :
    Integrable (fun u => θ u * deriv f u) ∧ Integrable (fun u => deriv θ u * f u) ∧
      (∫ u, θ u * deriv f u) = -(∫ u, deriv θ u * f u) := by
  have hp : ContDiff ℝ ∞ (fun u => θ u * f u) := contDiff_test_mul_local hU f θ hf hθ hs
  have hpc : HasCompactSupport (fun u => θ u * f u) := hc.mul_right
  have hdθ : ContDiff ℝ ∞ (deriv θ) := hθ.deriv'
  have hds : tsupport (deriv θ) ⊆ U := (tsupport_deriv_subset θ).trans hs
  have hq : ContDiff ℝ ∞ (fun u => deriv θ u * f u) :=
    contDiff_test_mul_local hU f (deriv θ) hf hdθ hds
  have hqi : Integrable (fun u => deriv θ u * f u) :=
    hq.continuous.integrable_of_hasCompactSupport hc.deriv.mul_right
  have hdpi : Integrable (deriv (fun u => θ u * f u)) :=
    (hp.continuous_deriv (by simp)).integrable_of_hasCompactSupport hpc.deriv
  have hDeriv (x : ℝ) : deriv (fun u => θ u * f u) x =
      deriv θ x * f x + θ x * deriv f x := by
    by_cases hx : x ∈ U
    · exact deriv_mul (hθ.differentiable (by simp) x)
        ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    · have hz : θ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
      have hθx : θ x = 0 := hz.eq_of_nhds
      have hθd : deriv θ x = 0 := hz.deriv_eq.trans (deriv_const x 0)
      have hprod : (fun u => θ u * f u) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
        hz.mono (fun u hu => by simp [hu])
      have hpd : deriv (fun u => θ u * f u) x = 0 :=
        hprod.deriv_eq.trans (deriv_const x 0)
      rw [hpd, hθx, hθd]
      ring
  have hpi : Integrable (fun u => θ u * deriv f u) := by
    apply (hdpi.sub hqi).congr
    filter_upwards with u
    change deriv (fun u => θ u * f u) u - deriv θ u * f u = θ u * deriv f u
    rw [hDeriv]
    ring
  have hz := integral_deriv_compact_zero (fun u => θ u * f u) hp hpc
  have heq : (∫ u, deriv (fun u => θ u * f u) u) =
      (∫ u, deriv θ u * f u) + ∫ u, θ u * deriv f u := by
    simp_rw [hDeriv]
    exact integral_add hqi hpi
  refine ⟨hpi, hqi, ?_⟩
  linarith

theorem nonneg_of_smooth_test_integrals {U : Set ℝ} (hU : IsOpen U) (ρ : ℝ → ℝ)
    (hρ : ContinuousOn ρ U)
    (h : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∀ u, 0 ≤ θ u) → 0 ≤ ∫ u, θ u * ρ u) : ∀ u ∈ U, 0 ≤ ρ u := by
  intro x hx
  by_contra hn
  have hneg : ρ x < 0 := lt_of_not_ge hn
  have hnN : {u : ℝ | u ∈ U ∧ ρ u < 0} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hx,
      (hρ.continuousAt (hU.mem_nhds hx)).eventually (Iio_mem_nhds hneg)] with u hu hnu
    exact ⟨hu, hnu⟩
  obtain ⟨θ, hθs, hθc, hθ, hθrange, hθx⟩ := exists_smooth_tsupport_subset hnN
  have hsU : tsupport θ ⊆ U := fun u hu => (hθs hu).1
  have hθnonneg : ∀ u, 0 ≤ θ u := fun u => (hθrange (mem_range_self u)).1
  have hcont : Continuous (fun u => -(θ u * ρ u)) :=
    (continuous_test_mul_local hU ρ θ hρ hθ.continuous hsU).neg
  have hc : HasCompactSupport (fun u => -(θ u * ρ u)) :=
    (hθc.mul_right : HasCompactSupport (fun u => θ u * ρ u)).neg
  have hnn : ∀ u, 0 ≤ -(θ u * ρ u) := by
    intro u
    by_cases hz : θ u = 0
    · simp [hz]
    · have hρn := (hθs (subset_tsupport θ hz)).2
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hθnonneg u) hρn.le)
  have hne : -(θ x * ρ x) ≠ 0 := by
    rw [hθx, one_mul]
    exact neg_ne_zero.mpr hneg.ne
  have hpos : 0 < ∫ u, -(θ u * ρ u) :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hc hnn hne
  rw [integral_neg] at hpos
  have hnnInt := h θ hθ hθc hsU hθnonneg
  linarith

end Burnett.RosenGeneralLSC

namespace Burnett.RosenGeneralLSC
open Filter MeasureTheory Set
open scoped BigOperators Topology ContDiff
variable {ι : Type*} [Fintype ι]

def traceField (A : ℝ → Matrix ι ι ℝ) (u : ℝ) : ℝ := Matrix.trace (A u)

def limitDensity (A : ℝ → Matrix ι ι ℝ) (u : ℝ) : ℝ :=
  -deriv (traceField A) u - frameEnergy (A u)

theorem contDiffOn_traceField {U : Set ℝ} (A : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun u => A u i j) U) :
    ContDiffOn ℝ ∞ (traceField A) U := by
  simpa only [traceField, Matrix.trace, Matrix.diag_apply] using
    (ContDiffOn.sum (s := Finset.univ) (fun i _ => hA i i))

theorem continuousOn_limitDensity {U : Set ℝ} (hU : IsOpen U) (A : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun u => A u i j) U) :
    ContinuousOn (limitDensity A) U :=
  ((contDiffOn_traceField A hA).continuousOn_deriv_of_isOpen hU (by simp)).neg.sub
    (continuousOn_frameEnergy A (fun i j => (hA i j).continuousOn))

theorem integral_mul_traceField {K : Set ℝ} (hK : IsCompact K)
    (A : ℝ → Matrix ι ι ℝ) (w : ℝ → ℝ)
    (hA : ∀ i j, ContinuousOn (fun u => A u i j) K) (hw : ContinuousOn w K) :
    (∫ u in K, w u * traceField A u) = ∑ i : ι, ∫ u in K, w u * A u i i := by
  simp only [traceField, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  rw [integral_finset_sum]
  intro i _
  exact (hw.mul (hA i i)).integrableOn_compact hK

theorem trace_pairings_on_interval {U : Set ℝ} (a b : ℝ) (hab : a ≤ b)
    (hJU : Icc a b ⊆ U) (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContinuousOn (fun u => A n u i j) U)
    (hB : ∀ i j, ContinuousOn (fun u => B u i j) U)
    (hw : LocalC1MatrixPairings U A B) (w : ℝ → ℝ) (hw1 : ContDiffOn ℝ 1 w U) :
    Tendsto (fun n => ∫ u in Icc a b, w u * traceField (A n) u) atTop
      (𝓝 (∫ u in Icc a b, w u * traceField B u)) := by
  have hn (n : ℕ) := integral_mul_traceField isCompact_Icc (A n) w
    (fun i j => (hA n i j).mono hJU) (hw1.continuousOn.mono hJU)
  have h0 := integral_mul_traceField isCompact_Icc B w
    (fun i j => (hB i j).mono hJU) (hw1.continuousOn.mono hJU)
  simp_rw [hn]
  rw [h0]
  exact tendsto_finset_sum _ (fun i _ => hw a b hab hJU w hw1 i i)

theorem setIntegral_test_mul_eq_global {K : Set ℝ} (f θ : ℝ → ℝ)
    (hs : tsupport θ ⊆ K) : (∫ u in K, θ u * f u) = ∫ u, θ u * f u := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hθu : θ u = 0 := by
    by_contra hn
    exact hu (hs (subset_tsupport θ hn))
  rw [hθu, zero_mul]

theorem vacuum_test_identity {U : Set ℝ} (hU : IsOpen U) (A : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun u => A u i j) U)
    (hvac : ∀ u ∈ U, -deriv (traceField A) u = frameEnergy (A u))
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ U) :
    (∫ u, θ u * frameEnergy (A u)) = ∫ u, deriv θ u * traceField A u := by
  have hi := local_test_integration_by_parts hU (traceField A) θ
    (contDiffOn_traceField A hA) hθ hc hs
  have heq : (fun u => θ u * frameEnergy (A u)) =
      fun u => -(θ u * deriv (traceField A) u) := by
    funext u
    by_cases hu : u ∈ U
    · rw [← hvac u hu]
      ring
    · have hθu : θ u = 0 := by
        by_contra hn
        exact hu (hs (subset_tsupport θ hn))
      simp [hθu]
  rw [heq, integral_neg, hi.2.2, neg_neg]

theorem weighted_vacuum_density_nonneg_on_interval {U : Set ℝ} (hU : IsOpen U)
    (a b : ℝ) (hab : a ≤ b) (hJU : Icc a b ⊆ U)
    (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContDiffOn ℝ ∞ (fun u => A n u i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun u => B u i j) U)
    (hw : LocalC1MatrixPairings U A B)
    (hvac : ∀ n u, u ∈ U → -deriv (traceField (A n)) u = frameEnergy (A n u))
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ Icc a b) (hθ0 : ∀ u, 0 ≤ θ u) :
    0 ≤ ∫ u, θ u * limitDensity B u := by
  have hsU := hs.trans hJU
  have hds := (tsupport_deriv_subset θ).trans hs
  have hdθ : ContDiff ℝ ∞ (deriv θ) := hθ.deriv'
  have hTrace := trace_pairings_on_interval a b hab hJU A B
    (fun n i j => (hA n i j).continuousOn) (fun i j => (hB i j).continuousOn) hw
    (deriv θ) (hdθ.contDiffOn.of_le (by simp))
  have hVA (n : ℕ) : (∫ u in Icc a b, θ u * frameEnergy (A n u)) =
      ∫ u in Icc a b, deriv θ u * traceField (A n) u := by
    rw [setIntegral_test_mul_eq_global _ θ hs,
      setIntegral_test_mul_eq_global _ (deriv θ) hds]
    exact vacuum_test_identity hU (A n) (hA n) (hvac n) θ hθ hc hsU
  have hq : Tendsto (fun n => ∫ u in Icc a b, θ u * frameEnergy (A n u)) atTop
      (𝓝 (∫ u in Icc a b, deriv θ u * traceField B u)) := by
    simp_rw [hVA]
    exact hTrace
  have hiB := local_test_integration_by_parts hU (traceField B) θ
    (contDiffOn_traceField B hB) hθ hc hsU
  have hBq : (∫ u in Icc a b, θ u * (-deriv (traceField B) u)) =
      ∫ u in Icc a b, deriv θ u * traceField B u := by
    rw [setIntegral_test_mul_eq_global _ θ hs,
      setIntegral_test_mul_eq_global _ (deriv θ) hds]
    have heq : (fun u => θ u * (-deriv (traceField B) u)) =
        fun u => -(θ u * deriv (traceField B) u) := by funext u; ring
    rw [heq, integral_neg, hiB.2.2, neg_neg]
  rw [← hBq] at hq
  have hLSC := weighted_frame_lsc_on_interval a b hab hJU A B
    (fun n i j => (hA n i j).continuousOn) hB hw θ (hθ.contDiffOn.of_le (by simp))
    (fun u _ => hθ0 u) _ hq
  have hIN : IntegrableOn (fun u => θ u * (-deriv (traceField B) u)) (Icc a b) :=
    (hθ.continuous.continuousOn.mul
      (((contDiffOn_traceField B hB).continuousOn_deriv_of_isOpen hU (by simp)).neg.mono hJU )).integrableOn_compact isCompact_Icc
  have hIE : IntegrableOn (fun u => θ u * frameEnergy (B u)) (Icc a b) :=
    (hθ.continuous.continuousOn.mul
      ((continuousOn_frameEnergy B (fun i j => (hB i j).continuousOn)).mono hJU )).integrableOn_compact isCompact_Icc
  have heq : (∫ u in Icc a b, θ u * limitDensity B u) =
      (∫ u in Icc a b, θ u * (-deriv (traceField B) u)) -
        ∫ u in Icc a b, θ u * frameEnergy (B u) := by
    simp only [limitDensity, mul_sub]
    exact integral_sub hIN hIE
  rw [← setIntegral_test_mul_eq_global (limitDensity B) θ hs, heq]
  exact sub_nonneg.mpr hLSC

theorem nonneg_of_local_interval_test_integrals {U : Set ℝ} (hU : IsOpen U) (ρ : ℝ → ℝ)
    (hρ : ContinuousOn ρ U)
    (h : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → ∀ θ : ℝ → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Icc a b →
        (∀ u, 0 ≤ θ u) → 0 ≤ ∫ u, θ u * ρ u) : ∀ x ∈ U, 0 ≤ ρ x := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hJU : Icc (x - ε) (x + ε) ⊆ U := by
    intro y hy
    apply hεU
    change dist y x ≤ ε
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hWU : Ioo (x - ε) (x + ε) ⊆ U := Ioo_subset_Icc_self.trans hJU
  have hp := nonneg_of_smooth_test_integrals isOpen_Ioo ρ (hρ.mono hWU) ?_
  · exact hp x ⟨by linarith, by linarith⟩
  · intro θ hθ hc hs hn
    exact h _ _ (by linarith) hJU θ hθ hc (hs.trans Ioo_subset_Icc_self) hn

theorem limitDensity_nonneg_of_vacuum {U : Set ℝ} (hU : IsOpen U)
    (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContDiffOn ℝ ∞ (fun u => A n u i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun u => B u i j) U)
    (hw : LocalC1MatrixPairings U A B)
    (hvac : ∀ n u, u ∈ U → -deriv (traceField (A n)) u = frameEnergy (A n u)) :
    ∀ u ∈ U, 0 ≤ limitDensity B u := by
  apply nonneg_of_local_interval_test_integrals hU (limitDensity B) (continuousOn_limitDensity hU B hB)
  intro a b hab hJU θ hθ hc hs hn
  exact weighted_vacuum_density_nonneg_on_interval hU a b hab hJU A B hA hB hw hvac θ hθ hc hs hn

theorem rho_nonneg_of_vacuum_trace_data {U : Set ℝ} (hU : IsOpen U)
    (A : ℕ → ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ n i j, ContDiffOn ℝ ∞ (fun u => A n u i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun u => B u i j) U)
    (hw : LocalC1MatrixPairings U A B) (τn : ℕ → ℝ → ℝ) (τ : ℝ → ℝ)
    (hnTrace : ∀ n u, u ∈ U → τn n u = traceField (A n) u)
    (hTrace : ∀ u ∈ U, τ u = traceField B u)
    (hvac : ∀ n u, u ∈ U → -deriv (τn n) u = frameEnergy (A n u)) :
    ∀ u ∈ U, 0 ≤ -deriv τ u - frameEnergy (B u) := by
  have hV (n : ℕ) (u : ℝ) (hu : u ∈ U) :
      -deriv (traceField (A n)) u = frameEnergy (A n u) := by
    have hg : τn n =ᶠ[𝓝 u] traceField (A n) := by
      filter_upwards [hU.mem_nhds hu] with y hy
      exact hnTrace n y hy
    rw [← hg.deriv_eq]
    exact hvac n u hu
  intro u hu
  have hg : τ =ᶠ[𝓝 u] traceField B := by
    filter_upwards [hU.mem_nhds hu] with y hy
    exact hTrace y hy
  rw [hg.deriv_eq]
  exact limitDensity_nonneg_of_vacuum hU A B hA hB hw hV u hu

end Burnett.RosenGeneralLSC

namespace Burnett.RosenScreen

open Filter MeasureTheory Set
open scoped ContDiff Topology

private theorem exists_Icc_smooth_cutoff {U : Set ℝ} (hU : IsOpen U) {l r : ℝ}
    (hlr : l ≤ r) (hJ : Icc l r ⊆ U) :
    ∃ a b : ℝ, a ≤ b ∧ Icc l r ⊆ Icc a b ∧ Icc a b ⊆ U ∧
      ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Icc a b ∧
        (∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) ∧ ∀ u ∈ Icc l r, ψ u = 1 := by
  obtain ⟨δl, hδl, hballL⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hJ (left_mem_Icc.mpr hlr)))
  obtain ⟨δr, hδr, hballR⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hJ (right_mem_Icc.mpr hlr)))
  let δ := min δl δr / 2
  have hδ : 0 < δ := half_pos (lt_min hδl hδr)
  have hδL : δ < δl := (half_lt_self (lt_min hδl hδr)).trans_le (min_le_left _ _)
  have hδR : δ < δr := (half_lt_self (lt_min hδl hδr)).trans_le (min_le_right _ _)
  have hOuter : Icc (l - δ) (r + δ) ⊆ U := by
    intro u hu
    by_cases hL : u < l
    · apply hballL
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hL)]
      linarith [hu.1]
    · by_cases hR : r < u
      · apply hballR
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hR)]
        linarith [hu.2]
      · exact hJ ⟨le_of_not_gt hL, le_of_not_gt hR⟩
  let m := (l + r) / 2
  let s := (r - l) / 2
  let ψ : ContDiffBump m := ⟨s + δ / 2, s + δ, by dsimp [s]; linarith, by linarith⟩
  refine ⟨l - δ, r + δ, by linarith, ?_, hOuter, ψ, ψ.contDiff, ψ.hasCompactSupport, ?_,
    fun u => ⟨ψ.nonneg' u, ψ.le_one⟩, ?_⟩
  · intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [ψ.tsupport_eq]
    intro u hu
    have h : -(s + δ) ≤ u - m ∧ u - m ≤ s + δ := abs_le.mp
      (by simpa only [Metric.mem_closedBall, Real.dist_eq] using hu)
    exact ⟨by dsimp [m, s] at *; linarith [h.1], by dsimp [m, s] at *; linarith [h.2]⟩
  · intro u hu
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(s + δ / 2) ≤ u - m ∧ u - m ≤ s + δ / 2
    constructor <;> dsimp [m, s] <;> linarith [hu.1, hu.2]

theorem tendsto_local_Icc_pairings_all_L1_of_compact_smooth {U : Set ℝ} (hU : IsOpen U)
    {qₙ : ℕ → ℝ → ℝ} {q : ℝ → ℝ}
    (hCn : ∀ n, ContinuousOn (qₙ n) U) (hCq : ContinuousOn q U)
    (hBounds : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → ∃ C : ℝ, 0 ≤ C ∧
      (∀ n, ∀ᵐ u ∂(volume.restrict (Icc a b)), ‖qₙ n u‖ ≤ C) ∧
      ∀ᵐ u ∂(volume.restrict (Icc a b)), ‖q u‖ ≤ C)
    (hSmooth : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U →
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Icc a b →
        Tendsto (fun n => ∫ u in Icc a b, θ u * qₙ n u) atTop (𝓝 (∫ u in Icc a b, θ u * q u)))
    {l r : ℝ} (hlr : l ≤ r) (hJ : Icc l r ⊆ U) (w : ℝ → ℝ) (hw : IntegrableOn w (Icc l r)) :
    Tendsto (fun n => ∫ u in Icc l r, w u * qₙ n u) atTop (𝓝 (∫ u in Icc l r, w u * q u)) := by
  obtain ⟨a, b, hab, hJK, hKU, ψ, hψ, hψc, hψs, hψB, hψ1⟩ := exists_Icc_smooth_cutoff hU hlr hJ
  obtain ⟨C, hC, hBn, hBq⟩ := hBounds a b hab hKU
  let J := Icc l r
  let K := Icc a b
  let μ : Measure ℝ := volume.restrict K
  let wn := J.indicator w
  have hwn : IntegrableOn wn K :=
    (hw.integrable_indicator measurableSet_Icc).mono_measure Measure.restrict_le_self
  let Fn (n : ℕ) (u : ℝ) := ψ u * qₙ n u
  let F (u : ℝ) := ψ u * q u
  have hm {f : ℝ → ℝ} (hf : ContinuousOn f U) :
      AEStronglyMeasurable (fun u => ψ u * f u) μ :=
    ((hψ.continuous.continuousOn.mul hf).mono hKU).aestronglyMeasurable measurableSet_Icc
  have hB {f : ℝ → ℝ} (hf : ∀ᵐ u ∂μ, ‖f u‖ ≤ C) : ∀ᵐ u ∂μ, ‖ψ u * f u‖ ≤ C := by
    filter_upwards [hf] with u hu
    rw [norm_mul, Real.norm_of_nonneg (hψB u).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hψB u).2).trans hu
  have hsmooth (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
      Tendsto (fun n => ∫ u in K, g u * Fn n u) atTop (𝓝 (∫ u in K, g u * F u)) := by
    let θ := fun u => ψ u * g u
    have hθs : tsupport θ ⊆ K := tsupport_mul_subset_left.trans hψs
    have hp := hSmooth a b hab hKU θ (hψ.mul hg) hψc.mul_right hθs
    simpa only [θ, Fn, F, mul_assoc, mul_left_comm] using hp
  have ht := tendsto_Icc_pairings_all_L1_of_smooth hab hC (fun n => hm (hCn n)) (hm hCq)
    (fun n => hB (hBn n)) (hB hBq) hsmooth wn hwn
  have heq (f : ℝ → ℝ) : (∫ u in K, wn u * (ψ u * f u)) = ∫ u in J, w u * f u := by
    calc
      (∫ u in K, wn u * (ψ u * f u)) = ∫ u in K, J.indicator (fun x => w x * f x) u := by
        apply integral_congr_ae
        refine Eventually.of_forall fun u => ?_
        by_cases hu : u ∈ J
        · simp only [wn, indicator_of_mem hu, hψ1 u hu, one_mul]
        · simp only [wn, indicator_of_notMem hu, zero_mul]
      _ = _ := by
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          inter_eq_left.mpr hJK]
  have hEqSeq : (fun n => ∫ u in K, wn u * Fn n u) = (fun n => ∫ u in J, w u * qₙ n u) :=
    funext fun n => heq (qₙ n)
  change Tendsto (fun n => ∫ u in K, wn u * Fn n u) atTop
    (𝓝 (∫ u in K, wn u * (ψ u * q u))) at ht
  rw [hEqSeq, heq q] at ht
  exact ht

end Burnett.RosenScreen

namespace Burnett.RosenScreen

open Filter Matrix MeasureTheory RosenGeneralLSC Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Elementwise Topology

def curveScreenShape (γ : ℝ → Screen2) (u : ℝ) : Screen2 :=
  screenL (γ u) (fun a b => deriv (fun t => γ t a b) u)

def curveScreenMatrix (γ : ℝ → Screen2) (u : ℝ) : Screen2 :=
  screenS (γ u) (fun a b => deriv (fun t => γ t a b) u)

def curveScreenTrace (γ : ℝ → Screen2) (u : ℝ) : ℝ := Matrix.trace (curveScreenShape γ u)

theorem curveScreenTrace_eq_traceField (γ : ℝ → Screen2) (u : ℝ) (hPos : (γ u).PosDef) :
    curveScreenTrace γ u = traceField (curveScreenMatrix γ) u :=
  trace_screenL_eq_trace_screenS _ _ hPos

theorem curveScreenEnergy_eq_trace_shape_sq {U : Set ℝ} (hU : IsOpen U) (γ : ℝ → Screen2)
    (hPos : ∀ u ∈ U, (γ u).PosDef) (u : ℝ) (hu : u ∈ U) :
    frameEnergy (curveScreenMatrix γ u) = Matrix.trace ((curveScreenShape γ u) ^ 2) := by
  rw [frameEnergy_eq_nested]
  exact (trace_screenL_sq_eq_sum_screenS_sq _ _ (hPos u hu) (screenDeriv2_isSymm γ U hU hPos u hu)).symm

private theorem frameEnergy_norm_le_of_matrix_norm {A : Screen2} {M : ℝ}
    (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) : ‖frameEnergy A‖ ≤ 4 * M ^ 2 := by
  rw [Real.norm_of_nonneg (frameEnergy_nonneg A), frameEnergy]
  calc
    _ ≤ ∑ _k : Fin 2 × Fin 2, M ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      have h := (dist_le_pi_dist (A k.1) ((0 : Screen2) k.1) k.2).trans
        (dist_le_pi_dist A (0 : Screen2) k.1)
      have hentry : ‖A k.1 k.2‖ ≤ ‖A‖ := by simpa using h
      exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hM, ← Real.norm_eq_abs] using hentry.trans hA)
    _ = 4 * M ^ 2 := by norm_num [Fintype.card_prod]

private theorem ae_matrix_norm_le_of_eLpNorm_top {μ : Measure ℝ} {A : ℝ → Screen2} {M : ℝ}
    (hM : 0 ≤ M) (hA : eLpNorm A ∞ μ ≤ ENNReal.ofReal M) : ∀ᵐ u ∂μ, ‖A u‖ ≤ M := by
  rw [eLpNorm_exponent_top] at hA
  filter_upwards [ae_le_eLpNormEssSup (f := A) (μ := μ)] with u hu
  apply (ENNReal.ofReal_le_ofReal_iff hM).mp
  rw [ofReal_norm_eq_enorm]
  exact hu.trans hA

private theorem vacuum_energy_tendsto_Icc_smooth {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ U) {A : ℕ → ℝ → Screen2} {B : ℝ → Screen2}
    (hA : ∀ n i j, ContDiffOn ℝ ∞ (fun u => A n u i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun u => B u i j) U) (hWeak : LocalC1MatrixPairings U A B)
    (hVac : ∀ n u, u ∈ U → -deriv (traceField (A n)) u = frameEnergy (A n u))
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ Icc a b) :
    Tendsto (fun n => ∫ u in Icc a b, θ u * frameEnergy (A n u)) atTop
      (𝓝 (∫ u in Icc a b, θ u * (-deriv (traceField B) u))) := by
  have hθ' : ContDiff ℝ 1 (deriv θ) := (contDiff_infty.mp hθ.deriv') 1
  have hs' := (tsupport_deriv_subset θ).trans hs
  have ht := trace_pairings_on_interval a b hab hJ A B (fun n i j => (hA n i j).continuousOn)
    (fun i j => (hB i j).continuousOn) hWeak (deriv θ) hθ'.contDiffOn
  have hE (n : ℕ) : (∫ u in Icc a b, θ u * frameEnergy (A n u)) =
      ∫ u in Icc a b, deriv θ u * traceField (A n) u := by
    rw [setIntegral_test_mul_eq_global _ θ hs, setIntegral_test_mul_eq_global _ (deriv θ) hs']
    exact vacuum_test_identity hU (A n) (hA n) (hVac n) θ hθ hc (hs.trans hJ)
  have hQ : (∫ u in Icc a b, θ u * (-deriv (traceField B) u)) =
      ∫ u in Icc a b, deriv θ u * traceField B u := by
    rw [setIntegral_test_mul_eq_global _ θ hs, setIntegral_test_mul_eq_global _ (deriv θ) hs']
    simp_rw [mul_neg, integral_neg]
    rw [(local_test_integration_by_parts hU (traceField B) θ (contDiffOn_traceField B hB)
      hθ hc (hs.trans hJ)).2.2, neg_neg]
  simpa only [hE, hQ] using ht

theorem screenFrobeniusEnergy_LInf_weakStar_Icc {U : Set ℝ} (hU : IsOpen U)
    {γₙ : ℕ → ℝ → Screen2} {γ : ℝ → Screen2}
    (hγₙ : ∀ n i j, ContDiffOn ℝ ∞ (fun u => γₙ n u i j) U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hPosₙ : ∀ n u, u ∈ U → (γₙ n u).PosDef) (hPos : ∀ u ∈ U, (γ u).PosDef)
    (hUniform : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → ∀ i j,
      TendstoUniformlyOn (fun n u => γₙ n u i j) (fun u => γ u i j) atTop (Icc a b))
    (hDeriv : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n i j u, u ∈ Icc a b → ‖deriv (fun t => γₙ n t i j) u‖ ≤ C)
    (hVac : ∀ n u, u ∈ U →
      -deriv (curveScreenTrace (γₙ n)) u = Matrix.trace ((curveScreenShape (γₙ n) u) ^ 2))
    {l r : ℝ} (hlr : l ≤ r) (hJ : Icc l r ⊆ U) :
    let μ : Measure ℝ := volume.restrict (Icc l r)
    let E := fun (n : ℕ) u => frameEnergy (curveScreenMatrix (γₙ n) u)
    let Q := fun u => -deriv (curveScreenTrace γ) u
    ∃ C : ℝ, 0 ≤ C ∧ (∀ n, eLpNorm (E n) ∞ μ ≤ ENNReal.ofReal C) ∧
      eLpNorm Q ∞ μ ≤ ENNReal.ofReal C ∧
      ∀ w : ℝ → ℝ, Integrable w μ →
        (∀ n, Integrable (fun u => w u * E n u) μ) ∧ Integrable (fun u => w u * Q u) μ ∧
          Tendsto (fun n => ∫ u, w u * E n u ∂μ) atTop (𝓝 (∫ u, w u * Q u ∂μ)) := by
  dsimp only
  let A (n : ℕ) := curveScreenMatrix (γₙ n)
  let B := curveScreenMatrix γ
  let E (n : ℕ) (u : ℝ) := frameEnergy (A n u)
  let Q (u : ℝ) := -deriv (curveScreenTrace γ) u
  have hA (n : ℕ) (i j : Fin 2) : ContDiffOn ℝ ∞ (fun u => A n u i j) U :=
    screenS_deriv_entry_contDiffOn _ U hU (hγₙ n) (hPosₙ n) i j
  have hB (i j : Fin 2) : ContDiffOn ℝ ∞ (fun u => B u i j) U :=
    screenS_deriv_entry_contDiffOn _ U hU hγ hPos i j
  have hE (n : ℕ) : ContinuousOn (E n) U :=
    continuousOn_frameEnergy (A n) (fun i j => (hA n i j).continuousOn)
  have hQeq (u : ℝ) (hu : u ∈ U) : Q u = -deriv (traceField B) u := by
    have he : curveScreenTrace γ =ᶠ[𝓝 u] traceField B := by
      filter_upwards [hU.mem_nhds hu] with x hx
      exact curveScreenTrace_eq_traceField γ x (hPos x hx)
    exact congrArg Neg.neg he.deriv_eq
  have hQ : ContinuousOn Q U :=
    ((contDiffOn_traceField B hB).continuousOn_deriv_of_isOpen hU (by simp)).neg.congr hQeq
  have hV (n : ℕ) (u : ℝ) (hu : u ∈ U) : -deriv (traceField (A n)) u = E n u := by
    have he : curveScreenTrace (γₙ n) =ᶠ[𝓝 u] traceField (A n) := by
      filter_upwards [hU.mem_nhds hu] with x hx
      exact curveScreenTrace_eq_traceField _ _ (hPosₙ n x hx)
    rw [← he.deriv_eq, hVac n u hu]
    exact (curveScreenEnergy_eq_trace_shape_sq hU _ (hPosₙ n) u hu).symm
  have hWeak : LocalC1MatrixPairings U A B := by
    intro a b hab hK w hw i j
    obtain ⟨C, hC, hD⟩ := hDeriv a b hab hK
    exact tendsto_restrict_Icc_screenS_deriv_mul_test hab hU hK hγₙ hγ hPosₙ hPos
      (hUniform a b hab hK) hC hD hw i j
  have hBounds (a b : ℝ) (hab : a ≤ b) (hK : Icc a b ⊆ U) : ∃ C : ℝ, 0 ≤ C ∧
      (∀ n, ∀ᵐ u ∂(volume.restrict (Icc a b)), ‖E n u‖ ≤ C) ∧
      ∀ᵐ u ∂(volume.restrict (Icc a b)), ‖Q u‖ ≤ C := by
    obtain ⟨D, hD0, hD⟩ := hDeriv a b hab hK
    obtain ⟨M, hM, hNorm, _⟩ := screenS_deriv_LInf_weakStar_Icc hab hU hK hγₙ hγ hPosₙ hPos
      (hUniform a b hab hK) hD0 hD
    obtain ⟨P, hP⟩ := isCompact_Icc.bddAbove_image (hQ.mono hK).norm
    let C := max (4 * M ^ 2) P
    refine ⟨C, (by exact (show 0 ≤ 4 * M ^ 2 by positivity).trans (le_max_left _ _)), ?_, ?_⟩
    · intro n
      filter_upwards [ae_matrix_norm_le_of_eLpNorm_top hM (hNorm n)] with u hu
      exact (frameEnergy_norm_le_of_matrix_norm hM hu).trans (le_max_left _ _)
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with u hu
      exact (hP (mem_image_of_mem _ hu)).trans (le_max_right _ _)
  have hs (a b : ℝ) (hab : a ≤ b) (hK : Icc a b ⊆ U) (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
      (hc : HasCompactSupport θ) (hθK : tsupport θ ⊆ Icc a b) :
      Tendsto (fun n => ∫ u in Icc a b, θ u * E n u) atTop (𝓝 (∫ u in Icc a b, θ u * Q u)) := by
    have he : (∫ u in Icc a b, θ u * Q u) = ∫ u in Icc a b, θ u * (-deriv (traceField B) u) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      exact congrArg (fun q => θ u * q) (hQeq u (hK hu))
    rw [he]
    exact vacuum_energy_tendsto_Icc_smooth hU hab hK hA hB hWeak hV θ hθ hc hθK
  obtain ⟨C, hC, hEB, hQB⟩ := hBounds l r hlr hJ
  have hNorm (F : ℝ → ℝ) (hF : ∀ᵐ u ∂(volume.restrict (Icc l r)), ‖F u‖ ≤ C) :
      eLpNorm F ∞ (volume.restrict (Icc l r)) ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hF
  refine ⟨C, hC, fun n => hNorm _ (hEB n), hNorm _ hQB, ?_⟩
  intro w hw
  refine ⟨fun n => ?_, ?_, tendsto_local_Icc_pairings_all_L1_of_compact_smooth hU hE hQ hBounds hs hlr hJ w hw⟩
  · simpa only [mul_comm] using hw.bdd_mul' (((hE n).mono hJ).aestronglyMeasurable measurableSet_Icc) (hEB n)
  · simpa only [mul_comm] using hw.bdd_mul' ((hQ.mono hJ).aestronglyMeasurable measurableSet_Icc) hQB

end Burnett.RosenScreen
