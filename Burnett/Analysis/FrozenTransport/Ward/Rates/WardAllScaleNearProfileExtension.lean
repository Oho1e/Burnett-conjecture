import Burnett.Analysis.GaugeProjection.GaugeProjectionTemperate
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 9500000

noncomputable section

namespace Burnett.C02

open Set Filter
open Burnett.P01 (gaugeProjectionInfrared gaugeProjectionInfrared_contDiff
  gaugeProjectionInfrared_one gaugeProjectionInfrared_zero)
open scoped ContDiff Topology

variable {X P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Smoothly extend the local normalized multiplier with equality on the
whole compact set of active coefficients. The extension is multiplication
by one compact cutoff, and so retains all its local zeros. -/
theorem exists_wardCompactProfile_extension [FiniteDimensional ℝ X]
    {U K : Set X} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : X → ℂ) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : X → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x ∈ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => (χ x : ℂ) * f x) ∧
      HasCompactSupport (fun x => (χ x : ℂ) * f x) := by
  rcases eq_empty_or_nonempty K with rfl | hNonempty
  · refine ⟨fun _ => 0,contDiff_const,?_,?_,by simp,?_,?_⟩
    · simp [HasCompactSupport,tsupport]
    · simp [tsupport]
    · simp only [Complex.ofReal_zero,zero_mul,contDiff_const]
    · simp [HasCompactSupport,tsupport]
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨g,hgSupp,hg,hgRange⟩ :=
    (isOpen_interior : IsOpen (interior L)).exists_smooth_support_eq
  have hgPos (x : X) (hx : x ∈ K) : 0 < g x := by
    have hn : g x ≠ 0 := Function.mem_support.mp (hgSupp.symm ▸ hKL hx)
    exact lt_of_le_of_ne (hgRange (mem_range_self x)).1 (Ne.symm hn)
  obtain ⟨m,hm,hMin⟩ := hK.exists_isMinOn hNonempty hg.continuous.continuousOn
  have hPos := hgPos m hm
  let χ (x : X) := gaugeProjectionInfrared ((2/g m) * g x)
  have hχ : ContDiff ℝ ∞ χ := gaugeProjectionInfrared_contDiff.comp (contDiff_const.mul hg)
  have hχL : tsupport χ ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hxL
    have hZero : g x = 0 := by
      by_contra hn
      exact hxL (interior_subset (hgSupp ▸ Function.mem_support.mpr hn))
    exact hx (by simp only [χ,hZero,mul_zero,gaugeProjectionInfrared_zero zero_le_one])
  have hχSupp := hχL.trans hLU
  have hχOne (x : X) (hx : x ∈ K) : χ x = 1 := by
    apply gaugeProjectionInfrared_one
    have hle : g m ≤ g x := hMin hx
    calc
      2 = (2/g m) * g m := (div_mul_cancel₀ _ hPos.ne').symm
      _ ≤ (2/g m) * g x := mul_le_mul_of_nonneg_left hle (by positivity)
  let F (x : X) := (χ x : ℂ) * f x
  have hχCompact : HasCompactSupport χ := hL.of_isClosed_subset isClosed_closure hχL
  have hFCompact : HasCompactSupport F := by
    apply hχCompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    apply Function.mem_support.mpr
    intro hZero
    exact hx (by simp [F,hZero])
  refine ⟨χ,hχ,hχCompact,hχSupp,hχOne,?_ ,hFCompact⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hOut : x ∉ tsupport χ := fun he => hx (hχSupp he)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hOut] with y hy
    change χ y = 0 at hy
    simp only [hy,Complex.ofReal_zero,zero_mul]

private theorem ward_slice_iteratedFDeriv_le {f : P × X → ℂ} (hf : ContDiff ℝ ∞ f)
    (p : P) (x : X) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y : X => f (p,y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (p,x)‖ := by
  let L : X →L[ℝ] P × X := ContinuousLinearMap.inr ℝ P X
  let z : P × X := (p,0)
  let shift : P × X → P × X := fun y => z+y
  have hZ (y : X) : shift (L y) = (p,y) := by simp [shift,z,L,ContinuousLinearMap.inr_apply]
  have hShift : ContDiff ℝ ∞ (f ∘ shift) := hf.comp (contDiff_const.add contDiff_id)
  have e := L.iteratedFDeriv_comp_right hShift x (i := n) (WithTop.coe_le_coe.mpr le_top)
  have hF : (f ∘ shift) ∘ L = fun y : X => f (p,y) := funext fun y => congrArg f (hZ y)
  have hDeriv : iteratedFDeriv ℝ n (f ∘ shift) (L x) = iteratedFDeriv ℝ n f (p,x) := by
    change iteratedFDeriv ℝ n (fun y => f (z+y)) (L x) = _
    rw [iteratedFDeriv_comp_add_left]
    exact congrArg (iteratedFDeriv ℝ n f) (hZ x)
  rw [hF,hDeriv] at e
  rw [e]
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun y => by
    change ‖((0 : P),y)‖ ≤ 1*‖y‖
    simp [Prod.norm_def])
  have hProduct : (∏ _ : Fin n, ‖L‖) ≤ 1 := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) hL n
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hProduct)

/-- Uniform frequency derivative budget on a compact parameter and input
set for one jointly smooth complex profile, including zero order. -/
theorem exists_wardCompactProfile_sliceJets (f : P × X → ℂ) (hf : ContDiff ℝ ∞ f)
    {K : Set (P × X)} (hK : IsCompact K) (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n ≤ N, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ n (fun y : X => f (z.1,y)) z.2‖ ≤ A := by
  have one (n : Fin (N+1)) : ∃ A : ℝ, 0 < A ∧ ∀ z ∈ K,
      ‖iteratedFDeriv ℝ (n : ℕ) (fun y : X => f (z.1,y)) z.2‖ ≤ A := by
    have hc : Continuous (iteratedFDeriv ℝ (n : ℕ) f) :=
      hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨A,hA,hB⟩ := (hK.image hc).isBounded.exists_pos_norm_le
    exact ⟨A,hA,fun z hz => (ward_slice_iteratedFDeriv_le hf z.1 z.2 n).trans (hB _ ⟨z,hz,rfl⟩)⟩
  choose A hA hJet using one
  refine ⟨∑ n, A n,Finset.sum_nonneg (fun n _ => (hA n).le),?_⟩
  intro n hn z hz
  let i : Fin (N+1) := ⟨n,Nat.lt_succ_of_le hn⟩
  exact (hJet i z hz).trans
    (Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ i))

end Burnett.C02
