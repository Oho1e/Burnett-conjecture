import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileExtension
import Burnett.Analysis.AngularCaps.ActualEnlargedCapJets

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

namespace Burnett.C02

open Set Filter
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Topology

/-- The actual real odd degree-one chart test on the compact receiving
window admits a smooth odd homogeneous extension in the base variable.
The replacement agrees at every frequency on that same window. -/
theorem exists_wardRealOddChartTest_extension (K U : Set E)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ {ξ : E | ξ ≠ 0}))
    (hOdd : ∀ x ∈ K, ∀ ξ, a (x,-ξ) = -a (x,ξ))
    (hHom : ∀ x ∈ K, ∀ t : ℝ, 0 < t → ∀ ξ, a (x,t • ξ) = t * a (x,ξ)) :
    ∃ b : Joint → ℝ, ContDiffOn ℝ ∞ b {p | p.2 ≠ 0} ∧
      (∀ x ξ, b (x,-ξ) = -b (x,ξ)) ∧
      (∀ x (t : ℝ), 0 < t → ∀ ξ, b (x,t • ξ) = t * b (x,ξ)) ∧
      ∀ x ∈ K, ∀ ξ, b (x,ξ) = a (x,ξ) := by
  obtain ⟨χ,hχ,_,hχSupp,hχOne,_,_⟩ := exists_wardCompactProfile_extension hU hK hKU
    (fun _ => (0 : ℂ)) contDiffOn_const
  let u (ξ : E) := ‖ξ‖⁻¹ • ξ
  let b (p : Joint) := χ p.1 * (‖p.2‖ * ((a (p.1,u p.2) - a (p.1,-u p.2))/2))
  have uNZ (ξ : E) (hξ : ξ ≠ 0) : u ξ ≠ 0 :=
    smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hξ)) hξ
  refine ⟨b,?_,?_,?_,?_⟩
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    by_cases hx : p.1 ∈ U
    · have hz : p.2 ≠ 0 := hp
      have hn : ContDiffAt ℝ ∞ (fun y : Joint => ‖y.2‖) p := contDiffAt_snd.norm ℝ hz
      have hu : ContDiffAt ℝ ∞ (fun y : Joint => u y.2) p :=
        (hn.inv (norm_ne_zero_iff.mpr hz)).smul contDiffAt_snd
      have hb : ContDiffAt ℝ ∞ (Prod.fst : Joint → E) p := contDiffAt_fst
      have hMap₀ := hb.prodMk hu
      have hMap₁ := hb.prodMk hu.neg
      have hOpen : IsOpen (U ×ˢ {ξ : E | ξ ≠ 0}) := hU.prod isOpen_ne
      have h₀Mem : (p.1,u p.2) ∈ U ×ˢ {ξ : E | ξ ≠ 0} := ⟨hx,uNZ _ hz⟩
      have h₁Mem : (p.1,-u p.2) ∈ U ×ˢ {ξ : E | ξ ≠ 0} := ⟨hx,neg_ne_zero.mpr (uNZ _ hz)⟩
      have h₀At := ha.contDiffAt (hOpen.mem_nhds h₀Mem)
      have h₁At := ha.contDiffAt (hOpen.mem_nhds h₁Mem)
      have h₀ := h₀At.comp p hMap₀
      have h₁ := h₁At.comp p hMap₁
      exact (hχ.contDiffAt.comp p contDiffAt_fst).mul (hn.mul ((h₀.sub h₁).div_const 2))
    · have ht : p.1 ∉ tsupport χ := fun h => hx (hχSupp h)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have h := (notMem_tsupport_iff_eventuallyEq.mp ht).comp_tendsto continuous_fst.continuousAt
      filter_upwards [h] with y hy
      change χ y.1 = 0 at hy
      simp only [b,hy,zero_mul]
  · intro x ξ
    have h : u (-ξ) = -u ξ := by simp only [u,norm_neg,smul_neg]
    dsimp only [b]
    rw [norm_neg,h,neg_neg]
    ring
  · intro x t ht ξ
    by_cases hξ : ξ = 0
    · simp [hξ,b]
    have hN : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul,Real.norm_of_nonneg ht.le]
    have hU : u (t • ξ) = u ξ := by
      simp only [u,hN,smul_smul]
      congr 1
      field_simp [ht.ne',norm_ne_zero_iff.mpr hξ]
    dsimp only [b]
    rw [hN,hU]
    ring
  · intro x hx ξ
    by_cases hξ : ξ = 0
    · have hZero : a (x,0) = 0 := by
        have h := hOdd x hx 0
        rw [neg_zero] at h
        linarith only [h]
      simp [hξ,b,hZero]
    have hN := norm_pos_iff.mpr hξ
    have hBack : ‖ξ‖ • u ξ = ξ := by
      rw [show u ξ = ‖ξ‖⁻¹ • ξ from rfl,smul_smul,mul_inv_cancel₀ hN.ne',one_smul]
    have h := hHom x hx ‖ξ‖ hN (u ξ)
    rw [hBack] at h
    dsimp only [b]
    rw [hχOne x hx,one_mul,hOdd x hx (u ξ),h]
    ring

end Burnett.C02
