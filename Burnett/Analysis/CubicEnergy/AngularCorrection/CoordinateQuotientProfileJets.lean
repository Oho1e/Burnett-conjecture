import Burnett.Analysis.CubicEnergy.AngularCorrection.CoordinateJetDilation
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianQuantitative

set_option autoImplicit false
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.A07

open Set Metric Filter
open Burnett.A02.FrequencySplit (E Joint Freq8 splitFreq)
open Burnett.A06
open scoped ContDiff Topology BigOperators ComplexConjugate

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  change ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

private theorem exists_fixedCoordinateFactor_sphereJets
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (s : ℝ)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ x ≤ r, η x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 4) (n : ℕ), n ≤ 15 →
      ∀ x ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ n (scaledCoordinateFactor η s j) x‖ ≤ C := by
  classical
  have existsBound (i : Fin 4 × Fin 16) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ (i.2 : ℕ) (scaledCoordinateFactor η s i.1) x‖ ≤ C := by
    have hsmooth := scaledCoordinateFactor_contDiff η hη s i.1 hr hzero
    have hcont := (hsmooth.continuous_iteratedFDeriv (nat_le_smooth i.2)).norm
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Freq8) 1).bddAbove_image hcont.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx =>
      (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose C C0 hC using existsBound
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => C0 i), ?_⟩
  intro j n hn x hx
  let i : Fin 4 × Fin 16 := (j, ⟨n, Nat.lt_succ_of_le hn⟩)
  exact (hC i x hx).trans (Finset.single_le_sum (fun k _ => C0 k) (Finset.mem_univ i))

private theorem exists_pulledBackRegularizedSymbol_sphereJets
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    (L : Freq8 →L[ℝ] Joint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ ∞ c V →
      (∀ n ≤ 15, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n c z‖ ≤ B) →
      ∀ (part : ℂ →L[ℝ] ℝ), ‖part‖ ≤ 1 → ∀ (n : ℕ), n ≤ 15 →
      ∀ x ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ n (fun u => part (regularizedLowCartesianSymbol η χ c (L u))) x‖ ≤ C*B := by
  classical
  have input (i : Fin 16) :=
    exists_regularizedLowCartesianSymbol_quantitative_orderOne_bound i.val η χ hr hρ hR
      (hη.of_le (nat_le_smooth i.val)) hzero hone (hχ.of_le (nat_le_smooth i.val)) hcut
  choose C C0 hC using input
  let contribution (i : Fin 16) : ℝ := C i * (1+2*‖L‖) * ‖L‖ ^ i.val
  have contribution0 (i : Fin 16) : 0 ≤ contribution i := by
    dsimp [contribution]
    exact mul_nonneg (mul_nonneg (C0 i) (by positivity)) (by positivity)
  refine ⟨∑ i, contribution i, Finset.sum_nonneg (fun i _ => contribution0 i), ?_⟩
  intro V hV hContains c B B0 hc hjet part hpart n hn x hx
  let i : Fin 16 := ⟨n, Nat.lt_succ_of_le hn⟩
  let f := regularizedLowCartesianSymbol η χ c
  have hf : ContDiff ℝ ∞ f :=
    regularizedLowCartesianSymbol_contDiff η χ c hr hρ hη hzero hχ hcut hV hContains hc
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hL : ‖L x‖ ≤ ‖L‖ := by simpa only [hx1, mul_one] using L.le_opNorm x
  have h1 : ‖(L x).1‖ ≤ ‖L‖ :=
    (show ‖(L x).1‖ ≤ ‖L x‖ from le_max_left _ _).trans hL
  have h2 : ‖(L x).2‖ ≤ ‖L‖ :=
    (show ‖(L x).2‖ ≤ ‖L x‖ from le_max_right _ _).trans hL
  have hw : 1 ≤ 1 + ‖(L x).1‖ + ‖(L x).2‖ := by
    linarith [norm_nonneg (L x).1, norm_nonneg (L x).2]
  have hmax : 1 + ‖(L x).1‖ + ‖(L x).2‖ ≤ 1 + 2*‖L‖ := by linarith
  have hjet' (j : ℕ) (hj : j ≤ i.val) (z : Joint)
      (hz : z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ j c z‖ ≤ B := hjet j (hj.trans hn) z hz
  have hraw :
      ‖iteratedFDeriv ℝ n f (L x)‖ * (1 + ‖(L x).1‖ + ‖(L x).2‖)^n ≤
        C i * B * (1 + ‖(L x).1‖ + ‖(L x).2‖) :=
    hC i hV hContains c B B0 (hc.of_le (nat_le_smooth n)) hjet' (L x)
  have hin : ‖iteratedFDeriv ℝ n f (L x)‖ ≤ C i * B * (1+2*‖L‖) := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * (1 + ‖(L x).1‖ + ‖(L x).2‖)^n :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hw)
      _ ≤ _ := hraw
      _ ≤ _ := mul_le_mul_of_nonneg_left hmax (mul_nonneg (C0 i) B0)
  have hcomp : ContDiff ℝ ∞ (f ∘ L) := hf.comp L.contDiff
  change ‖iteratedFDeriv ℝ n (part ∘ (f ∘ L)) x‖ ≤ _
  rw [part.iteratedFDeriv_comp_left hcomp.contDiffAt (nat_le_smooth n),
    L.iteratedFDeriv_comp_right hf x (nat_le_smooth n)]
  let G := (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap fun _ => L
  have hGn : ‖G‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖^n := by
    simpa only [G, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  calc
    _ ≤ ‖part‖ * ‖G‖ := part.norm_compContinuousMultilinearMap_le G
    _ ≤ ‖G‖ := by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hpart (norm_nonneg G))
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖^n := hGn
    _ ≤ (C i * B * (1+2*‖L‖)) * ‖L‖^n :=
      mul_le_mul_of_nonneg_right hin (by positivity)
    _ = contribution i * B := by dsimp [contribution, i]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => contribution0 k) (Finset.mem_univ i)) B0

private theorem exists_fixedProduct_sphereJets
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    (L : Freq8 →L[ℝ] Joint) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ ∞ c V →
      (∀ n ≤ 15, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n c z‖ ≤ B) →
      ∀ (part : ℂ →L[ℝ] ℝ), ‖part‖ ≤ 1 → ∀ j : Fin 4, ∀ (n : ℕ), n ≤ 15 →
      ∀ x ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ n (fun u => scaledCoordinateFactor η s j u *
          part (regularizedLowCartesianSymbol η χ c (L u))) x‖ ≤ C*B := by
  classical
  obtain ⟨A, A0, hA⟩ := exists_fixedCoordinateFactor_sphereJets η hη s hr hzero
  obtain ⟨D, D0, hD⟩ :=
    exists_pulledBackRegularizedSymbol_sphereJets η χ hr hρ hR hη hzero hone hχ hcut L
  let binomialSum (i : Fin 16) : ℝ := ∑ k ∈ Finset.range (i.val+1), (i.val.choose k : ℝ)
  let S := ∑ i, binomialSum i
  have binomialSum0 (i : Fin 16) : 0 ≤ binomialSum i :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have S0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => binomialSum0 i)
  refine ⟨S*A*D, mul_nonneg (mul_nonneg S0 A0) D0, ?_⟩
  intro V hV hContains c B B0 hc hjet part hpart j n hn x hx
  let k : Fin 16 := ⟨n, Nat.lt_succ_of_le hn⟩
  let a := scaledCoordinateFactor η s j
  let g := fun u => part (regularizedLowCartesianSymbol η χ c (L u))
  have ha : ContDiff ℝ ∞ a := scaledCoordinateFactor_contDiff η hη s j hr hzero
  have hg : ContDiff ℝ ∞ g :=
    part.contDiff.comp ((regularizedLowCartesianSymbol_contDiff η χ c hr hρ hη hzero hχ
      hcut hV hContains hc).comp L.contDiff)
  change ‖iteratedFDeriv ℝ n (fun u => a u * g u) x‖ ≤ _
  refine (norm_iteratedFDeriv_mul_le ha hg x (nat_le_smooth n)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * A * (D*B) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      refine mul_le_mul ?_ (hD hV hContains c B B0 hc hjet part hpart (n-i)
        ((Nat.sub_le _ _).trans hn) x hx) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (hA j i (hi'.trans hn) x hx) (by positivity)
    _ = binomialSum k * (A*(D*B)) := by
      dsimp [binomialSum, k]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ S * (A*(D*B)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (fun i _ => binomialSum0 i) (Finset.mem_univ k)
    _ = _ := by ring

/-- The common joint-sphere Cartesian jet budget of the actual forward and
adjoint coordinate quotients, linear in the paper's normalized coefficient
jet budget. Both real and imaginary projections have op norm one. -/
theorem exists_coordinateQuotient_profile_sphereJet_bound
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ ∞ c V →
      (∀ n ≤ 15, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n c z‖ ≤ B) →
      ∀ (part : ℂ →L[ℝ] ℝ), ‖part‖ ≤ 1 → ∀ j : Fin 4, ∀ (n : ℕ), n ≤ 15 →
      ∀ x ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ n (fun u => part
          (coordinateQuotient (lowCartesianSymbol χ c) j (splitFreq u))) x‖ ≤ C*B ∧
        ‖iteratedFDeriv ℝ n (fun u => part
          (coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j (splitFreq u))) x‖ ≤ C*B := by
  let s := coordinateJetDilation ρ R
  let F := scaledJointFrequency s
  let A := scaledHighAdjointFrequency s
  obtain ⟨C, C0, hC⟩ :=
    exists_fixedProduct_sphereJets η χ hr hρ hR hη hzero hone hχ hcut F s
  obtain ⟨D, D0, hD⟩ :=
    exists_fixedProduct_sphereJets η χ hr hρ hR hη hzero hone hχ hcut A s
  refine ⟨max C D, C0.trans (le_max_left _ _), ?_⟩
  intro V hV hContains c B B0 hc hjet part hpart j n hn x hx
  let adjPart := part.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have conj_bound : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖conj z‖ ≤ 1 * ‖z‖
    rw [Complex.norm_conj, one_mul]
  have adjPart_bound : ‖adjPart‖ ≤ 1 := by
    refine (part.opNorm_comp_le _).trans ?_
    simpa only [one_mul] using mul_le_mul hpart conj_bound (norm_nonneg _) zero_le_one
  have hhigh : (1/2 : ℝ) < ‖x‖ := by
    rw [mem_sphere_zero_iff_norm.mp hx]
    norm_num
  have near := (isOpen_lt continuous_const continuous_norm).mem_nhds hhigh
  have hF : (fun u => part (coordinateQuotient (lowCartesianSymbol χ c) j (splitFreq u))) =ᶠ[𝓝 x]
      fun u => scaledCoordinateFactor η s j u * part (regularizedLowCartesianSymbol η χ c (F u)) := by
    filter_upwards [near] with u hu
    have eq := (coordinateQuotients_eq_scaledRegularized η χ c hρ hsmall
      (zero_lt_one.trans_le hR) hone hcut j u hu).1
    change part (coordinateQuotient (lowCartesianSymbol χ c) j (splitFreq u)) = _
    rw [eq, map_smul, smul_eq_mul]
  have hA : (fun u => part
      (coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j (splitFreq u))) =ᶠ[𝓝 x]
      fun u => scaledCoordinateFactor η s j u *
        adjPart (regularizedLowCartesianSymbol η χ c (A u)) := by
    filter_upwards [near] with u hu
    have eq := (coordinateQuotients_eq_scaledRegularized η χ c hρ hsmall
      (zero_lt_one.trans_le hR) hone hcut j u hu).2
    change part (coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j
      (splitFreq u)) = _
    rw [eq, map_smul, smul_eq_mul]
    rfl
  constructor
  · rw [(hF.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hC hV hContains c B B0 hc hjet part hpart j n hn x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) B0)
  · rw [(hA.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hD hV hContains c B B0 hc hjet adjPart adjPart_bound j n hn x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) B0)

end Burnett.A07
