import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestComparisonConsumer
import Burnett.Analysis.PrincipalEnergy.Freezing.FrozenInfraredComparison
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactPrincipalLeftCommutator
import Burnett.Analysis.PrincipalEnergy.Freezing.AffineCutoffComparisonBudgets

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff

private theorem compact_base_order_one_a_frequency_smooth (a : E → E → ℝ)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0}) (c : E) :
    ContDiffOn ℝ ∞ (a c) {ξ | ξ ≠ 0} :=
  Complex.reCLM.contDiff.fun_comp_contDiffOn (ha.frequencySmooth c)

private theorem compact_base_order_one_frozen_jets (a : E → E → ℝ)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (M : ℝ) (hM : CompactBaseOrderOneBudget a M) (c : E)
    (n : ℕ) (hn : n ≤ 7) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
    ‖iteratedFDeriv ℝ n (a c) ξ‖ ≤ M := by
  have hU : IsOpen {ξ : E | ξ ≠ 0} := isClosed_singleton.isOpen_compl
  have nz : ξ ≠ 0 := by
    have h : ‖ξ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hξ
    exact norm_ne_zero_iff.mp (h.trans_ne one_ne_zero)
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((compact_base_order_one_a_frequency_smooth a ha c).contDiffAt (hU.mem_nhds nz))
    (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  exact h.symm.trans_le (hM n hn ξ hξ c).1

/-- The original sandwiched quantization and the literal left principal
patch differ by a real order-zero operator, with a single finite bound
at each scale. The input correction is the difference between the
original full test and the compact-base homogeneous left test. -/
theorem exists_affine_original_test_comparison_W13 (P Rb : ℝ) (hP : 0 < P) (hRP : Rb < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) Rb, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) Rb → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (B : SchwartzMap E ℂ → E → ℂ) (R : SchwartzMap E ℂ → E → ℂ)
    (original : ∀ u, B u = radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u + R u)
    (A D : ℝ≥0∞) (Afin : A < ⊤) (Dfin : D < ⊤) (correction : SchwartzOrderZeroJetBound R A D)
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (Θ : SchwartzMap E ℂ) (θ : E → SchwartzMap E ℂ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (θshape : ∀ c x, θ c x = Θ (ℓ⁻¹ • (x-c))) :
    let B₀ (c : E) := radianAction (fixedInfraredSymbol cut add (a c))
    ∃ Bℓ : ℝ≥0∞, Bℓ < ⊤ ∧ ∀ c : E,
      SchwartzOrderZeroJetBound (fun u => (-Complex.I) •
        (sandwichedScalarTest (θ c) (fun v => B v - B₀ c v) u -
          radianLeftQuantization (localizedFrozenPrincipalSymbol a c (θ c)) u)) Bℓ Bℓ := by
  intro B₀
  let Pθ := ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0) Θ)
  let Tθ := ENNReal.ofReal (ℓ⁻¹ * ∑ j : Index, (SchwartzMap.seminorm ℝ 0 0) (energyPartial j Θ))
  let F₁ := (ℓ ^ 1)⁻¹ * patchFourierMoment 1 Θ
  let F₂ := (ℓ ^ 2)⁻¹ * patchFourierMoment 2 Θ
  have nonneg (n : ℕ) : 0 ≤ (ℓ ^ n)⁻¹ * patchFourierMoment n Θ :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le _)) (patch_moment_nonneg _ _)
  obtain ⟨Pfin,Tfin,θB⟩ := affine_test_cutoff_uniform_budgets Θ θ ℓ hℓ θshape
  obtain ⟨C,F,Cfin,Ffin,com⟩ := exists_localized_frozen_left_commutator_W13 P Rb hP hRP ρ hρ hS
    ρone a support ha hom M M0 hM F₁ F₂ (nonneg 1) (nonneg 2) Pθ Tθ Pfin Tfin
  obtain ⟨A₀,A₀fin,ir⟩ := exists_frozen_fixed_infrared_difference_W13 cut add hcut hadd M M0
  let R₀ (c : E) (u : SchwartzMap E ℂ) := B₀ c u - radianAction (a c) u
  have B₀eq (c : E) (_ : c ∈ (univ : Set E)) (u : SchwartzMap E ℂ) :
      B₀ c u = radianAction (a c) u + R₀ c u := by
    simp [R₀, add_comm (radianAction (a c) u), sub_add_cancel]
  have R₀B (c : E) (_ : c ∈ (univ : Set E)) : SchwartzOrderZeroJetBound (R₀ c) A₀ 0 :=
    ir (a c) (compact_base_order_one_a_frequency_smooth a ha c) (fun t ht => hom t ht c)
      (fun n hn => compact_base_order_one_frozen_jets a ha M hM c n (hn.trans (by decide)))
  have commutator (c : E) (_ : c ∈ (univ : Set E)) : SchwartzOrderZeroJetBound (localizedFrozenLeftCommutator a c (θ c)) C F :=
    com c (θ c) (le_of_eq ((θB c).2.2 1)) (le_of_eq ((θB c).2.2 2)) (θB c).1 (θB c).2.1
  have h := sandwiched_original_test_comparison_W13 a (compact_base_order_one_a_frequency_smooth a ha) hom
    univ θ B B₀ R R₀ original B₀eq A D A₀ 0 C F Pθ Tθ
    (fun c _ => (θB c).1) (fun c _ => (θB c).2.1) correction R₀B commutator
  let U := Pθ^2*(A+A₀)+C
  let V := 2*Pθ*Tθ*(A+A₀)+Pθ^2*(D+0)+F
  have sums : A + A₀ < ⊤ := ENNReal.add_lt_top.mpr ⟨Afin,A₀fin⟩
  have p2 : Pθ^2 < ⊤ := ENNReal.pow_lt_top Pfin
  have Uf : U < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top p2 sums,Cfin⟩
  have Vf : V < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) Pfin) Tfin) sums,
      ENNReal.mul_lt_top p2 (by simpa only [add_zero] using Dfin)⟩,Ffin⟩
  refine ⟨max U V, max_lt Uf Vf, ?_⟩
  intro c
  exact schwartz_order_zero_jet_bound_mono _ U V _ _ (h c (mem_univ c)) (le_max_left _ _) (le_max_right _ _)

end Burnett.A03
