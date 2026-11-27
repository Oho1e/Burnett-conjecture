import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalOrderZeroLeft
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalSymbolMixedJets
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylFullTestConsumer
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactComplexOrderZeroLeft

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set
open Burnett.A02.FrequencySplit
open scoped ContDiff Topology

section

open Finset
open scoped ENNReal BigOperators

private def projectedMixedMap (L : ℂ →L[ℝ] ℂ) (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => E) ℂ ℂ L

private theorem projected_mixed_map_norm_le (L : ℂ →L[ℝ] ℂ) (n : ℕ) :
    ‖projectedMixedMap L n‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun M => L.norm_compContinuousMultilinearMap_le M)

private theorem frequency_jet_of_projected_symbol (r : E → E → ℂ)
    (h : RadianOrderZeroSymbolSeminorms r) (L : ℂ →L[ℝ] ℂ) (n : ℕ) (x ξ : E) :
    iteratedFDeriv ℝ n (fun ζ => L (r x ζ)) ξ = projectedMixedMap L n (iteratedFDeriv ℝ n (r x) ξ) :=
  L.iteratedFDeriv_comp_left ((contDiffOn_univ.mp (h.jets.frequencySmooth x)).contDiffAt)
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

/-- A fixed real-linear projection acts on both mixed jets of the actual
order-zero symbol, with a constant controlled by its operator norm. -/
theorem radian_order_zero_symbol_map (r : E → E → ℂ) (h : RadianOrderZeroSymbolSeminorms r)
    (L : ℂ →L[ℝ] ℂ) :
    RadianOrderZeroSymbolSeminorms (fun x ξ => L (r x ξ)) := by
  have eq (n : ℕ) (ξ : E) :
      (fun x => iteratedFDeriv ℝ n (fun ζ => L (r x ζ)) ξ) =
        projectedMixedMap L n ∘ fun x => iteratedFDeriv ℝ n (r x) ξ :=
    funext fun x => frequency_jet_of_projected_symbol r h L n x ξ
  have J (n : ℕ) : (fun p : E × E => iteratedFDeriv ℝ n (fun ζ => L (r p.1 ζ)) p.2) =
      projectedMixedMap L n ∘ fun p => iteratedFDeriv ℝ n (r p.1) p.2 :=
    funext fun p => frequency_jet_of_projected_symbol r h L n p.1 p.2
  refine ⟨⟨fun x => L.contDiff.comp_contDiffOn (h.jets.frequencySmooth x),?_ ,?_⟩,?_⟩
  · intro n ξ hξ
    rw [eq]
    exact (projectedMixedMap L n).contDiff.comp (h.jets.baseJetSmooth n ξ hξ)
  · intro n
    rw [J]
    exact (projectedMixedMap L n).continuous.comp_continuousOn (h.jets.jointJetContinuous n)
  · intro n m
    obtain ⟨A,A0,hA⟩ := h.estimate n m
    let P := projectedMixedMap L n
    refine ⟨‖L‖ * A,mul_nonneg (norm_nonneg _) A0,?_⟩
    intro x ξ
    have q : iteratedFDeriv ℝ m
        (fun y => iteratedFDeriv ℝ n (fun ζ => L (r y ζ)) ξ) x =
        P.compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) ξ) x) := by
      rw [eq]
      exact P.iteratedFDeriv_comp_left ((h.jets.baseJetSmooth n ξ (mem_univ ξ)).contDiffAt)
        (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
    rw [q]
    calc
      _ ≤ (1+‖ξ‖)^n * (‖P‖ * ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) ξ) x‖) :=
        mul_le_mul_of_nonneg_left (P.norm_compContinuousMultilinearMap_le _) (by positivity)
      _ = ‖P‖ * ((1+‖ξ‖)^n * ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) ξ) x‖) := by ring
      _ ≤ ‖L‖ * A := mul_le_mul (projected_mixed_map_norm_le L n) (hA x ξ) (by positivity) (norm_nonneg _)

/-- The finite Mikhlin bounds used by the verified compact-base action
follow from ordinary mixed order-zero estimates. -/
theorem exists_compact_base_order_zero_budget_from_symbol_semis (r : E → E → ℝ)
    (h : RadianOrderZeroSymbolSeminorms (fun x ξ => (r x ξ : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ CompactBaseOrderZeroBudget r C := by
  choose A A0 hA using h.estimate
  let M := ∑ j ∈ Finset.range 9, (A j 0 + A j 8)
  have sm : ∀ j, 0 ≤ A j 0 + A j 8 := fun j => add_nonneg (A0 j 0) (A0 j 8)
  refine ⟨M,sum_nonneg fun j _ => sm j,?_⟩
  intro n hn ξ _ x
  have t : n ∈ Finset.range 9 := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  have b : A n 0 + A n 8 ≤ M := Finset.single_le_sum (f := fun j => A j 0 + A j 8) (fun j _ => sm j) t
  have w : ‖ξ‖^n ≤ (1+‖ξ‖)^n :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  constructor
  · have g := hA n 0 x ξ
    rw [norm_iteratedFDeriv_zero] at g
    exact ((mul_le_mul_of_nonneg_right w (norm_nonneg _)).trans g).trans
      ((le_add_of_nonneg_right (A0 n 8)).trans b)
  · exact ((mul_le_mul_of_nonneg_right w (norm_nonneg _)).trans (hA n 8 x ξ)).trans
      ((le_add_of_nonneg_left (A0 n 0)).trans b)

/-- An arbitrary complex order-zero symbol with bounded base support
gives the actual left action and its finite W¹,³ estimate. -/
theorem exists_radian_classical_order_zero_left_W13
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (r : E → E → ℂ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → r x ξ = 0)
    (h : RadianOrderZeroSymbolSeminorms r) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound (radianLeftQuantization r) C C := by
  let A (x ξ : E) := (r x ξ).re
  let B (x ξ : E) := (r x ξ).im
  have aS : RadianOrderZeroSymbolSeminorms (fun x ξ => (A x ξ : ℂ)) :=
    radian_order_zero_symbol_map r h (Complex.ofRealCLM.comp Complex.reCLM)
  have bS : RadianOrderZeroSymbolSeminorms (fun x ξ => (B x ξ : ℂ)) :=
    radian_order_zero_symbol_map r h (Complex.ofRealCLM.comp Complex.imCLM)
  obtain ⟨D,D0,hD⟩ := exists_compact_base_order_zero_budget_from_symbol_semis A aS
  obtain ⟨F,F0,hF⟩ := exists_compact_base_order_zero_budget_from_symbol_semis B bS
  have aSupport (x ξ : E) (outside : x ∉ closedBall (0 : E) R) : A x ξ = 0 := by
    simp [A,support x ξ outside]
  have bSupport (x ξ : E) (outside : x ∉ closedBall (0 : E) R) : B x ξ = 0 := by
    simp [B,support x ξ outside]
  have re : r = (fun x ξ => (A x ξ : ℂ) + Complex.I * (B x ξ : ℂ)) := by
    funext x ξ
    rw [mul_comm]
    exact (Complex.re_add_im (r x ξ)).symm
  rw [re]
  exact exists_compact_base_complex_order_zero_left_W13 P R hP hRP ρ hρ hS ρone
    A B aSupport bSupport aS.jets bS.jets D F D0 F0 hD hF

end

abbrev radianPuncturedSymbolDomain : Set (E × E) := (univ : Set E) ×ˢ ({0} : Set E)ᶜ

/-- The ordinary order-zero mixed estimates in the unbounded frequency
region. There is no assumption on the symbol or its derivatives inside it. -/
def RadianOrderZeroSymbolTail (T : ℝ) (r : E → E → ℂ) : Prop :=
  ∀ n m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, T < ‖ξ‖ →
    (1+‖ξ‖)^n * ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) ξ) x‖ ≤ C

private theorem mixed_jet_zero_off_compact_base (r : E → E → ℂ) (R : ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → r x ξ = 0)
    (n m : ℕ) (x ξ : E) (out : x ∉ closedBall (0 : E) R) :
    iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) ξ) x = 0 := by
  have h : (fun y => iteratedFDeriv ℝ n (r y) ξ) =ᶠ[𝓝 x] (fun _ : E => 0) := by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds out] with y hy
    have eq : r y = (fun _ : E => (0 : ℂ)) := funext fun ζ => support y ζ hy
    simp only [eq,iteratedFDeriv_zero_fun,Pi.zero_apply]
  calc
    _ = iteratedFDeriv ℝ m (fun _ : E => (0 :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ)) x :=
      (h.iteratedFDeriv ℝ m).self_of_nhds
    _ = 0 := by simp only [iteratedFDeriv_zero_fun,Pi.zero_apply]

/-- The missing bounded frequency region has automatic finite mixed
seminorms for an actual smooth symbol with compact base support. -/
theorem radian_order_zero_symbol_of_compact_base_tail
    (r : E → E → ℂ) (R T : ℝ)
    (smooth : ContDiff ℝ ∞ (Function.uncurry r))
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → r x ξ = 0)
    (tail : RadianOrderZeroSymbolTail T r) : RadianOrderZeroSymbolSeminorms r := by
  refine ⟨compact_base_frequency_jets_of_joint_smooth r smooth,?_⟩
  intro n m
  let g (p : E × E) := (1+‖p.2‖)^n *
    ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) p.2) p.1‖
  have gc : Continuous g := ((continuous_const.add continuous_snd.norm).pow n).mul
    (smooth_mixed_symbol_jet r smooth n m).continuous.norm
  obtain ⟨A,hA⟩ := ((isCompact_closedBall (0 : E) R).prod
    (isCompact_closedBall (0 : E) T)).bddAbove_image gc.continuousOn
  obtain ⟨B,B0,hB⟩ := tail n m
  refine ⟨max A B,B0.trans (le_max_right _ _),?_⟩
  intro x ξ
  by_cases h : T < ‖ξ‖
  · exact (hB x ξ h).trans (le_max_right _ _)
  · by_cases xin : x ∈ closedBall (0 : E) R
    · have ξin : ξ ∈ closedBall (0 : E) T := by
        simpa only [mem_closedBall,dist_zero_right] using le_of_not_gt h
      exact (hA ⟨(x,ξ),⟨xin,ξin⟩,rfl⟩).trans (le_max_left _ _)
    · rw [mixed_jet_zero_off_compact_base r R support n m x ξ xin,norm_zero,mul_zero]
      exact B0.trans (le_max_right _ _)

/-- The fixed infrared profile smooths the principal symbol jointly in
both variables. The only puncture is the one removed by the profile. -/
theorem compact_principal_fixed_infrared_joint_smooth
    (cut : SchwartzMap E ℂ) (a : E → E → ℝ)
    (smooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1) :
    ContDiff ℝ ∞ (fun p : E × E => (fixedInfraredSymbol cut 0 (a p.1) p.2 : ℂ)) := by
  have c : ContDiff ℝ ∞ (fixedRadianProfile cut) :=
    Complex.reCLM.contDiff.comp ((cut.smooth _).comp (contDiff_const.smul contDiff_id))
  have A : ContDiff ℝ ∞ (fun p : E × E => ((1-fixedRadianProfile cut p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (c.comp contDiff_snd))
  have off : IsOpen radianPuncturedSymbolDomain := isOpen_univ.prod isClosed_singleton.isOpen_compl
  have zeroProfile (ξ : E) : fixedRadianProfile (0 : SchwartzMap E ℂ) ξ = 0 := by
    simp [fixedRadianProfile]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases zero : p.2 = 0
  · have tp : Tendsto (Prod.snd : E × E → E) (𝓝 p) (𝓝 (0 : E)) := by
      have atPoint : ContinuousAt (Prod.snd : E × E → E) p := continuous_snd.continuousAt
      rw [← zero]
      exact atPoint.tendsto
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [tp.eventually plateau] with q hq
    simp only [fixedInfraredSymbol,hq,sub_self,zero_mul,zeroProfile,add_zero,Complex.ofReal_zero]
  · have pin : p ∈ radianPuncturedSymbolDomain := ⟨mem_univ _,zero⟩
    have good := A.contDiffAt.mul (smooth.contDiffAt (off.mem_nhds pin))
    simpa only [fixedInfraredSymbol,zeroProfile,add_zero,Complex.ofReal_mul] using good

/-- The actual full left symbol minus its fixed-infrared homogeneous
principal part has order zero at every frequency. The input at high
frequency is the first remainder of the classical symbol expansion. -/
theorem classical_full_left_symbol_remainder_order_zero
    (b : E → E → ℂ) (a : E → E → ℝ) (R T : ℝ)
    (bs : ContDiff ℝ ∞ (Function.uncurry b))
    (asmooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain)
    (bsupp : ∀ x ξ, x ∉ closedBall (0 : E) R → b x ξ = 0)
    (asupp : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (atInfinity : RadianOrderZeroSymbolTail T (fun x ξ => b x ξ - (a x ξ : ℂ)))
    (cut : SchwartzMap E ℂ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (outside : ∀ ξ, T < ‖ξ‖ → fixedRadianProfile cut ξ = 0) :
    RadianOrderZeroSymbolSeminorms (fun x ξ => b x ξ - (fixedInfraredSymbol cut 0 (a x) ξ : ℂ)) := by
  let r (x ξ : E) := b x ξ - (fixedInfraredSymbol cut 0 (a x) ξ : ℂ)
  let s (x ξ : E) := b x ξ - (a x ξ : ℂ)
  have rs : ContDiff ℝ ∞ (Function.uncurry r) := bs.sub
    (compact_principal_fixed_infrared_joint_smooth cut a asmooth plateau)
  have rSupport (x ξ : E) (h : x ∉ closedBall (0 : E) R) : r x ξ = 0 := by
    simp [r,bsupp x ξ h,asupp x ξ h,fixedInfraredSymbol,fixedRadianProfile]
  apply radian_order_zero_symbol_of_compact_base_tail r R T rs rSupport
  intro n m
  obtain ⟨C,C0,hC⟩ := atInfinity n m
  refine ⟨C,C0,?_⟩
  intro x ξ high
  have eq (y : E) : r y =ᶠ[𝓝 ξ] s y := by
    have O : IsOpen {q : E | T < ‖q‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [O.mem_nhds high] with ζ hζ
    have z : fixedRadianProfile (0 : SchwartzMap E ℂ) ζ = 0 := by simp [fixedRadianProfile]
    simp only [r,s,fixedInfraredSymbol,outside ζ hζ,sub_zero,one_mul,z,add_zero]
  have jj : (fun y => iteratedFDeriv ℝ n (r y) ξ) = (fun y => iteratedFDeriv ℝ n (s y) ξ) :=
    funext fun y => ((eq y).iteratedFDeriv ℝ n).self_of_nhds
  rw [jj]
  exact hC x ξ high

end Burnett.A03
