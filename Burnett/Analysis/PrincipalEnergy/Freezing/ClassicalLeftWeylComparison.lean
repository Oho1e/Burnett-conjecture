import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalLeftSymbolRemainder
import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalLeftInfraredGap
import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianLeftQuantizationAlgebra
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderOneModes

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

/-- The mixed symbol bounds imply the ordinary value growth needed in
the same actual left Fourier integrals. -/
theorem radian_left_symbol_growth_of_order_zero (r : E → E → ℂ)
    (h : RadianOrderZeroSymbolSeminorms r) : RadianLeftSymbolGrowth r := by
  intro x
  obtain ⟨D,D0,hD⟩ := h.estimate 0 0
  have m : Measurable (r x) := (contDiffOn_univ.mp (h.jets.frequencySmooth x)).continuous.measurable
  refine ⟨m,D,D0,fun ξ => ?_⟩
  have h := hD x ξ
  simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero] at h
  exact h.trans (le_mul_of_one_le_right D0 (le_add_of_nonneg_right (norm_nonneg _)))

/-- The homogeneous principal value has linear frequency growth
controlled by its normalized sphere seminorm. -/
theorem compact_homogeneous_principal_left_growth
    (a : E → E → ℝ)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M) :
    RadianLeftSymbolGrowth (fun x ξ => (a x ξ : ℂ)) := by
  intro x
  refine ⟨measurable_of_continuousOn_compl_singleton 0 (ha.frequencySmooth x).continuousOn,
    M,M0,fun ξ => ?_⟩
  have goal : ‖a x ξ‖ ≤ M*‖ξ‖ := by
    by_cases nz : ξ = 0
    · subst ξ
      have H := hom 2 (by norm_num) x (0 : E)
      simp only [smul_zero] at H
      have z : a x 0 = 0 := by linarith
      simp [z]
    · let q := ‖ξ‖⁻¹ • ξ
      have np : 0 < ‖ξ‖ := norm_pos_iff.mpr nz
      have sq : q ∈ sphere (0 : E) 1 := by
        rw [mem_sphere,dist_zero_right]
        dsimp only [q]
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr np.le),inv_mul_cancel₀ np.ne']
      have h := (hM 0 (by decide) q sq x).1
      simp only [norm_iteratedFDeriv_zero,Complex.norm_real] at h
      have same : ‖ξ‖ • q = ξ := by
        dsimp only [q]
        rw [smul_smul,mul_inv_cancel₀ np.ne',one_smul]
      rw [← same,hom ‖ξ‖ np x q,norm_mul,Real.norm_of_nonneg np.le]
      simpa only [same,mul_comm] using mul_le_mul_of_nonneg_left h np.le
  rw [Complex.norm_real]
  exact goal.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) M0)

/-- A classical left symbol in a fixed Euclidean chart, retaining just the
first remainder of its expansion. It has arbitrary complex lower terms. -/
structure ClassicalRadianLeftData (b : E → E → ℂ) (a : E → E → ℝ) (R T : ℝ) : Prop where
  fullSmooth : ContDiff ℝ ∞ (Function.uncurry b)
  principalSmooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain
  fullSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → b x ξ = 0
  principalSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0
  firstRemainder : RadianOrderZeroSymbolTail T (fun x ξ => b x ξ - (a x ξ : ℂ))

/-- The standard local left action with its actual compact smoothing
kernel. The target Weyl model is a separately defined operator. -/
def classicalLocalLeftAction (b K : E → E → ℂ) (u : SchwartzMap E ℂ) : E → ℂ :=
  radianLeftQuantization b u + compactKernelAction K u

private theorem left_symbol_growth_add (r s : E → E → ℂ)
    (hr : RadianLeftSymbolGrowth r) (hs : RadianLeftSymbolGrowth s) :
    RadianLeftSymbolGrowth (fun x ξ => r x ξ + s x ξ) := by
  intro x
  obtain ⟨rm,A,A0,ra⟩ := hr x
  obtain ⟨sm,B,B0,sa⟩ := hs x
  refine ⟨rm.add sm,A+B,add_nonneg A0 B0,fun ξ => ?_⟩
  apply (norm_add_le _ _).trans
  rw [add_mul]
  exact add_le_add (ra ξ) (sa ξ)

/-- The actual arbitrary local left symbol and its smoothing kernel
differ from its homogeneous left principal action by a finite W¹,³
operator. The proof includes the fixed infrared correction. -/
theorem exists_classical_local_left_homogeneous_difference_W13
    (P R T : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (b : E → E → ℂ) (a : E → E → ℝ) (data : ClassicalRadianLeftData b a R T)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (outside : ∀ ξ, T < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (K : E → E → ℂ) (RK : ℝ) (Ks : ContDiff ℝ 1 (Function.uncurry K))
    (Ksupport : ∀ x y, x ∉ closedBall (0 : E) RK ∨ y ∉ closedBall (0 : E) RK → K x y = 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound (fun u =>
      classicalLocalLeftAction b K u - radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u) C C := by
  let A (x ξ : E) := (a x ξ : ℂ)
  let v (x ξ : E) := (fixedInfraredSymbol cut 0 (a x) ξ : ℂ)
  let r (x ξ : E) := b x ξ - v x ξ
  let g (x ξ : E) := ((fixedInfraredSymbol cut 0 (a x) ξ - a x ξ : ℝ) : ℂ)
  have rS := classical_full_left_symbol_remainder_order_zero b a R T data.fullSmooth
    data.principalSmooth data.fullSupport data.principalSupport data.firstRemainder cut plateau outside
  have rSupport (x ξ : E) (h : x ∉ closedBall (0 : E) R) : r x ξ = 0 := by
    simp [r,v,data.fullSupport x ξ h,data.principalSupport x ξ h,fixedInfraredSymbol,fixedRadianProfile]
  obtain ⟨C,Cf,Cr⟩ := exists_radian_classical_order_zero_left_W13 P R hP hRP ρ hρ hS ρone r rSupport rS
  obtain ⟨D,Df,Dg⟩ := exists_compact_fixed_infrared_left_principal_gap_W13 P R hP hRP ρ hρ hS ρone
    a data.principalSupport ha hom M M0 hM cut hcut plateau
  obtain ⟨F,Ff,FK⟩ := exists_compact_kernel_order_zero_jet_bound K RK Ks Ksupport
  have aG : RadianLeftSymbolGrowth A := compact_homogeneous_principal_left_growth a ha hom M M0 hM
  have rG : RadianLeftSymbolGrowth r := radian_left_symbol_growth_of_order_zero r rS
  have gEq (x ξ : E) : g x ξ = -((fixedRadianProfile cut ξ : ℝ) : ℂ) * A x ξ := by
    simp only [g,A,fixedInfraredSymbol,fixedRadianProfile,SchwartzMap.zero_apply,Complex.zero_re,add_zero,
      Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
    ring
  have gG : RadianLeftSymbolGrowth g := by
    intro x
    obtain ⟨m,V,V0,VB⟩ := aG x
    let S := SchwartzMap.seminorm ℝ 0 0 cut
    have S0 : 0 ≤ S := apply_nonneg _ _
    have mG : Measurable (g x) := by
      simp only [show g x = (fun ξ => -((fixedRadianProfile cut ξ : ℝ) : ℂ) * A x ξ) from funext (gEq x)]
      exact (Complex.continuous_ofReal.measurable.comp (fixed_radian_profile_measurable cut)).neg.mul m
    refine ⟨mG,S*V,mul_nonneg S0 V0,fun ξ => ?_⟩
    rw [gEq,norm_mul,norm_neg,Complex.norm_real,mul_assoc]
    exact mul_le_mul (fixed_radian_profile_norm_bound cut hcut ξ) (VB ξ) (norm_nonneg _) S0
  have full : (fun x ξ => A x ξ + (r x ξ + g x ξ)) = b := by
    funext x ξ
    simp only [A,r,g,v,Complex.ofReal_sub]
    ring
  have eq : (fun u => classicalLocalLeftAction b K u - radianLeftQuantization A u) =
      fun u => (radianLeftQuantization r u + radianLeftQuantization g u) + compactKernelAction K u := by
    funext u
    have a := radian_left_quantization_add_actual A (fun x ξ => r x ξ + g x ξ) aG
      (left_symbol_growth_add r g rG gG) u
    rw [full,radian_left_quantization_add_actual r g rG gG] at a
    rw [classicalLocalLeftAction,a]
    abel
  rw [eq]
  exact ⟨C+D+F,ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨Cf,Df⟩,Ff⟩,
    schwartz_order_zero_jet_bound_add _ _ _ _ _ _
      (schwartz_order_zero_jet_bound_add _ _ _ _ _ _ Cr Dg) FK⟩

/-- An independently presented classical left test and the verified
compact Weyl test with the same homogeneous principal symbol differ
by an actual finite order-zero W¹,³ action. -/
theorem exists_same_principal_classical_left_weyl_difference_W13
    (P R T : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (b : E → E → ℂ) (a : E → E → ℝ) (data : ClassicalRadianLeftData b a R T)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (outside : ∀ ξ, T < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (K : E → E → ℂ) (RK : ℝ) (Ks : ContDiff ℝ 1 (Function.uncurry K))
    (Ksupport : ∀ x y, x ∉ closedBall (0 : E) RK ∨ y ∉ closedBall (0 : E) RK → K x y = 0)
    (s : E → E → ℝ) (ssupp : ∀ x ξ, x ∉ closedBall (0 : E) R → s x ξ = 0)
    (hs : CompactBaseFrequencyJets (fun x q => (s x q : ℂ)) univ)
    (N : ℝ) (N0 : 0 ≤ N) (hN : CompactBaseOrderZeroBudget s N)
    (J : E → E → ℂ) (RJ : ℝ) (Js : ContDiff ℝ 1 (Function.uncurry J))
    (Jsupp : ∀ x y, x ∉ closedBall (0 : E) RJ ∨ y ∉ closedBall (0 : E) RJ → J x y = 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound (fun u =>
      classicalLocalLeftAction b K u - compactWeylFullTest P ρ hρ hS cut a s J u) C C := by
  let L := radianLeftQuantization (fun x ξ => (a x ξ : ℂ))
  let G (u : SchwartzMap E ℂ) := compactBaseFixedInfraredWeyl P ρ hρ hS cut a u - L u
  let B := compactBaseModeQuantization P ρ hρ hS (1/2) s
  let S := compactKernelAction J
  obtain ⟨C,Cf,left⟩ := exists_classical_local_left_homogeneous_difference_W13 P R T hP hRP ρ hρ hS
    ρone b a data ha hom M M0 hM cut hcut plateau outside K RK Ks Ksupport
  obtain ⟨D,Df,principal⟩ := exists_compact_fixed_principal_weyl_left_gap_W13 P R hP hRP ρ hρ hS ρone
    a data.principalSupport ha hom M M0 hM cut hcut plateau
  obtain ⟨F,Ff,lower⟩ := exists_compact_base_order_zero_mode_action_W13 P R hP hRP.le ρ hρ hS s ssupp hs N N0 hN
  obtain ⟨H,Hf,kernel⟩ := exists_compact_kernel_order_zero_jet_bound J RJ Js Jsupp
  let W (u : SchwartzMap E ℂ) := (G u + B u) + S u
  have WB : SchwartzOrderZeroJetBound W (D+F+H) (D+F+H) :=
    schwartz_order_zero_jet_bound_add _ _ _ _ _ _
      (schwartz_order_zero_jet_bound_add G B D D F F principal (lower (1/2))) kernel
  have eq : (fun u => classicalLocalLeftAction b K u - compactWeylFullTest P ρ hρ hS cut a s J u) =
      (fun u => (classicalLocalLeftAction b K u - L u) - W u) := by
    funext u
    unfold compactWeylFullTest
    dsimp only [W,G,L,B,S]
    abel
  rw [eq]
  exact ⟨C+(D+F+H),ENNReal.add_lt_top.mpr ⟨Cf,ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨Df,Ff⟩,Hf⟩⟩,
    schwartz_order_zero_jet_bound_sub _ _ _ _ _ _ left WB⟩

end Burnett.A03
