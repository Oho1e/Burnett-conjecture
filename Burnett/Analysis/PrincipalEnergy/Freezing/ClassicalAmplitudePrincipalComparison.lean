import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalAmplitudeLeftRemainderW13

set_option autoImplicit false
set_option maxHeartbeats 5400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

private theorem classical_amplitude_diagonal_data
    (A : E → E → E → ℂ) (a : E → E → ℝ) (R Ry T : ℝ)
    (h : CompactRadianTwoPointOrderOne A R Ry)
    (aSmooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain)
    (aSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (tail : RadianOrderZeroSymbolTail T (fun x ξ => A x x ξ - (a x ξ : ℂ))) :
    ClassicalRadianLeftData (fun x ξ => A x x ξ) a R T :=
  ⟨compact_radian_amplitude_diagonal_smooth A R Ry h,aSmooth,
    fun x ξ => h.outputSupport x x ξ,aSupport,tail⟩

/-- The actual compact amplitude test, including its separated smooth
kernel, differs from the homogeneous principal left action by a finite
order-zero operator. Its first classical remainder is the remainder
of the literal amplitude diagonal at high frequency. -/
theorem exists_compact_classical_amplitude_homogeneous_difference_W13
    (P R Ry T : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (A : E → E → E → ℂ) (h : CompactRadianTwoPointOrderOne A R Ry)
    (directions : RadianOrdinaryDirectionalAmplitudeBounds A)
    (a : E → E → ℝ)
    (aSmooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain)
    (aSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (tail : RadianOrderZeroSymbolTail T (fun x ξ => A x x ξ - (a x ξ : ℂ)))
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (outside : ∀ ξ, T < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (K : E → E → ℂ) (RK : ℝ) (Ks : ContDiff ℝ 1 (Function.uncurry K))
    (Ksupport : ∀ x y, x ∉ closedBall (0 : E) RK ∨ y ∉ closedBall (0 : E) RK → K x y = 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound (fun u =>
      compactRadianAmplitudeTestAction A R Ry h K u -
      radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u) C C := by
  let b (x ξ : E) := A x x ξ
  let B := compactRadianAmplitudeTestAction A R Ry h K
  let D := classicalLocalLeftAction b K
  let L := radianLeftQuantization (fun x ξ => (a x ξ : ℂ))
  have data := classical_amplitude_diagonal_data A a R Ry T h aSmooth aSupport tail
  obtain ⟨C,Cf,CB⟩ := exists_compact_radian_amplitude_diagonal_difference_W13 P R Ry hP hRP
    ρ hρ hS ρone A h directions K
  obtain ⟨F,Ff,FB⟩ := exists_classical_local_left_homogeneous_difference_W13 P R T hP hRP ρ hρ hS
    ρone b a data ha hom M M0 hM cut hcut plateau outside K RK Ks Ksupport
  have eq : (fun u => B u - L u) = (fun u => (B u - D u)+(D u - L u)) := by
    funext u
    abel
  rw [eq]
  exact ⟨C+F,ENNReal.add_lt_top.mpr ⟨Cf,Ff⟩,
    schwartz_order_zero_jet_bound_add (fun u => B u-D u) (fun u => D u-L u) C C F F CB FB⟩

/-- Two independently computed tests with the same homogeneous
principal symbol differ by an actual finite order-zero action. The
physical amplitude and the complete Weyl model retain their own
lower terms and smooth kernels. -/
theorem exists_compact_classical_amplitude_weyl_difference_W13
    (P R Ry T : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (A : E → E → E → ℂ) (h : CompactRadianTwoPointOrderOne A R Ry)
    (directions : RadianOrdinaryDirectionalAmplitudeBounds A)
    (a : E → E → ℝ)
    (aSmooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain)
    (aSupport : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (tail : RadianOrderZeroSymbolTail T (fun x ξ => A x x ξ - (a x ξ : ℂ)))
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
      compactRadianAmplitudeTestAction A R Ry h K u -
      compactWeylFullTest P ρ hρ hS cut a s J u) C C := by
  let b (x ξ : E) := A x x ξ
  let B := compactRadianAmplitudeTestAction A R Ry h K
  let D := classicalLocalLeftAction b K
  let W := compactWeylFullTest P ρ hρ hS cut a s J
  have data := classical_amplitude_diagonal_data A a R Ry T h aSmooth aSupport tail
  obtain ⟨C,Cf,CB⟩ := exists_compact_radian_amplitude_diagonal_difference_W13 P R Ry hP hRP
    ρ hρ hS ρone A h directions K
  obtain ⟨F,Ff,FB⟩ := exists_same_principal_classical_left_weyl_difference_W13 P R T hP hRP ρ hρ hS
    ρone b a data ha hom M M0 hM cut hcut plateau outside K RK Ks Ksupport s ssupp hs N N0 hN J RJ Js Jsupp
  have eq : (fun u => B u - W u) = (fun u => (B u - D u)+(D u - W u)) := by
    funext u
    abel
  rw [eq]
  exact ⟨C+F,ENNReal.add_lt_top.mpr ⟨Cf,Ff⟩,
    schwartz_order_zero_jet_bound_add (fun u => B u-D u) (fun u => D u-W u) C C F F CB FB⟩

end Burnett.A03
