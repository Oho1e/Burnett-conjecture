import Burnett.Analysis.TransportWard.Weyl.NormalizedWeylMidpoint
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylPrincipalComparison
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactPrincipalLeftCommutator

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.V03

open Filter Function MeasureTheory Metric Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal Topology

/-- The actual chart Weyl operator is the compact Fourier-series Weyl
action with its original input and output cutoffs. -/
theorem windowedWeyl_action_eq_compact_fixed_infrared_weyl
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (hρOne : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ) (hSupp : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) {ξ | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hLow : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile cut ξ = 1)
    (θ : E → ℝ) (χ : SchwartzMap E ℂ) (hχ : ∀ x, χ x = (θ x : ℂ)) (W : ℝ)
    (hAmp : CompactRadianTwoPointOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ))) W W)
    (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (windowedWeylLeftSymbol θ
      (fun y ξ => (fixedInfraredSymbol cut 0 (a y) ξ : ℂ)) W hAmp) u x =
      sandwichedScalarTest χ (compactBaseFixedInfraredWeyl P ρ hρ hS cut a) u x := by
  let β (y ξ : E) := (fixedInfraredSymbol cut 0 (a y) ξ : ℂ)
  have hMul : scalarSchwartzProduct χ u = energyProduct χ u := by
    ext y
    rfl
  have hOriginal := windowedWeyl_normalized_midpoint_tendsto_leftAction θ β W hAmp χ hχ u x
  rw [hMul] at hOriginal
  change Tendsto (fun n : ℕ => (θ x : ℂ) * radianMidpointTruncation β n (energyProduct χ u) x) atTop
    (𝓝 (firstOrderAction (windowedWeylLeftSymbol θ β W hAmp) u x)) at hOriginal
  have hOld := compact_base_fixed_infrared_weyl_is_midpoint_limit P R hP hRP ρ hρ hS hρOne
    a hSupp ha hHom M hM0 hM cut hcut hLow (energyProduct χ u) x
  have hSeries := (tendsto_const_nhds (x := (θ x : ℂ))).mul hOld
  change _ = χ x * compactBaseFixedInfraredWeyl P ρ hρ hS cut a (energyProduct χ u) x
  rw [hχ]
  exact tendsto_nhds_unique hOriginal hSeries

/-- The fixed chart Weyl action equals the original homogeneous left
action plus a genuine order-zero correction. -/
theorem windowedWeyl_actual_left_comparison_W13
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (hρOne : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ) (hSupp : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) {ξ | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hLow : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile cut ξ = 1)
    (θ : E → ℝ) (χ : SchwartzMap E ℂ) (hχ : ∀ x, χ x = (θ x : ℂ)) (W : ℝ)
    (hPlateau : ∀ x ξ, a x ξ ≠ 0 → θ x = 1)
    (hAmp : CompactRadianTwoPointOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ))) W W) :
    ∃ (Q : SchwartzMap E ℂ → E → ℂ) (A D : ℝ≥0∞), A < ⊤ ∧ D < ⊤ ∧
      SchwartzOrderZeroJetBound Q A D ∧
      ∀ u : SchwartzMap E ℂ, firstOrderAction (windowedWeylLeftSymbol θ
          (fun y ξ => (fixedInfraredSymbol cut 0 (a y) ξ : ℂ)) W hAmp) u =
        radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u + Q u := by
  let L := radianLeftQuantization (fun y ξ => (a y ξ : ℂ))
  let V := compactBaseFixedInfraredWeyl P ρ hρ hS cut a
  let C := compactPrincipalLeftCommutator a χ
  let Γ := sandwichedScalarTest χ (fun u => V u - L u)
  let J (u : SchwartzMap E ℂ) (x : E) := χ x * C u x
  obtain ⟨K, hK, hGap⟩ := exists_compact_fixed_principal_weyl_left_gap_W13
    P R hP hRP ρ hρ hS hρOne a hSupp ha hHom M hM0 hM cut hcut hLow
  obtain ⟨H, hH, hCom⟩ := exists_compact_principal_left_commutator_W13
    P R hP hRP ρ hρ hS hρOne a hSupp ha hHom M hM0 hM
    (patchFourierMoment 1 χ) (patchFourierMoment 2 χ)
    (patch_moment_nonneg _ _) (patch_moment_nonneg _ _)
  let U := eLpNorm (χ : E → ℂ) ⊤ volume
  let T := ∑ j : Index, eLpNorm (energyPartial j χ : E → ℂ) ⊤ volume
  have hU : U < ⊤ := (χ.memLp ⊤ volume).2
  have hT : T < ⊤ := ENNReal.sum_lt_top.mpr fun j _ => ((energyPartial j χ).memLp ⊤ volume).2
  have hJet (j : Index) : eLpNorm (energyPartial j χ : E → ℂ) ⊤ volume ≤ T :=
    Finset.single_le_sum (f := fun k : Index => eLpNorm (energyPartial k χ : E → ℂ) ⊤ volume)
      (fun _ _ => bot_le) (Finset.mem_univ j)
  have hΓ : SchwartzOrderZeroJetBound Γ (U^2*K) (2*U*T*K + U^2*K) :=
    schwartz_order_zero_jet_bound_sandwich χ (fun u => V u - L u) K K U T hGap le_rfl hJet
  have hJ : SchwartzOrderZeroJetBound J (U*H) (T*H + U*H) :=
    schwartz_order_zero_jet_bound_output_product χ C H H U T (hCom χ le_rfl le_rfl) le_rfl hJet
  have hQ := schwartz_order_zero_jet_bound_add Γ J _ _ _ _ hΓ hJ
  refine ⟨fun u => Γ u + J u, _, _, ?_, ?_, hQ, ?_⟩
  · exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (ENNReal.pow_lt_top hU) hK, ENNReal.mul_lt_top hU hH⟩
  · have hLeft : 2*U*T*K < ⊤ := ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hU) hT) hK
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hLeft,
      ENNReal.mul_lt_top (ENNReal.pow_lt_top hU) hK⟩, ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top hT hH, ENNReal.mul_lt_top hU hH⟩⟩
  intro u
  funext x
  have hWindow : χ x * (χ x * L u x) = L u x := by
    by_cases same : χ x = 1
    · simp only [same, one_mul]
    · have ha0 (ξ : E) : a x ξ = 0 := by
        by_contra hn
        exact same (by rw [hχ, hPlateau x ξ hn, Complex.ofReal_one])
      have hz : L u x = 0 := by
        simp only [L, radianLeftQuantization, ha0, Complex.ofReal_zero, mul_zero, zero_mul, integral_zero]
      simp only [hz, mul_zero]
  rw [windowedWeyl_action_eq_compact_fixed_infrared_weyl P R hP hRP ρ hρ hS hρOne a hSupp
    ha hHom M hM0 hM cut hcut hLow θ χ hχ W hAmp]
  change χ x * V (energyProduct χ u) x = L u x +
    (χ x * (V (energyProduct χ u) x - L (energyProduct χ u) x) +
      χ x * (L (energyProduct χ u) x - χ x * L u x))
  nth_rw 1 [← hWindow]
  ring

end Burnett.V03
