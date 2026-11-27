import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierAngularDerivatives
import Burnett.Analysis.PrincipalEnergy.Freezing.RescaledFourierJetDecay

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.A03

open Metric Set MeasureTheory Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff

/-- The actual ambient frequency jets of the same complex coefficients of
the rescaled real spatial symbol have a common polynomial mode bound. -/
theorem exists_actual_rescaled_coefficient_angular_decay
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S ≤ P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (N H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers U : Set CoordinateSpace),
        IsOpen U → (∀ x : CoordinateSpace, ContDiffOn ℝ ∞ (a x) U) →
        (∀ r : ℕ, r ≤ H → ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ c ∈ centers, ∀ ξ ∈ U, ∀ r : ℕ, r ≤ H → ∀ j : ℕ, 0 < j → j ≤ max 1 N →
            ∀ x ∈ closedBall c S, ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ r (a z) ξ) x‖ ≤ M) →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ ξ ∈ U,
            ∀ r : ℕ, r ≤ H → ∀ k : Index → ℤ,
              ‖iteratedFDeriv ℝ r (localizedSpatialFourierCoefficient P k χ a c ℓ) ξ‖ ≤
                C * M * ℓ / (1 + ‖spatialLatticeVector k‖)^N := by
  classical
  choose D hD decays using fun r : ℕ =>
    exists_rescaled_ambient_fourier_jet_coefficient_decay χ hχ S P hS hP hSP support N r
  choose V hV bounds using fun r : ℕ =>
    exists_rescaled_ambient_angular_spatial_jet_bound χ hχ S hS support N r
  let levels := Finset.range (H + 1)
  let C := ∑ r ∈ levels, D r
  let K := ∑ r ∈ levels, V r
  refine ⟨C, Finset.sum_nonneg fun r _ => hD r, ?_⟩
  have hDle (r : ℕ) (hr : r ≤ H) : D r ≤ C :=
    Finset.single_le_sum (fun r _ => hD r) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  have hVle (r : ℕ) (hr : r ≤ H) : V r ≤ K :=
    Finset.single_le_sum (fun r _ => hV r) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  intro a centers U openU smoothFrequency smoothSpatial M hM hJets c hc ℓ hℓ hSmall
  let realProfile (y ξ : CoordinateSpace) := rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ y
  let u (y ξ : CoordinateSpace) := (realProfile y ξ : ℂ)
  have realSmooth (y : CoordinateSpace) : ContDiffOn ℝ ∞ (realProfile y) U :=
    (ContDiffOn.const_smul ((χ y)^2) ((smoothFrequency (c + ℓ • y)).sub (smoothFrequency c)))
  have complexSmooth (y : CoordinateSpace) : ContDiffOn ℝ ∞ (u y) U :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn (realSmooth y)
  have freqAt (r : ℕ) (x ξ : CoordinateSpace) (hξ : ξ ∈ U) : ContDiffAt ℝ (r : ℕ) (a x) ξ :=
    ((smoothFrequency x).contDiffAt (openU.mem_nhds hξ)).of_le (by exact_mod_cast le_top)
  have liftJet (r : ℕ) (y ξ : CoordinateSpace) (hξ : ξ ∈ U) :
      iteratedFDeriv ℝ r (u y) ξ =
        complexifyAmbientFrequencyJet r (iteratedFDeriv ℝ r (realProfile y) ξ) := by
    have hr : (r : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    exact Complex.ofRealCLM.iteratedFDeriv_comp_left ((realSmooth y).contDiffAt (openU.mem_nhds hξ)) hr
  have measured (r : ℕ) (hr : r ≤ H) (ξ : CoordinateSpace) (hξ : ξ ∈ U) :
      AEStronglyMeasurable (fun y => iteratedFDeriv ℝ r (u y) ξ)
        ((volume : Measure CoordinateSpace).restrict (spatialFourierCube P)) := by
    have exactJet (y : CoordinateSpace) : iteratedFDeriv ℝ r (realProfile y) ξ =
        rescaledLocalizedSymbolDifference χ (fun x => iteratedFDeriv ℝ r (a x) ξ) c ℓ y :=
      angular_rescaled_symbol_jet_eq χ a c y ξ ℓ r (freqAt r (c + ℓ • y) ξ hξ) (freqAt r c ξ hξ)
    have smoothDiff : ContDiff ℝ ∞
        (rescaledSpatialDifference (fun x => iteratedFDeriv ℝ r (a x) ξ) c ℓ) :=
      ((smoothSpatial r hr ξ hξ).comp (contDiff_const.add (contDiff_id.const_smul ℓ))).sub contDiff_const
    have smoothLocalized : ContDiff ℝ ∞
        (rescaledLocalizedSymbolDifference χ (fun x => iteratedFDeriv ℝ r (a x) ξ) c ℓ) :=
      (hχ.pow 2).smul smoothDiff
    simp only [fun y => liftJet r y ξ hξ, exactJet]
    exact ((complexifyAmbientFrequencyJet r).continuous.comp smoothLocalized.continuous).aestronglyMeasurable
  have dominated : ∀ angle ∈ U, ∃ ε : ℝ, 0 < ε ∧ ball angle ε ⊆ U ∧
      ∃ B : ℝ, ∀ r : ℕ, r ≤ H → ∀ q ∈ ball angle ε, ∀ y ∈ spatialFourierCube P,
        ‖iteratedFDeriv ℝ r (u y) q‖ ≤ B := by
    intro angle hAngle
    obtain ⟨ε, hε, inside⟩ := Metric.isOpen_iff.mp openU angle hAngle
    refine ⟨ε, hε, inside, K * M * ℓ, ?_⟩
    intro r hr q hq y _
    have hqU := inside hq
    have estimate := bounds r a centers U (freqAt r) (smoothSpatial r hr) M hM
      (fun center hCenter ξ hξ => hJets center hCenter ξ hξ r hr)
      c hc ℓ hℓ hSmall q hqU 0 (Nat.zero_le N) y
    rw [norm_iteratedFDeriv_zero] at estimate
    rw [liftJet r y q hqU, LinearIsometry.norm_map]
    exact estimate.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hVle r hr) hM) hℓ.le)
  intro ξ hξ r hr k
  change ‖iteratedFDeriv ℝ r (fun q => spatialCubeFourierCoefficient P k (fun y => u y q)) ξ‖ ≤ _
  rw [iteratedFDeriv_spatial_cube_fourier_coefficient P k u U openU H
    (fun y _ => complexSmooth y) measured dominated r hr ξ hξ]
  simp only [fun y => liftJet r y ξ hξ]
  have estimate := decays r a centers U (freqAt r) (smoothSpatial r hr) M hM
    (fun center hCenter q hq => hJets center hCenter q hq r hr) c hc ℓ hℓ hSmall ξ hξ k
  exact estimate.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDle r hr) hM) hℓ.le) (by positivity))

end Burnett.A03
