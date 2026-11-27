import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierAngularRegularity
import Burnett.Analysis.PrincipalEnergy.Freezing.ActualRescaledCoefficientAngularDecay
import Mathlib.Analysis.Complex.OperatorNorm

set_option autoImplicit false
set_option maxHeartbeats 1750000
noncomputable section

namespace Burnett.A03

open Metric Set MeasureTheory Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff

/-- The actual real cosine and sine coefficient functions have the same
uniform decay in their ambient frequency derivatives as the complex
coefficient, on the stated open frequency domain. -/
theorem exists_localized_real_spatial_coefficient_jet_bound
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
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ k : Index → ℤ,
            let coefficient := localizedSpatialFourierCoefficient P k χ a c ℓ
            let cosine := fun ξ => (coefficient ξ).re
            let sine := fun ξ => -(coefficient ξ).im
            ContDiffOn ℝ (H : ℕ) cosine U ∧ ContDiffOn ℝ (H : ℕ) sine U ∧
              ∀ ξ ∈ U, ∀ r : ℕ, r ≤ H →
                ‖iteratedFDeriv ℝ r cosine ξ‖ ≤ C * M * ℓ / (1 + ‖spatialLatticeVector k‖)^N ∧
                ‖iteratedFDeriv ℝ r sine ξ‖ ≤ C * M * ℓ / (1 + ‖spatialLatticeVector k‖)^N := by
  classical
  obtain ⟨C, hC, decay⟩ :=
    exists_actual_rescaled_coefficient_angular_decay χ hχ S P hS hP hSP support N H
  refine ⟨C, hC, ?_⟩
  choose V hV bounds using fun r : ℕ =>
    exists_rescaled_ambient_angular_spatial_jet_bound χ hχ S hS support N r
  let levels := Finset.range (H + 1)
  let K := ∑ r ∈ levels, V r
  have hVle (r : ℕ) (hr : r ≤ H) : V r ≤ K :=
    Finset.single_le_sum (fun r _ => hV r) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  intro a centers U openU smoothFrequency smoothSpatial M hM hJets c hc ℓ hℓ hSmall k coefficient cosine sine
  let realProfile (y ξ : CoordinateSpace) := rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ y
  let u (y ξ : CoordinateSpace) := (realProfile y ξ : ℂ)
  have realSmooth (y : CoordinateSpace) : ContDiffOn ℝ ∞ (realProfile y) U :=
    ContDiffOn.const_smul ((χ y)^2) ((smoothFrequency (c + ℓ • y)).sub (smoothFrequency c))
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
  have coefficientSmooth : ContDiffOn ℝ (H : ℕ) coefficient U :=
    contDiffOn_spatial_cube_fourier_coefficient P k u U openU H
      (fun y _ => Complex.ofRealCLM.contDiff.fun_comp_contDiffOn (realSmooth y)) measured dominated
  let readSine : ℂ →L[ℝ] ℝ := -Complex.imCLM
  refine ⟨Complex.reCLM.contDiff.fun_comp_contDiffOn coefficientSmooth,
    readSine.contDiff.fun_comp_contDiffOn coefficientSmooth, ?_⟩
  intro ξ hξ r hr
  have hcAt := coefficientSmooth.contDiffAt (openU.mem_nhds hξ)
  have best := decay a centers U openU smoothFrequency smoothSpatial M hM hJets c hc ℓ hℓ hSmall ξ hξ r hr k
  have control (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ = 1) :
      ‖iteratedFDeriv ℝ r (L ∘ coefficient) ξ‖ ≤
        C * M * ℓ / (1 + ‖spatialLatticeVector k‖)^N := by
    rw [L.iteratedFDeriv_comp_left hcAt (by exact_mod_cast hr)]
    calc
      _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ r coefficient ξ‖ :=
        L.norm_compContinuousMultilinearMap_le _
      _ ≤ _ := by rw [hL, one_mul]; exact best
  exact ⟨control Complex.reCLM Complex.reCLM_norm,
    control readSine (by simp only [readSine, norm_neg, Complex.imCLM_norm])⟩

end Burnett.A03
