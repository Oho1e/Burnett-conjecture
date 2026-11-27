import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierDecay
import Burnett.Analysis.PrincipalEnergy.Freezing.RealCubeFourierModes
import Burnett.Analysis.PrincipalEnergy.Freezing.AngularRescaledJets

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff

private theorem localized_smooth_and_support {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (S : ℝ)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S)
    (A : CoordinateSpace → V) (hA : ContDiff ℝ ∞ A) (c : CoordinateSpace) (ℓ : ℝ) :
    ContDiff ℝ ∞ (rescaledLocalizedSymbolDifference χ A c ℓ) ∧
      tsupport (rescaledLocalizedSymbolDifference χ A c ℓ) ⊆ closedBall (0 : CoordinateSpace) S := by
  have smoothDiff : ContDiff ℝ ∞ (rescaledSpatialDifference A c ℓ) :=
    (hA.comp (contDiff_const.add (contDiff_id.const_smul ℓ))).sub contDiff_const
  refine ⟨(hχ.pow 2).smul smoothDiff, ?_⟩
  have hSquare : tsupport (fun y => (χ y)^2) ⊆ tsupport χ := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := χ) (g := χ))
  exact (tsupport_smul_subset_left _ _).trans (hSquare.trans support)

private theorem fourier_decay_of_isometric_lift
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : V →ₗᵢ[ℝ] F) (g : CoordinateSpace → V) (hg : ContDiff ℝ ∞ g)
    (S P : ℝ) (hP : 0 < P) (hSP : S ≤ P)
    (hgSupport : tsupport g ⊆ closedBall (0 : CoordinateSpace) S)
    (N : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (jets : ∀ n : ℕ, n ≤ N → ∀ y, ‖iteratedFDeriv ℝ n g y‖ ≤ M) (k : Index → ℤ) :
    ‖spatialCubeFourierCoefficient P k (L ∘ g)‖ ≤
      (max 1 ((3 / spatialModeRate P)^N) * M) / (1 + ‖spatialLatticeVector k‖)^N := by
  have liftedSupport : tsupport (L ∘ g) ⊆ closedBall (0 : CoordinateSpace) S := by
    apply closure_minimal _ isClosed_closedBall
    intro y h
    apply hgSupport
    apply subset_closure
    apply Function.mem_support.mpr
    intro hz
    exact (Function.mem_support.mp h) (by simp only [Function.comp_apply, hz, map_zero])
  have compact : HasCompactSupport (L ∘ g) :=
    (isCompact_closedBall (0 : CoordinateSpace) S).of_isClosed_subset isClosed_closure liftedSupport
  let f := compact.toSchwartzMap (L.toContinuousLinearMap.contDiff.comp hg)
  have asFunction : (f : CoordinateSpace → F) = L ∘ g := rfl
  have value (y : CoordinateSpace) (_ : y ∈ spatialFourierCube P) : ‖f y‖ ≤ M := by
    have h := jets 0 (Nat.zero_le N) y
    rw [norm_iteratedFDeriv_zero] at h
    simpa only [show f y = L (g y) from rfl, L.norm_map] using h
  have jet (y : CoordinateSpace) (_ : y ∈ spatialFourierCube P) :
      ‖iteratedFDeriv ℝ N (f : CoordinateSpace → F) y‖ ≤ M := by
    have hN : (N : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    rw [asFunction, L.norm_iteratedFDeriv_comp_left hg.contDiffAt hN]
    exact jets N le_rfl y
  have support : tsupport (f : CoordinateSpace → F) ⊆ spatialFourierCube P :=
    liftedSupport.trans (closed_ball_subset_spatial_fourier_cube S P hSP)
  simpa only [asFunction] using
    spatial_cube_fourier_coefficient_polynomial_decay f P hP N M hM support value jet k

/-- The actual complex Fourier coefficient of the rescaled real symbol has
uniform spatial mode decay with the original O(ℓ) gain. -/
theorem exists_localized_spatial_fourier_coefficient_decay
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S ≤ P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers directions : Set CoordinateSpace),
        (∀ ξ ∈ directions, ContDiff ℝ ∞ (fun x => a x ξ)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ c ∈ centers, ∀ ξ ∈ directions, ∀ j : ℕ, 0 < j → j ≤ max 1 N →
            ∀ x ∈ closedBall c S, ‖iteratedFDeriv ℝ j (fun z => a z ξ) x‖ ≤ M) →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ ξ ∈ directions, ∀ k : Index → ℤ,
            ‖localizedSpatialFourierCoefficient P k χ a c ℓ ξ‖ ≤
              C * M * ℓ / (1 + ‖spatialLatticeVector k‖)^N := by
  obtain ⟨K, hK, estimate⟩ := exists_rescaled_localized_symbol_jet_bound
    (F := ℝ) (Ω := CoordinateSpace) χ hχ S hS support N
  let C := max 1 ((3 / spatialModeRate P)^N) * K
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a centers directions smooth M hM hJets c hc ℓ hℓ hSmall ξ hξ k
  obtain ⟨hg, hSup⟩ := localized_smooth_and_support χ hχ S support (fun x => a x ξ) (smooth ξ hξ) c ℓ
  have result := fourier_decay_of_isometric_lift Complex.ofRealLI _ hg S P hP hSP hSup N
    (K * M * ℓ) (by positivity) (estimate a centers directions smooth M hM hJets c hc ℓ hℓ hSmall ξ hξ) k
  have eq : max 1 ((3 / spatialModeRate P)^N) * (K * M * ℓ) = C * M * ℓ := by
    dsimp only [C]
    ring
  rw [eq] at result
  exact result

/-- Complexifying an actual real ambient jet preserves its multilinear
operator norm. -/
def complexifyAmbientFrequencyJet (r : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => CoordinateSpace) ℝ →ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin r => CoordinateSpace) ℂ where
  toLinearMap :=
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin r => CoordinateSpace) ℝ ℂ
      Complex.ofRealCLM).toLinearMap
  norm_map' f := Complex.ofRealLI.norm_compContinuousMultilinearMap f

/-- The same polynomial bound holds for the coefficient of every fixed
actual ambient frequency jet, with its multilinear operator norm. -/
theorem exists_rescaled_ambient_fourier_jet_coefficient_decay
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S ≤ P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (N r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers directions : Set CoordinateSpace),
        (∀ x : CoordinateSpace, ∀ ξ ∈ directions, ContDiffAt ℝ (r : ℕ) (a x) ξ) →
        (∀ ξ ∈ directions, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ c ∈ centers, ∀ ξ ∈ directions, ∀ j : ℕ, 0 < j → j ≤ max 1 N →
            ∀ x ∈ closedBall c S,
              ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ r (a z) ξ) x‖ ≤ M) →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ ξ ∈ directions, ∀ k : Index → ℤ,
            ‖spatialCubeFourierCoefficient P k (fun y => complexifyAmbientFrequencyJet r
              (iteratedFDeriv ℝ r (fun w =>
                rescaledLocalizedSymbolDifference χ (fun x => a x w) c ℓ y) ξ))‖ ≤
              C * M * ℓ / (1 + ‖spatialLatticeVector k‖)^N := by
  obtain ⟨K, hK, estimate⟩ := exists_rescaled_ambient_angular_spatial_jet_bound χ hχ S hS support N r
  let C := max 1 ((3 / spatialModeRate P)^N) * K
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a centers directions smoothFrequency smoothSpatial M hM hJets c hc ℓ hℓ hSmall ξ hξ k
  let A := fun x => iteratedFDeriv ℝ r (a x) ξ
  let g := rescaledLocalizedSymbolDifference χ A c ℓ
  have exactJet (y : CoordinateSpace) :
      iteratedFDeriv ℝ r (fun w => rescaledLocalizedSymbolDifference χ (fun x => a x w) c ℓ y) ξ = g y :=
    angular_rescaled_symbol_jet_eq χ a c y ξ ℓ r (smoothFrequency (c + ℓ • y) ξ hξ)
      (smoothFrequency c ξ hξ)
  obtain ⟨hg, hSup⟩ := localized_smooth_and_support χ hχ S support A (smoothSpatial ξ hξ) c ℓ
  have bound (n : ℕ) (hn : n ≤ N) (y : CoordinateSpace) : ‖iteratedFDeriv ℝ n g y‖ ≤ K * M * ℓ := by
    have h := estimate a centers directions smoothFrequency smoothSpatial M hM hJets c hc ℓ hℓ
      hSmall ξ hξ n hn y
    simpa only [exactJet] using h
  have result := fourier_decay_of_isometric_lift (complexifyAmbientFrequencyJet r) g hg S P hP hSP hSup N
    (K * M * ℓ) (by positivity) bound k
  have eq : max 1 ((3 / spatialModeRate P)^N) * (K * M * ℓ) = C * M * ℓ := by
    dsimp only [C]
    ring
  rw [eq] at result
  simpa only [exactJet] using result

end Burnett.A03
