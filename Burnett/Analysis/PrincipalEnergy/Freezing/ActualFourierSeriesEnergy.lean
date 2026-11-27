import Burnett.Analysis.PrincipalEnergy.Freezing.ModeLpJetSeries
import Burnett.Analysis.PrincipalEnergy.Freezing.CubicEnergyLpContinuity
import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteFourierActionBound
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ComplexConjugate BigOperators Topology Burnett.A03

private theorem fixed_cutoff_spatial_jets_bound (ρ : CoordinateSpace → ℝ)
    (smooth : ContDiff ℝ ∞ ρ) (compact : HasCompactSupport ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℕ, r ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ r ρ y‖ ≤ B := by
  classical
  have perOrder (r : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ y, ‖iteratedFDeriv ℝ r ρ y‖ ≤ A := by
    have hTop : (r : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hC := (smooth.continuous_iteratedFDeriv hTop).norm
    have hK := (compact.iteratedFDeriv (𝕜 := ℝ) r).norm
    obtain ⟨y, hy⟩ := hC.exists_forall_ge_of_hasCompactSupport hK
    exact ⟨_, norm_nonneg _, hy⟩
  choose A hA upper using perOrder
  let B := ∑ r ∈ Finset.range 3, A r
  refine ⟨B, Finset.sum_nonneg (fun r _ => hA r), ?_⟩
  intro r hr y
  exact (upper r y).trans (Finset.single_le_sum (fun n _ => hA n) (Finset.mem_range.mpr (by omega)))

/-- The very same local real Fourier family defines an (L^3) jet sum on
the supported field. Its three-slot action energy obeys the uniform
leading bound from the finite truncations. -/
theorem exists_actual_full_fourier_patch_energy_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap CoordinateSpace ℂ)
    (symm : ∀ a d i j k, C a d i j k = C d a i k j)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P R : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S < P) (hR : 0 < R)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (L : ℕ) (hL : 7 < L) :
    ∃ (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ)
      (hSuppρ : tsupport ρ ⊆ ball (0 : CoordinateSpace) P) (K : ℝ),
      0 ≤ K ∧ HasCompactSupport ρ ∧
      (∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (c : CoordinateSpace) (ℓ : ℝ),
        0 < ℓ → ℓ ≤ 1 → ∀ ξ : CoordinateSpace, ContDiff ℝ ∞ (fun x => a x ξ) →
        ∀ x : CoordinateSpace,
          HasSum (fun k : Index → ℤ => ∑ j : Fin 2, localizedRealSpatialModeProfile P k ρ c ℓ j x *
            localizedRealSpatialAngularMode P k χ a c ℓ j ξ)
            ((χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ))) ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers U : Set CoordinateSpace),
        IsOpen U → sphere (0 : CoordinateSpace) 1 ⊆ U →
        (∀ x : CoordinateSpace, ContDiffOn ℝ ∞ (a x) U) →
        (∀ r : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) →
        (∀ H : ℕ, ∃ B : ℝ, 0 ≤ B ∧ SpatialAngularJetBound a centers U S L H B) →
        (∀ x ξ, a x (-ξ) = -a x ξ) →
        (∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ) →
        ∀ M : ℝ, 0 ≤ M → SpatialAngularJetBound a centers U S L 16 M →
        ∀ c ∈ centers, ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), ℓ ≤ 1 →
        ∀ z : J → SchwartzMap CoordinateSpace ℂ, (∀ i x, conj (z i x) = z i x) →
          tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
          let f (k : Index → ℤ) (j : Fin 2) := localizedRealSpatialModeSchwartz P k ρ hρ hSuppρ c ℓ hℓ j
          let b (k : Index → ℤ) (j : Fin 2) := localizedRealSpatialAngularMode P k χ a c ℓ j
          ∃ h : ∀ k j i, SeparatedModeLpJet (f k j) (b k j) (z i),
            (∀ i : J, Summable (fun k : Index → ℤ => ∑ j : Fin 2, ‖(h k j i).valueLp‖)) ∧
            (∀ p : Index × J, Summable (fun k : Index → ℤ => ∑ j : Fin 2, ‖(h k j p.2).coordinateLp p.1‖)) ∧
            ∃ V : PatchFieldLpJet J,
              HasSum (fun k : Index → ℤ => ∑ j : Fin 2, separatedModeFieldLpJet (f k j) (b k j) z (h k j)) V ∧
              (∀ p : Index × J, HasWeakCoordinateDerivative3 (V.1 p.2) (V.2 p) p.1) ∧
              ‖principalCubicLpFunctional C z V‖ ≤ K * M * ℓ * euclideanFieldGradientL3 z ^ 3 := by
  classical
  obtain ⟨ρ, hρ, hSuppρ, K, hK, compact, expansion, finite⟩ :=
    exists_actual_finite_fourier_patch_action_bound C symm χ hχ S P R hS hP hSP hR support L hL
  obtain ⟨B, hB, profileJets⟩ := fixed_cutoff_spatial_jets_bound ρ hρ compact
  obtain ⟨_, _, profileSum⟩ := exists_weighted_spatial_profile_sum_bound P L hL
  obtain ⟨Kangular, hKangular, angular⟩ :=
    exists_localized_angular_mode_sphere_jet_bound χ hχ S P hS hP hSP.le support L
  refine ⟨ρ, hρ, hSuppρ, K, hK, compact, expansion, ?_⟩
  intro a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM hJets
    c hc ℓ hℓ hSmall z hz hSupp f b
  let I := Index → ℤ
  let D (k : I) (_ : Fin 2) := Kangular * M * ℓ / (spatialLatticeWeight k)^L
  have hMode (k : I) (j : Fin 2) :=
    angular a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM hJets c hc ℓ hℓ hSmall k j
  have hSmooth (k : I) (j : Fin 2) : ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0} := (hMode k j).1
  have hHomogeneous (k : I) (j : Fin 2) (t : ℝ) (ht : 0 < t) (ξ : CoordinateSpace) :
      b k j (t • ξ) = t * b k j ξ := (hMode k j).2.1 t ht ξ
  have hD (k : I) (j : Fin 2) : 0 ≤ D k j := by dsimp only [D, spatialLatticeWeight]; positivity
  have weights (r : ℕ) (hr : r ≤ 2) :
      Summable (fun k : I => ∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)) := by
    have each (k : I) :
        (∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)) =
          D k 0 * spatialProfileJetLInfinity r (localizedSpatialCosineProfile P k ρ c ℓ) +
          D k 1 * spatialProfileJetLInfinity r (localizedSpatialSineProfile P k ρ c ℓ) := by
      have profileNorm (j : Fin 2) : schwartzProfileJetLInfinity r (f k j) =
          spatialProfileJetLInfinity r (localizedRealSpatialModeProfile P k ρ c ℓ j) :=
        localized_real_spatial_mode_schwartz_Linfinity P k ρ hρ hSuppρ c ℓ hℓ j r
      rw [Fin.sum_univ_two, profileNorm 0, profileNorm 1]
      simp [localizedRealSpatialModeProfile]
    simp_rw [each]
    exact (profileSum ρ B hρ hB profileJets c ℓ hℓ (fun k => D k 0) (fun k => D k 1)
      (Kangular * M) (mul_nonneg hKangular hM) (fun k => ⟨hD k 0, le_rfl⟩)
      (fun k => ⟨hD k 1, le_rfl⟩) r hr).1
  choose h certify using fun i : J =>
    exists_summable_separated_mode_jets f b D hSmooth hHomogeneous hD
      (fun k j => (hMode k j).2.2.2) weights (z i)
  refine ⟨fun k j i => h i k j, fun i => (certify i).1, fun p => (certify p.2).2.1 p.1, ?_⟩
  let modeJet (k : I) (j : Fin 2) := separatedModeFieldLpJet (f k j) (b k j) z (fun i => h i k j)
  let v (k : I) (i : J) := ∑ j : Fin 2, (h i k j).valueLp
  let d (k : I) (p : Index × J) := ∑ j : Fin 2, (h p.2 k j).coordinateLp p.1
  let V : PatchFieldLpJet J := (fun i => ∑' k, v k i, fun p => ∑' k, d k p)
  let series (k : I) := ∑ j : Fin 2, modeJet k j
  have phaseSum (k : I) : series k = (v k, d k) := by
    apply Prod.ext
    · funext i
      simp only [series, Prod.fst_sum, Finset.sum_apply, modeJet, separatedModeFieldLpJet, v]
    · funext p
      simp only [series, Prod.snd_sum, Finset.sum_apply, modeJet, separatedModeFieldLpJet, d]
  have valueSum : HasSum v V.1 := Pi.hasSum.mpr fun i => (certify i).2.2.1
  have derivativeSum : HasSum d V.2 :=
    Pi.hasSum.mpr fun p => ((certify p.2).2.2.2 p.1).1
  have jetSum : HasSum series V := by
    rw [show series = (fun k => (v k, d k)) from funext phaseSum]
    exact valueSum.prodMk derivativeSum
  refine ⟨V, jetSum, fun p => ((certify p.2).2.2.2 p.1).2, ?_⟩
  let F := principalCubicLpFunctional C z
  have hLimit := (continuous_norm.tendsto (F V)).comp (jetSum.mapL F)
  apply le_of_tendsto hLimit
  apply Eventually.of_forall
  intro truncation
  have eq : (∑ k ∈ truncation, F (series k)) =
      principalPatchTestEnergy C z (fun i x =>
        ∑ k ∈ truncation, ∑ j : Fin 2, separatedSkewAction (f k j) (b k j) (z i) x) := by
    rw [finite_mode_energy_eq_sum C z truncation f b hSmooth hHomogeneous]
    apply Finset.sum_congr rfl
    intro k _
    change F (∑ j : Fin 2, modeJet k j) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      principal_cubic_Lp_functional_mode C z (f k j) (b k j) (hSmooth k j) (hHomogeneous k j) (fun i => h i k j)
  change ‖∑ k ∈ truncation, F (series k)‖ ≤ K * M * ℓ * euclideanFieldGradientL3 z ^ 3
  rw [eq]
  exact finite a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM hJets
    c hc ℓ hℓ hSmall z hz hSupp truncation

end Burnett.A03
