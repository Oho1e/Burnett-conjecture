import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedRealAngularCoefficientJets
import Burnett.Analysis.PrincipalEnergy.Freezing.WeightedSpatialProfileSums

set_option autoImplicit false
set_option maxHeartbeats 1450000
noncomputable section

namespace Burnett.A03

open Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff

/-- The two real symbols attached to the two physical modes of one lattice index. -/
def localizedRealSpatialAngularMode (P : ℝ) (k : Index → ℤ)
    (χ : CoordinateSpace → ℝ) (a : CoordinateSpace → CoordinateSpace → ℝ)
    (c : CoordinateSpace) (ℓ : ℝ) (j : Fin 2) (ξ : CoordinateSpace) : ℝ :=
  let coefficient := localizedSpatialFourierCoefficient P k χ a c ℓ ξ
  if j = 0 then coefficient.re else -coefficient.im

/-- Actual mixed ambient-frequency and spatial derivative bounds on the
fixed unscaled neighborhood of the centers. -/
def SpatialAngularJetBound (a : CoordinateSpace → CoordinateSpace → ℝ)
    (centers U : Set CoordinateSpace) (S : ℝ) (L H : ℕ) (M : ℝ) : Prop :=
  ∀ c ∈ centers, ∀ ξ ∈ U, ∀ r : ℕ, r ≤ H → ∀ j : ℕ, 0 < j → j ≤ max 1 L →
    ∀ x ∈ closedBall c S, ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ r (a z) ξ) x‖ ≤ M

private theorem homogeneous_smooth_off_zero
    (b : CoordinateSpace → ℝ) (U : Set CoordinateSpace) (hU : IsOpen U)
    (hSphere : sphere (0 : CoordinateSpace) 1 ⊆ U)
    (smooth : ContDiffOn ℝ ∞ b U)
    (hom : ∀ (t : ℝ), 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) :
    ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} := by
  intro ξ hξ
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let s : ℝ := ‖ξ‖⁻¹
  have hs : 0 < s := inv_pos.mpr hnorm
  have hn : s • ξ ∈ sphere (0 : CoordinateSpace) 1 := by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le]
    exact inv_mul_cancel₀ hnorm.ne'
  have hAt : ContDiffAt ℝ ∞ b (s • ξ) := smooth.contDiffAt (hU.mem_nhds (hSphere hn))
  have hScale : ContDiffAt ℝ ∞ (fun y : CoordinateSpace => s • y) ξ :=
    contDiffAt_id.const_smul s
  have hComp : ContDiffAt ℝ ∞ (fun y : CoordinateSpace => b (s • y)) ξ := hAt.comp ξ hScale
  have eq : (fun y : CoordinateSpace => ‖ξ‖ * b (s • y)) = b := by
    funext y
    rw [hom s hs, ← mul_assoc, mul_inv_cancel₀ hnorm.ne', one_mul]
  have hScaled : ContDiffAt ℝ ∞ (fun y : CoordinateSpace => ‖ξ‖ * b (s • y)) ξ :=
    contDiffAt_const.mul hComp
  exact (eq ▸ hScaled).contDiffWithinAt

/-- The cosine and sine coefficients of the locked spatial Fourier
construction are smooth odd homogeneous symbols. A single constant bounds
their ambient derivatives of orders 0–16 on the unit sphere. -/
theorem exists_localized_angular_mode_sphere_jet_bound
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S ≤ P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (L : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers U : Set CoordinateSpace),
        IsOpen U → sphere (0 : CoordinateSpace) 1 ⊆ U →
        (∀ x : CoordinateSpace, ContDiffOn ℝ ∞ (a x) U) →
        (∀ r : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) →
        (∀ H : ℕ, ∃ B : ℝ, 0 ≤ B ∧ SpatialAngularJetBound a centers U S L H B) →
        (∀ x ξ, a x (-ξ) = -a x ξ) →
        (∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ) →
        ∀ M : ℝ, 0 ≤ M → SpatialAngularJetBound a centers U S L 16 M →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ k : Index → ℤ, ∀ j : Fin 2,
            let b := localizedRealSpatialAngularMode P k χ a c ℓ j
            ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} ∧
              (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) ∧
              (∀ ξ, b (-ξ) = -b ξ) ∧ ∀ r : ℕ, r ≤ 16 → ∀ ξ ∈ sphere (0 : CoordinateSpace) 1,
                ‖iteratedFDeriv ℝ r b ξ‖ ≤ K * M * ℓ / (spatialLatticeWeight k)^L := by
  obtain ⟨K, hK, quantitative⟩ :=
    exists_localized_real_spatial_coefficient_jet_bound χ hχ S P hS hP hSP support L 16
  refine ⟨K, hK, ?_⟩
  intro a centers U hU hSphere frequency spatial higher hOdd hHom M hM hBound c hc ℓ hℓ hSmall k j b
  let coeff := localizedSpatialFourierCoefficient P k χ a c ℓ
  let cosMode (ξ : CoordinateSpace) := (coeff ξ).re
  let sinMode (ξ : CoordinateSpace) := -(coeff ξ).im
  have smoothOrders (H : ℕ) : ContDiffOn ℝ (H : ℕ) cosMode U ∧ ContDiffOn ℝ (H : ℕ) sinMode U := by
    obtain ⟨_, _, bound⟩ := exists_localized_real_spatial_coefficient_jet_bound χ hχ S P hS hP hSP support L H
    obtain ⟨B, hB, hBounds⟩ := higher H
    have result := bound a centers U hU frequency (fun r _ ξ hξ => spatial r ξ hξ) B hB hBounds c hc ℓ hℓ hSmall k
    exact ⟨result.1, result.2.1⟩
  have quantitativeModes := quantitative a centers U hU frequency (fun r _ ξ hξ => spatial r ξ hξ)
    M hM hBound c hc ℓ hℓ hSmall k
  obtain ⟨odd, hom⟩ := localized_spatial_fourier_real_modes_odd_homogeneous P k χ a c ℓ hOdd hHom
  by_cases hj : j = 0
  · have eq : b = cosMode := by funext ξ; simp only [b, localizedRealSpatialAngularMode, if_pos hj, cosMode, coeff]
    have hHomCos (t : ℝ) (ht : 0 < t) (ξ : CoordinateSpace) : cosMode (t • ξ) = t * cosMode ξ :=
      (hom t ht ξ).1
    rw [eq]
    refine ⟨homogeneous_smooth_off_zero cosMode U hU hSphere
      (contDiffOn_infty.mpr fun H => (smoothOrders H).1) hHomCos, hHomCos, fun ξ => (odd ξ).1, ?_⟩
    intro r hr ξ hξ
    exact (quantitativeModes.2.2 ξ (hSphere hξ) r hr).1
  · have eq : b = sinMode := by funext ξ; simp only [b, localizedRealSpatialAngularMode, if_neg hj, sinMode, coeff]
    have hHomSin (t : ℝ) (ht : 0 < t) (ξ : CoordinateSpace) : sinMode (t • ξ) = t * sinMode ξ := by
      change -(coeff (t • ξ)).im = t * -(coeff ξ).im
      rw [(hom t ht ξ).2, mul_neg]
    have hOddSin (ξ : CoordinateSpace) : sinMode (-ξ) = -sinMode ξ := by
      change -(coeff (-ξ)).im = -(-(coeff ξ).im)
      rw [(odd ξ).2]
    rw [eq]
    refine ⟨homogeneous_smooth_off_zero sinMode U hU hSphere
      (contDiffOn_infty.mpr fun H => (smoothOrders H).2) hHomSin, hHomSin, hOddSin, ?_⟩
    intro r hr ξ hξ
    exact (quantitativeModes.2.2 ξ (hSphere hξ) r hr).2

end Burnett.A03
