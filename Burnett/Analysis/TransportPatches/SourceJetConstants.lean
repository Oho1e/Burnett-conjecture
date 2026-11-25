import Burnett.Analysis.TransportPatches.LocalizedSourceScale
import Burnett.Analysis.GaugeProjection.LocalizedVacuumSourceBound

/-! Uniform constants for the fixed-background and gauge parts of the
actual localized source, independent of the patch cutoff. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.C03

open Set Metric Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators

open private loweredGaugeCovector_expanded from Burnett.Analysis.GaugeProjection.LocalizedVacuumSourceBound

private def uncutSourceTerms (q : LocalizedSourceJets) : Tensor2 × (Index → ℝ) :=
  let (A, D, DI, _, _, D₂) := q
  (fun i j => projectedSourceFirstJetRemainder A D DI i j - ∑ a, ∑ b, A a b * D₂ a b i j,
    fun j => loweredGaugeCovector A D j)

private theorem continuous_uncutSourceTerms : Continuous uncutSourceTerms := by
  unfold uncutSourceTerms projectedSourceFirstJetRemainder firstJetRicciRemainder ricci christoffel koszul
  dsimp only
  simp only [loweredGaugeCovector_expanded]
  fun_prop

/-- The uncut first-jet and fixed-background term, and the lowered gauge
source, are bounded on the actual original jet range. -/
theorem exists_uncutSource_uniform_bound
    (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (inv g g₀ : CoordinateSpace → Tensor2) (x : CoordinateSpace),
      ‖localizedSourceJets inv g g₀ x‖ ≤ B →
      (∀ i j, ‖projectedSourceFirstJetRemainder (inv x) (coordinateJet g x)
          (coordinateJet inv x) i j -
        scalarWaveAt (inv x) (fun y => g₀ y i j) x‖ ≤ C) ∧
      (∀ j, ‖coordinateGaugeCovector inv g x j‖ ≤ C) := by
  let ball := closedBall (0 : LocalizedSourceJets) B
  have hCompact : IsCompact ball := isCompact_closedBall _ _
  obtain ⟨C, hC, hF⟩ :=
    (hCompact.image continuous_uncutSourceTerms).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro inv g g₀ x hx
  let p := localizedSourceJets inv g g₀ x
  let q := uncutSourceTerms p
  have hp : p ∈ ball := by
    simpa only [ball, mem_closedBall, dist_zero_right] using hx
  have hQ : ‖q‖ ≤ C := hF q (mem_image_of_mem _ hp)
  constructor
  · intro i j
    change ‖q.1 i j‖ ≤ C
    exact ((norm_le_pi_norm (q.1 i) j).trans (norm_le_pi_norm q.1 i)).trans
      ((norm_fst_le q).trans hQ)
  · intro j
    change ‖q.2 j‖ ≤ C
    exact (norm_le_pi_norm q.2 j).trans ((norm_snd_le q).trans hQ)

end Burnett.C03
