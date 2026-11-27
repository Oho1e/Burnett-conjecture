import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierAngularRegularity
import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierReconstruction
import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierDecay
import Burnett.Analysis.SpatialFreezing.SpatialLatticeSummability
import Mathlib.Analysis.Complex.Basic
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactBaseFourierModes

set_option autoImplicit false
set_option maxHeartbeats 2900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff Topology BigOperators

local notation "E" => CoordinateSpace

/-- The actual cube Fourier coefficient of the full symbol at the same
frequency, using the original ambient-coordinate normalization. -/
def compactBaseCubeCoefficient (P : ℝ) (a : E → E → ℂ) (k : Index → ℤ) (ξ : E) : ℂ :=
  spatialCubeFourierCoefficient P k (fun x => a x ξ)

private theorem spatial_cube_compact (P : ℝ) : IsCompact (spatialFourierCube P) := by
  let e : E ≃ₜ (Index → ℝ) := PiLp.homeomorph 2 (fun _ : Index => ℝ)
  let C : Set (Index → ℝ) := Icc (fun _ => -P) (fun _ => P)
  have same : spatialFourierCube P = e.symm '' C := by
    ext x
    constructor
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      exact ⟨fun j => (hx j).1, fun j => (hx j).2⟩
    · rintro ⟨y,hy,rfl⟩ j
      exact ⟨hy.1 j, hy.2 j⟩
  rw [same]
  exact (isCompact_Icc (α := Index → ℝ)).image e.symm.continuous

private theorem compact_base_cube_jet_measurable (P : ℝ) (a : E → E → ℂ)
    (U : Set E) (ha : CompactBaseFrequencyJets a U) (n : ℕ) (ξ : E) (hξ : ξ ∈ U) :
    AEStronglyMeasurable (fun x => iteratedFDeriv ℝ n (a x) ξ)
      ((volume : Measure E).restrict (spatialFourierCube P)) :=
  ((ha.baseJetSmooth n ξ hξ).continuous).aestronglyMeasurable

private theorem compact_base_cube_jet_locally_bound (P : ℝ) (a : E → E → ℂ)
    (U : Set E) (hU : IsOpen U) (ha : CompactBaseFrequencyJets a U) (H : ℕ)
    (ξ : E) (hξ : ξ ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ball ξ ε ⊆ U ∧
      ∃ B : ℝ, ∀ n : ℕ, n ≤ H → ∀ q ∈ ball ξ ε, ∀ x ∈ spatialFourierCube P,
        ‖iteratedFDeriv ℝ n (a x) q‖ ≤ B := by
  classical
  obtain ⟨δ,hδ,near⟩ := Metric.isOpen_iff.mp hU ξ hξ
  let ε := δ / 2
  have hε : 0 < ε := by unfold ε; positivity
  have closedNear : closedBall ξ ε ⊆ U := by
    intro q hq
    apply near
    apply mem_ball.mpr
    exact (mem_closedBall.mp hq).trans_lt (by unfold ε; linarith)
  let C := spatialFourierCube P ×ˢ closedBall ξ ε
  have hC : IsCompact C := (spatial_cube_compact P).prod (isCompact_closedBall ξ ε)
  have localBound (n : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ C, ‖iteratedFDeriv ℝ n (a p.1) p.2‖ ≤ B := by
    let m (p : E × E) := ‖iteratedFDeriv ℝ n (a p.1) p.2‖
    have smooth : ContinuousOn m C := (ha.jointJetContinuous n).norm.mono fun p hp =>
      ⟨mem_univ _, closedNear hp.2⟩
    obtain ⟨B, upper⟩ := (hC.image_of_continuousOn smooth).bddAbove
    exact ⟨max 0 B, le_max_left _ _, fun p hp => (upper (mem_image_of_mem m hp)).trans (le_max_right _ _)⟩
  choose B B0 bound using localBound
  let M := ∑ n ∈ Finset.range (H + 1), B n
  refine ⟨ε,hε,ball_subset_closedBall.trans closedNear,M,?_⟩
  intro n hn q hq x hx
  have mem : (x,q) ∈ C := ⟨hx, ball_subset_closedBall hq⟩
  exact (bound n _ mem).trans (Finset.single_le_sum (fun j _ => B0 j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- Each derivative of the original Fourier coefficient is the same
coefficient of the actual frequency jet. -/
theorem compact_base_cube_coefficient_frequency_jet (P : ℝ) (a : E → E → ℂ)
    (U : Set E) (hU : IsOpen U) (ha : CompactBaseFrequencyJets a U)
    (k : Index → ℤ) (n : ℕ) (ξ : E) (hξ : ξ ∈ U) :
    iteratedFDeriv ℝ n (compactBaseCubeCoefficient P a k) ξ =
      spatialCubeFourierCoefficient P k (fun x => iteratedFDeriv ℝ n (a x) ξ) := by
  exact iteratedFDeriv_spatial_cube_fourier_coefficient P k a U hU n
    (fun x _ => ha.frequencySmooth x)
    (fun j _ q hq => compact_base_cube_jet_measurable P a U ha j q hq)
    (compact_base_cube_jet_locally_bound P a U hU ha n) n le_rfl ξ hξ

theorem compact_base_cube_coefficient_smooth (P : ℝ) (a : E → E → ℂ)
    (U : Set E) (hU : IsOpen U) (ha : CompactBaseFrequencyJets a U) (k : Index → ℤ) :
    ContDiffOn ℝ ∞ (compactBaseCubeCoefficient P a k) U := by
  refine contDiffOn_infty.mpr fun n => ?_
  exact contDiffOn_spatial_cube_fourier_coefficient P k a U hU n
    (fun x _ => ha.frequencySmooth x)
    (fun j _ q hq => compact_base_cube_jet_measurable P a U ha j q hq)
    (compact_base_cube_jet_locally_bound P a U hU ha n)

/-- The true coefficient of a compact-base symbol inherits the full
polynomial lattice decay from the fixed-frequency base derivatives. -/
theorem compact_base_cube_coefficient_jet_decay (P R : ℝ) (hP : 0 < P) (hRP : R ≤ P)
    (a : E → E → ℂ) (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (U : Set E) (hU : IsOpen U) (ha : CompactBaseFrequencyJets a U)
    (n L : ℕ) (ξ : E) (hξ : ξ ∈ U) (D : ℝ) (D0 : 0 ≤ D)
    (hV : ∀ x, ‖iteratedFDeriv ℝ n (a x) ξ‖ ≤ D)
    (hD : ∀ x, ‖iteratedFDeriv ℝ L (fun y => iteratedFDeriv ℝ n (a y) ξ) x‖ ≤ D)
    (k : Index → ℤ) :
    ‖iteratedFDeriv ℝ n (compactBaseCubeCoefficient P a k) ξ‖ ≤
      (max 1 ((3 / spatialModeRate P)^L) * D) / spatialLatticeWeight k ^ L := by
  let g (x : E) := iteratedFDeriv ℝ n (a x) ξ
  have zero (x : E) (hx : x ∉ closedBall (0 : E) R) : g x = 0 := by
    have all : a x = (fun _ : E => (0 : ℂ)) := funext fun q => support x q hx
    simp only [g, all, iteratedFDeriv_zero_fun, Pi.zero_apply]
  have gS : tsupport g ⊆ closedBall (0 : E) R := by
    apply closure_minimal _ isClosed_closedBall
    intro x mem
    by_contra hx
    exact mem (zero x hx)
  have c : HasCompactSupport g := (isCompact_closedBall (0 : E) R).of_isClosed_subset isClosed_closure gS
  let f := c.toSchwartzMap (ha.baseJetSmooth n ξ hξ)
  have fEq : (f : E → _) = g := rfl
  have hv (x : E) (_ : x ∈ spatialFourierCube P) : ‖f x‖ ≤ D := hV x
  have hd (x : E) (_ : x ∈ spatialFourierCube P) : ‖iteratedFDeriv ℝ L (f : E → _) x‖ ≤ D := by
    rw [fEq]
    exact hD x
  rw [compact_base_cube_coefficient_frequency_jet P a U hU ha k n ξ hξ]
  change ‖spatialCubeFourierCoefficient P k g‖ ≤ _
  rw [← fEq]
  exact spatial_cube_fourier_coefficient_polynomial_decay f P hP L D D0
    (gS.trans (closed_ball_subset_spatial_fourier_cube R P hRP)) hv hd k

end Burnett.A03
