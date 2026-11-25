import Burnett.Analysis.FrozenTransport.V03PrincipalCoefficientRemainder
import Burnett.Analysis.TransportWard.Amplitude

/-! Coefficients taken from the actual first-order Gamma–Gamma density. -/

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Burnett.V03

open Set MeasureTheory Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open scoped BigOperators ContDiff Interval Matrix.Norms.Elementwise Topology

/-- The open domain of the actual inverse-metric and volume density formulas. -/
def nonsingularMetricDomain : Set Mat := {G | G.det ≠ 0}

theorem isOpen_nonsingularMetricDomain : IsOpen nonsingularMetricDomain :=
  (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set ℝ)).preimage continuous_id.matrix_det

private theorem det_contDiffOn_of_entries (A : Mat → Mat) (U : Set Mat)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun G => A G i j) U) :
    ContDiffOn ℝ ∞ (fun G => (A G).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hA (σ i) i)

private theorem entry_smooth (i j : Fin 4) : ContDiff ℝ ∞ (fun G : Mat => G i j) :=
  (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 4 → ℝ) i)

private theorem contDiffOn_inverseMetricEntry (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun G : Mat => inverseMatrix G i j) nonsingularMetricDomain := by
  have hd := det_contDiffOn_of_entries id nonsingularMetricDomain
    (fun a b => (entry_smooth a b).contDiffOn)
  have hadj : ContDiffOn ℝ ∞ (fun G : Mat => G.adjugate i j) nonsingularMetricDomain := by
    simp only [Matrix.adjugate_apply]
    apply det_contDiffOn_of_entries
    intro a b
    by_cases ha : a = j
    · subst a
      simpa using (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : Mat => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) b) nonsingularMetricDomain)
    · simpa [Matrix.updateRow_apply, ha] using (entry_smooth a b).contDiffOn
  simpa only [inverseMatrix, matrixInverse, Matrix.inv_def, Ring.inverse_eq_inv',
    id_eq, Matrix.smul_apply, smul_eq_mul] using
    (hd.inv fun _ hG => hG).mul hadj

private theorem contDiffOn_metricDensity :
    ContDiffOn ℝ ∞ metricDensity nonsingularMetricDomain := by
  have hd := det_contDiffOn_of_entries id nonsingularMetricDomain
    (fun a b => (entry_smooth a b).contDiffOn)
  have habs : ContDiffOn ℝ ∞ (fun G : Mat => |G.det|) nonsingularMetricDomain :=
    (contDiffOn_abs (s := {r : ℝ | r ≠ 0}) (fun _ hr => hr)).comp hd (fun _ hG => hG)
  exact habs.sqrt (fun _ hG => abs_ne_zero.mpr hG)

private theorem contDiffOn_gammaCross_inverse (X Y : Jet) :
    ContDiffOn ℝ ∞ (fun G : Mat => gammaCross (inverseMatrix G) X Y) nonsingularMetricDomain := by
  have hΓ (Z : Jet) (a b c : Fin 4) :
      ContDiffOn ℝ ∞ (fun G : Mat => christoffel (inverseMatrix G) Z a b c)
        nonsingularMetricDomain := by
    unfold christoffel
    exact ContDiffOn.sum fun d _ => (contDiffOn_inverseMetricEntry a d).mul contDiffOn_const
  unfold gammaCross connectionCross
  exact ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ =>
    (contDiffOn_inverseMetricEntry b c).mul (ContDiffOn.sum fun a _ => ContDiffOn.sum fun e _ =>
      ((hΓ X a a e).mul (hΓ Y e b c)).sub ((hΓ X a c e).mul (hΓ Y e b a)))

theorem contDiffOn_metricKineticCoefficient (X Y : Jet) :
    ContDiffOn ℝ ∞ (fun G : Mat => metricKineticCoefficient G X Y) nonsingularMetricDomain := by
  simp only [metricKineticCoefficient, kineticCoefficient_eq_cross]
  exact contDiffOn_metricDensity.mul ((contDiffOn_gammaCross_inverse X Y).add
    (contDiffOn_gammaCross_inverse Y X))

/-- A spatial derivative and an index of the fixed real field basis. -/
abbrev ActionSlot (ι : Type*) := Fin 4 × ι

/-- Actual jet with one prescribed metric basis tensor in one derivative slot. -/
def metricAxisJet {ι : Type*} (S : ι → Mat) (s : ActionSlot ι) : Jet :=
  Pi.single s.1 (S s.2)

/-- The Euler coefficient `C_{IJ}^{ab}` in the chosen metric basis, read by
polarizing the actual density on two basis jets. -/
def metricActionCoefficient {ι : Type*} (S : ι → Mat) (s t : ActionSlot ι) (G : Mat) : ℝ :=
  metricKineticCoefficient G (metricAxisJet S s) (metricAxisJet S t)

theorem metricActionCoefficient_swap {ι : Type*} (S : ι → Mat) (s t : ActionSlot ι) :
    metricActionCoefficient S s t = metricActionCoefficient S t s := by
  funext G
  simp only [metricActionCoefficient, metricKineticCoefficient_eq_polarization]
  rw [add_comm (metricAxisJet S s) (metricAxisJet S t)]
  ring

theorem contDiffOn_metricActionCoefficient {ι : Type*} (S : ι → Mat) (s t : ActionSlot ι) :
    ContDiffOn ℝ ∞ (metricActionCoefficient S s t) nonsingularMetricDomain :=
  contDiffOn_metricKineticCoefficient _ _

private def metricKineticBilinear (G : Mat) : Jet →ₗ[ℝ] Jet →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (metricKineticCoefficient G)
    (fun X Y Z => by simp only [metricKineticCoefficient, kineticCoefficient_add_left, mul_add])
    (fun r X Y => by simp only [metricKineticCoefficient, kineticCoefficient_smul_left, smul_eq_mul]; ring)
    (fun X Y Z => by simp only [metricKineticCoefficient, kineticCoefficient_add_right, mul_add])
    (fun r X Y => by simp only [metricKineticCoefficient, kineticCoefficient_smul_right, smul_eq_mul]; ring)

/-- The jet with the supplied coordinates in the fixed field basis. -/
def metricJetOfComponents {ι : Type*} [Fintype ι] (S : ι → Mat) (p : ActionSlot ι → ℝ) : Jet :=
  ∑ s, p s • metricAxisJet S s

theorem metricJetOfComponents_apply {ι : Type*} [Fintype ι] (S : ι → Mat)
    (p : ActionSlot ι → ℝ) (a : Fin 4) :
    metricJetOfComponents S p a = ∑ i, p (a, i) • S i := by
  have h (b : Fin 4) (i : ι) :
      (p (b, i) • metricAxisJet S (b, i)) a = if b = a then p (b, i) • S i else 0 := by
    by_cases hba : b = a
    · simp [metricAxisJet, hba]
    · simp [metricAxisJet, hba]
  simp only [metricJetOfComponents, Finset.sum_apply, Fintype.sum_prod_type, h]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The factor one half gives the paper's actual first-order Lagrangian in
arbitrary fixed field coordinates. -/
theorem metricActionDensity_eq_coefficient_sum {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : Mat) (p : ActionSlot ι → ℝ) :
    metricActionDensity G (metricJetOfComponents S p) =
      (1 / 2 : ℝ) * ∑ s, ∑ t, metricActionCoefficient S s t G * p s * p t := by
  let X := metricJetOfComponents S p
  have hDiag : metricKineticBilinear G X X = 2 * metricActionDensity G X := by
    change metricKineticCoefficient G X X = _
    simp only [metricKineticCoefficient, kineticCoefficient_eq_cross,
      metricActionDensity, gammaCross, connectionCross, quadraticAction,
      Burnett.Geometry.CurvatureDifference.quadraticDifference]
    ring
  have hSum : metricKineticBilinear G X X =
      ∑ s, ∑ t, metricActionCoefficient S s t G * p s * p t := by
    simp only [X, metricJetOfComponents, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    change p s * (p t * metricActionCoefficient S t s G) = _
    rw [congrFun (metricActionCoefficient_swap S t s) G]
    ring
  rw [← hSum, hDiag]
  ring

/-- The actual principal remainder inherits the required simultaneous
transposition of derivative and field indices. -/
theorem metricPrincipalRemainder_swap {ι : Type*}
    (S : ι → Mat) (s t : ActionSlot ι) (g h : Mat) :
    principalCoefficientRemainder (metricActionCoefficient S s t) g h =
      principalCoefficientRemainder (metricActionCoefficient S t s) g h := by
  rw [metricActionCoefficient_swap S s t]

theorem metricPrincipalRemainder_eq_integral {ι : Type*} (S : ι → Mat)
    (s t : ActionSlot ι) (g h : Mat)
    (hseg : ∀ u ∈ Icc (0 : ℝ) 1, (fieldSegment g h u).det ≠ 0) :
    principalCoefficientRemainder (metricActionCoefficient S s t) g h =
      -(∫ u in (0 : ℝ)..1,
        (1 - u) * secondFDeriv (metricActionCoefficient S s t) (fieldSegment g h u) h h) := by
  exact principalCoefficientRemainder_eq_integral _ isOpen_nonsingularMetricDomain
    (contDiffOn_metricActionCoefficient S s t) g h hseg

theorem metricPrincipalRemainder_pointwise_bounds {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : ι → Mat) (s t : ActionSlot ι) (g h : X → Mat) (x : X)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hseg : ∀ u ∈ Icc (0 : ℝ) 1, (fieldSegment (g x) (h x) u).det ≠ 0)
    {M₂ M₃ : ℝ}
    (hM₂ : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖secondFDeriv (metricActionCoefficient S s t) (fieldSegment (g x) (h x) u)‖ ≤ M₂)
    (hM₃₀ : 0 ≤ M₃)
    (hM₃ : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v,
      ‖thirdFDeriv (metricActionCoefficient S s t) (fieldSegment (g x) (h x) u)
        (h x) (h x) v‖ ≤ M₃ * ‖h x‖^2 * ‖v‖) :
    ‖principalCoefficientRemainder (metricActionCoefficient S s t) (g x) (h x)‖ ≤ M₂ * ‖h x‖^2 ∧
    ‖fderiv ℝ (fun y => principalCoefficientRemainder (metricActionCoefficient S s t) (g y) (h y)) x‖ ≤
      M₃ * ‖h x‖^2 * ‖fderiv ℝ g x‖ + M₂ * ‖h x‖ * ‖fderiv ℝ h x‖ :=
  ⟨norm_principalCoefficientRemainder_le _ isOpen_nonsingularMetricDomain
      (contDiffOn_metricActionCoefficient S s t) (g x) (h x) hseg hM₂,
    norm_fderiv_principalCoefficientRemainder_le _ isOpen_nonsingularMetricDomain
      (contDiffOn_metricActionCoefficient S s t) g h x hg hh hseg hM₂ hM₃₀ hM₃⟩

end Burnett.V03
