import Burnett.Geometry.ConnectionErrorSequence
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual auxiliary metric connection and perturbation derivative

The auxiliary derivative is computed from the auxiliary metric, rather than
identified with the raw coordinate derivative. This local coordinate result
does not yet identify a manifold pullback or the physical auxiliary tensor norm.
-/

noncomputable section

namespace Burnett.Geometry.AuxiliaryConnection

open Filter
open scoped Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.ConnectionErrorSequence

/-- The coordinate expression of the covariant derivative with respect to
the actual computed auxiliary metric connection. -/
def auxiliaryPerturbationJet
    (r g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) : FirstJet :=
  covariantJet (computedConnection r x)
    (metricComponents g₁ x - metricComponents g₀ x)
    (coordinateJet (fun y => metricComponents g₁ y - metricComponents g₀ y) x)

/-- Continuity is proved for the actual finite connection contractions. -/
theorem continuousOn_covariantJet {X : Type*} [TopologicalSpace X]
    (Γ : X → Connection) (h : X → Tensor2) (dh : X → FirstJet) (S : Set X)
    (hΓ : ContinuousOn Γ S) (hh : ContinuousOn h S) (hdh : ContinuousOn dh S) :
    ContinuousOn (fun x => covariantJet (Γ x) (h x) (dh x)) S := by
  have hΓc (e b c : Index) :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hΓ e) b) c
  have hhc (b c : Index) := continuousOn_pi.mp (continuousOn_pi.mp hh b) c
  have hdc (b c d : Index) :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hdh b) c) d
  apply continuousOn_pi.mpr
  intro b
  apply continuousOn_pi.mpr
  intro c
  apply continuousOn_pi.mpr
  intro d
  exact ((hdc b c d).sub (continuousOn_finset_sum Finset.univ
    (fun e _ => (hΓc e b c).mul (hhc e d)))).sub
      (continuousOn_finset_sum Finset.univ (fun e _ => (hΓc e b d).mul (hhc c e)))

/-- C¹ metric components make the actual auxiliary derivative continuous
on the local set. No continuity of a separately supplied jet is assumed. -/
theorem continuousOn_auxiliaryPerturbationJet
    (U S : Set CoordinateSpace) (hU : IsOpen U) (hSU : S ⊆ U)
    (r g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrn : ∀ x ∈ S, (r x).Nondegenerate) (hrs : ∀ x ∈ S, (r x).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc₁ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₁ y a b) U) :
    ContinuousOn (auxiliaryPerturbationJet r g₀ g₁) S := by
  have hc : ∀ a b, ContDiffOn ℝ 1
      (fun y => (metricComponents g₁ y - metricComponents g₀ y) a b) U :=
    fun a b => (hc₁ a b).sub (hc₀ a b)
  exact continuousOn_covariantJet _ _ _ S
    (continuousOn_computedConnection r U S hU hSU hrc hrn hrs)
    ((continuousOn_components_of_contDiffOn _ U hc).mono hSU)
    ((continuousOn_coordinateJet _ U hU hc).mono hSU)

/-- Auxiliary metric C¹ regularity and compactness supply the connection
bound. Only the actual auxiliary covariant jet remains as a bound input. -/
theorem exists_eventual_rawJet_bound_of_auxiliary_bound
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (r g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrn : ∀ x ∈ K, (r x).Nondegenerate) (hrs : ∀ x ∈ K, (r x).IsSymm)
    {D : ℝ} (hD : 0 ≤ D)
    (hcov : ∀ᶠ n in atTop, ∀ x ∈ K, ‖auxiliaryPerturbationJet r g₀ (g n) x‖ ≤ D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    ∃ D' : ℝ, 0 ≤ D' ∧ ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x‖ ≤ D' := by
  obtain ⟨G, hG, hΓ⟩ := exists_pos_bound_metricConnection r U K hU hKU hK hrc hrn hrs
  refine ⟨D + 8 * G, by positivity, ?_⟩
  have hsmall := Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one
  filter_upwards [hcov, hsmall] with n hcn hsn
  intro x hx
  have hh : ‖metricComponents (g n) x - metricComponents g₀ x‖ ≤ 1 := by
    have hd := hsn x hx
    rw [dist_comm, dist_eq_norm] at hd
    exact hd.le
  have hΓ' : ‖computedConnection r x‖ ≤ G := by
    simpa only [computedConnection_eq_metricConnection r x (hrn x hx) (hrs x hx)] using hΓ x hx
  have hb := norm_rawJet_le_covariantJet (computedConnection r x)
    (metricComponents (g n) x - metricComponents g₀ x)
    (coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x)
  change ‖coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x‖ ≤
    ‖auxiliaryPerturbationJet r g₀ (g n) x‖ +
      8 * ‖computedConnection r x‖ * ‖metricComponents (g n) x - metricComponents g₀ x‖ at hb
  have hm := mul_le_mul hΓ' hh (norm_nonneg _) hG.le
  have hc := hcn x hx
  nlinarith

/-- The previous coordinate connection-error theorem now consumes the
actual auxiliary derivative. Physical tensor norms and a.e. bounds are
handled separately, without replacing the derivative by a raw jet. -/
theorem metricConnectionError_uniform_of_auxiliary_coordinate_bound
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (r g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents r y a b) U)
    (hrn : ∀ x ∈ K, (r x).Nondegenerate) (hrs : ∀ x ∈ K, (r x).IsSymm)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hd : ∀ n x, x ∈ K → DifferentiableComponentsAt (metricComponents (g n)) x)
    {D : ℝ} (hD : 0 ≤ D)
    (hcov : ∀ᶠ n in atTop, ∀ x ∈ K, ‖auxiliaryPerturbationJet r g₀ (g n) x‖ ≤ D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K := by
  obtain ⟨D', hD', hraw⟩ := exists_eventual_rawJet_bound_of_auxiliary_bound
    U K hU hKU hK r g₀ g hrc hrn hrs hD hcov hconv
  exact metricConnectionError_uniform_of_coordinate_bounds U K hU hKU hK g₀ g
    hn₀ hn hs₀ hs hc₀ hd hD' hraw hconv

end Burnett.Geometry.AuxiliaryConnection
