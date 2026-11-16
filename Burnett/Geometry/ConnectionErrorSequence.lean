import Burnett.Geometry.PerturbationJet
import Burnett.Geometry.InverseSequence
import Burnett.Geometry.BackgroundConnection

/-!
# Local coordinate-bound consumer for the actual connection error

This theorem combines compact inverse control, background C¹ regularity,
and the actual raw coordinate first-jet bound. The paper's admissibility
bound instead uses D = ∇ʳ and the physical auxiliary-r norm. Its conversion
to these coordinate norms remains a separate open geometric interface;
this file does not rename that input or assert the full F04 conclusion.
-/

noncomputable section

namespace Burnett.Geometry.ConnectionErrorSequence

open Filter
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.PerturbationJet
open scoped Topology

/-- Reversing the sign of the connection reconstructs the actual raw jet.
This is algebra on first derivatives, independent of auxiliary-norm
comparisons or smoothness claims. -/
theorem covariantJet_reverse (Γ : Connection) (h : Tensor2) (dh : FirstJet) :
    covariantJet (-Γ) h (covariantJet Γ h dh) = dh := by
  funext b c d
  simp only [covariantJet, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

/-- A future ∇ʳ-to-coordinate consumer can use this direction after it has
constructed the actual auxiliary connection and the physical-r norm
comparison. Those geometric bridges are not assumptions hidden here. -/
theorem norm_rawJet_le_covariantJet (Γ : Connection) (h : Tensor2) (dh : FirstJet) :
    ‖dh‖ ≤ ‖covariantJet Γ h dh‖ + 8 * ‖Γ‖ * ‖h‖ := by
  have hb := norm_covariantJet_le (-Γ) h (covariantJet Γ h dh)
  simpa only [covariantJet_reverse, norm_neg] using hb

/-- The connection error converges uniformly on K from local background
C¹ components, the actual coordinate perturbation first-jet bound, and
the actual metric component uniform convergence. There are no supplied
inverse bounds, inverse smallness, Γ bounds, J bounds, or E-convergence
premises. The remaining raw-coordinate/r-norm distinction is explicit. -/
theorem metricConnectionError_uniform_of_coordinate_bounds
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hd : ∀ n x, x ∈ K → DifferentiableComponentsAt (metricComponents (g n)) x)
    {D : ℝ} (hD : 0 ≤ D)
    (hraw : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖coordinateJet (fun y => metricComponents (g n) y - metricComponents g₀ y) x‖ ≤ D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K := by
  have hsym₀ : ∀ x ∈ K, (g₀ x).IsSymm := fun x hx => (hs₀ x hx).self_of_nhds
  have hsym : ∀ n x, x ∈ K → (g n x).IsSymm :=
    fun n x hx => (hs n x hx).self_of_nhds
  have hcK : ContinuousOn (metricComponents g₀) K :=
    (BackgroundConnection.continuousOn_components_of_contDiffOn (metricComponents g₀) U hc₀).mono hKU
  have hd₀ : ∀ x ∈ K, DifferentiableComponentsAt (metricComponents g₀) x := by
    intro x hx a b
    exact ((hc₀ a b).differentiableOn (by simp) x (hKU hx)).differentiableAt
      (hU.mem_nhds (hKU hx))
  obtain ⟨B, hB, hbase, hest, hinvUniform⟩ := InverseSequence.compact_uniform_inverseMetric
    atTop g₀ g coordinateBasis K hK hcK hn₀ hsym₀ hn hsym hconv
  have hbase' : ∀ x (hx : x ∈ K), ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ B := hbase
  have hsmall : ∀ᶠ n in atTop, ∀ x (hx : x ∈ K),
      16 * ‖metricComponents (g n) x - metricComponents g₀ x‖ *
        ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ 1/2 := by
    filter_upwards [hest] with n hnEst
    intro x hx
    exact (hnEst x hx).1
  obtain ⟨G, hG, hΓ⟩ := BackgroundConnection.exists_pos_bound_metricConnection
    g₀ U K hU hKU hK hc₀ hn₀ hsym₀
  have hjet := eventually_bound_perturbationCovariantJet K g₀ g hn₀ hG.le hΓ hraw hconv
  exact metricConnectionError_tendstoUniformlyOn K g₀ g hn₀ hn hs₀ hs hd₀ hd
    (H := D + 8*G) (by positivity) hbase' hjet hsmall hconv

end Burnett.Geometry.ConnectionErrorSequence
