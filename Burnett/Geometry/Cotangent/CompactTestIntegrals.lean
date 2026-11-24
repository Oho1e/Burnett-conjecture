import Burnett.Geometry.Cotangent.CompactTestPartition
import Burnett.Geometry.Cotangent.Core
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Assemble chartwise tested integrals on a compact base support using one finite partition. -/

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.CotangentTests

open Filter Set MeasureTheory
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open scoped ContDiff Topology Manifold

/-- The same finite weights may be used on two measure spaces related by a projection.
Only their sum on the base support and the localized integrability and equality are used. -/
theorem integral_eq_of_finite_projected_parts {X P : Type*} [MeasurableSpace X] [MeasurableSpace P]
    (π : P → X) (dV : Measure X) (μ : Measure P) {K : Set X}
    (R : X → ℝ) (G : P → ℝ) (hR : ∀ᵐ x ∂dV, x ∉ K → R x = 0)
    (hG : ∀ᵐ p ∂μ, π p ∉ K → G p = 0)
    {n : ℕ} (ρ : Fin n → X → ℝ) (hρ : ∀ x ∈ K, ∑ k, ρ k x = 1)
    (hpart : ∀ k, Integrable (fun x => ρ k x * R x) dV ∧
      Integrable (fun p => ρ k (π p) * G p) μ ∧
      (∫ x, ρ k x * R x ∂dV) = ∫ p, ρ k (π p) * G p ∂μ) :
    Integrable R dV ∧ Integrable G μ ∧ (∫ x, R x ∂dV) = ∫ p, G p ∂μ := by
  have hbase : (fun x => ∑ k, ρ k x * R x) =ᵐ[dV] R := by
    filter_upwards [hR] with x hx
    by_cases hk : x ∈ K
    · rw [← Finset.sum_mul, hρ x hk, one_mul]
    · simp [hx hk]
  have hphase : (fun p => ∑ k, ρ k (π p) * G p) =ᵐ[μ] G := by
    filter_upwards [hG] with p hp
    by_cases hk : π p ∈ K
    · rw [← Finset.sum_mul, hρ _ hk, one_mul]
    · simp [hp hk]
  have ib := integrable_finset_sum Finset.univ (fun i _ => (hpart i).1)
  have ip := integrable_finset_sum Finset.univ (fun i _ => (hpart i).2.1)
  refine ⟨ib.congr hbase, ip.congr hphase, ?_⟩
  calc
    (∫ x, R x ∂dV) = ∫ x, ∑ k, ρ k x * R x ∂dV := (integral_congr_ae hbase).symm
    _ = ∑ k, ∫ x, ρ k x * R x ∂dV := integral_finset_sum _ (fun i _ => (hpart i).1)
    _ = ∑ k, ∫ p, ρ k (π p) * G p ∂μ := Finset.sum_congr rfl (fun k _ => (hpart k).2.2)
    _ = ∫ p, ∑ k, ρ k (π p) * G p ∂μ :=
      (integral_finset_sum _ (fun i _ => (hpart i).2.1)).symm
    _ = ∫ p, G p ∂μ := integral_congr_ae hphase

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [MeasurableSpace M]

/-- Finite subordinate cutoffs turn two restricted integral identities on open sets into
one equality for the whole compactly supported test. The second integrand is supported over
the base compactum; its support in the phase space need not be compact. -/
theorem integral_eq_of_compact_base_local_tests {ι P : Type*} [MeasurableSpace P]
    (π : P → M) (dV : Measure M) (μ : Measure P) (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    {K : Set M} (hK : IsCompact K) (hcover : K ⊆ ⋃ i, U i)
    (R : M → ℝ) (G : P → ℝ) (hR : ∀ᵐ x ∂dV, x ∉ K → R x = 0)
    (hG : ∀ᵐ p ∂μ, π p ∉ K → G p = 0)
    (htest : ∀ i (φ : M → ℝ), ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U i →
      IntegrableOn (fun x => φ x * R x) (U i) dV ∧
      IntegrableOn (fun p => φ (π p) * G p) (π ⁻¹' U i) μ ∧
      (∫ x in U i, φ x * R x ∂dV) = ∫ p in π ⁻¹' U i, φ (π p) * G p ∂μ) :
    Integrable R dV ∧ Integrable G μ ∧ (∫ x, R x ∂dV) = ∫ p, G p ∂μ := by
  obtain ⟨n, idx, ρ, V, _, hKV, hρ, hsum⟩ :=
    exists_finite_smooth_cutoffs_on_compact U hU hK hcover
  apply integral_eq_of_finite_projected_parts π dV μ R G hR hG ρ (fun x hx => hsum x (hKV hx))
  intro k
  obtain ⟨hs, hc, hsub, _⟩ := hρ k
  obtain ⟨hL, hP, heq⟩ := htest (idx k) (ρ k) hs hc hsub
  have hz (x : M) (hx : x ∉ U (idx k)) : ρ k x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsub hx'))
  have hb (x : M) (hx : x ∉ U (idx k)) : ρ k x * R x = 0 := by rw [hz x hx, zero_mul]
  have hp (p : P) (h : p ∉ π ⁻¹' U (idx k)) : ρ k (π p) * G p = 0 := by
    rw [hz (π p) h, zero_mul]
  exact ⟨hL.integrable_of_forall_notMem_eq_zero hb, hP.integrable_of_forall_notMem_eq_zero hp,
    (setIntegral_eq_integral_of_forall_compl_eq_zero hb).symm.trans
      (heq.trans (setIntegral_eq_integral_of_forall_compl_eq_zero hp))⟩

/-- Assembly on the actual cotangent bundle, for open windows inside preferred chart sources.
Both the base and phase restrictions use the same window and their actual base projection. -/
theorem cotangent_integral_eq_of_preferredChart_tests [MeasurableSpace (CotangentBundle M)]
    {ι : Type*} (center : ι → M) (O : ι → Set M) (hO : ∀ i, IsOpen (O i))
    {K : Set M} (hK : IsCompact K)
    (hcover : K ⊆ ⋃ i, (chartAt CoordinateSpace (center i)).source ∩ O i)
    (dV : Measure M) (μ : Measure (CotangentBundle M))
    (R : M → ℝ) (G : CotangentBundle M → ℝ)
    (hR : ∀ᵐ x ∂dV, x ∉ K → R x = 0) (hG : ∀ᵐ p ∂μ, p.proj ∉ K → G p = 0)
    (htest : ∀ i (φ : M → ℝ), let U := (chartAt CoordinateSpace (center i)).source ∩ O i
      ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      IntegrableOn (fun x => φ x * R x) U dV ∧
      IntegrableOn (fun p : CotangentBundle M => φ p.proj * G p)
        ((fun p : CotangentBundle M => p.proj) ⁻¹' U) μ ∧
      (∫ x in U, φ x * R x ∂dV) =
        ∫ p in (fun p : CotangentBundle M => p.proj) ⁻¹' U, φ p.proj * G p ∂μ) :
    Integrable R dV ∧ Integrable G μ ∧ (∫ x, R x ∂dV) = ∫ p, G p ∂μ :=
  integral_eq_of_compact_base_local_tests (fun p : CotangentBundle M => p.proj) dV μ
    (fun i => (chartAt CoordinateSpace (center i)).source ∩ O i)
    (fun i => (chartAt CoordinateSpace (center i)).open_source.inter (hO i))
    hK hcover R G hR hG htest

end Burnett.Geometry.CotangentTests
