import Burnett.Geometry.Cotangent.CausalPulse.CanonicalFlowPulseSmooth
import Burnett.Geometry.Cotangent.CausalPulse.OrbitTimeStripWindow

set_option autoImplicit false
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonInitialFamily Burnett.Geometry.CotangentHamiltonCrossingEnergy

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- The continuous time function has full range and a consistent orientation
along every maximal null Hamilton orbit. -/
def HasCompleteNullTime (T : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) : Prop :=
  ∀ z : PuncturedNullCotangent g hn,
    let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
    let t := fun b => T (A.curve b).1
    (MonotoneOn t A.domain ∨ AntitoneOn t A.domain) ∧ SurjOn t A.domain univ

private theorem exists_timeStrip_endpoints (T : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hT : HasCompleteNullTime T g hg hn hs)
    (z : PuncturedNullCotangent g hn) :
    let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
    ∃ a b : ℝ, a ∈ A.domain ∧ b ∈ A.domain ∧ a ≤ b ∧
      ((T (A.curve a).1 < -1 ∧ 1 < T (A.curve b).1) ∨
        (1 < T (A.curve a).1 ∧ T (A.curve b).1 < -1)) := by
  intro A
  have hSurj := (hT z).2
  obtain ⟨a, ha, hLow⟩ := hSurj (mem_univ (-2 : ℝ))
  obtain ⟨b, hb, hHigh⟩ := hSurj (mem_univ (2 : ℝ))
  change T (A.curve a).1 = -2 at hLow
  change T (A.curve b).1 = 2 at hHigh
  rcases le_total a b with hab | hba
  · exact ⟨a, b, ha, hb, hab, Or.inl ⟨by rw [hLow]; norm_num, by rw [hHigh]; norm_num⟩⟩
  · exact ⟨b, a, hb, ha, hba, Or.inr ⟨by rw [hHigh]; norm_num, by rw [hLow]; norm_num⟩⟩

theorem canonicalPulseMass_pos_of_completeNullTime (T f : M → ℝ) (hf : Continuous f)
    (hNonneg : ∀ x, 0 ≤ f x) (hSupport : Function.support f = T ⁻¹' Ioo (-1) 1)
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hT : HasCompleteNullTime T g hg hn hs) (z : PuncturedNullCotangent g hn) :
    0 < canonicalPulseMass f g hg hn hs z := by
  let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
  let γ := fun t => (A.curve t).1
  obtain ⟨a, b, ha, hb, hab, hEnds⟩ := exists_timeStrip_endpoints T g hg hn hs hT z
  have hwin : Icc a b ⊆ A.domain := A.domain_interval.out ha hb
  have hOutside := timeStripPulse_zero_outside_window T f γ (by norm_num : (-1 : ℝ) < 1)
    hSupport ha hb hab (hT z).1 hEnds
  obtain ⟨t, ht, hZero⟩ := (hT z).2 (mem_univ (0 : ℝ))
  have hPos : f (γ t) ≠ 0 := by
    change γ t ∈ Function.support f
    rw [hSupport]
    change T (γ t) ∈ Ioo (-1 : ℝ) 1
    rw [show T (γ t) = 0 from hZero]
    norm_num
  have hIn : t ∈ Icc a b := by
    by_contra h
    exact hPos (hOutside t ht h)
  have hγ : ContinuousOn γ A.domain := continuous_cotangent_projection.comp_continuousOn A.integral.continuousOn
  exact (pulseIntegral_pos_of_parameters f hf hNonneg γ A.domain_open hγ hwin hIn hPos hOutside).2.2

private theorem pulseTimeEndpoint_continuousAt (T : M → ℝ) (hT : Continuous T)
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} {t : ℝ} (ht : (p, t) ∈ maximalPuncturedFlowDomain g hg hn hs) :
    ContinuousAt (fun q => T ((maximalPuncturedFlow g hg hn hs (q, t)).1)) p := by
  have hSmooth := maximalPuncturedFlow_jointSmooth g hg hn hs
  have hInit : ContinuousAt (fun q : CotangentBundle M => (q, t)) p :=
    continuousAt_id.prodMk continuousAt_const
  have hFlow : ContinuousAt (fun q : CotangentBundle M =>
      maximalPuncturedFlow g hg hn hs (q, t)) p :=
    ContinuousAt.comp' (f := fun q : CotangentBundle M => (q, t))
      (hSmooth.2.contMDiffAt (hSmooth.1.mem_nhds ht)).continuousAt hInit
  exact hT.continuousAt.comp (continuous_cotangent_projection.continuousAt.comp hFlow)

/-- The true orbit pulse near a null phase can be read on a fixed compact
affine interval, with the same phase flow on the ambient cotangent bundle. -/
theorem exists_smooth_canonicalPulseMass_germ (T f : M → ℝ) (hTc : Continuous T)
    (hf : ContMDiff Model 𝓘(ℝ) ∞ f) (hSupport : Function.support f = T ⁻¹' Ioo (-1) 1)
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hT : HasCompleteNullTime T g hg hn hs) (z : PuncturedNullCotangent g hn) :
    ∃ E : CotangentBundle M → ℝ, ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E z.val ∧
      ∀ᶠ q in 𝓝 z.val, ∀ (hq : q ∈ puncturedCotangent) (h0 : dualEnergy g hn q = 0),
        E q = canonicalPulseMass f g hg hn hs ⟨q, hq, h0⟩ := by
  let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
  let F := maximalPuncturedFlow g hg hn hs
  let D := maximalPuncturedFlowDomain g hg hn hs
  obtain ⟨a, b, ha, hb, hab, hEnds⟩ := exists_timeStrip_endpoints T g hg hn hs hT z
  have hDom : ∀ t ∈ Icc a b, (z.val, t) ∈ D := fun t ht => ⟨z.property.1, A.domain_interval.out ha hb ht⟩
  let J := fixedTimePulse f g hg hn hs (Icc a b)
  refine ⟨J, contMDiffAt_fixedTimePulse f hf g hg hn hs _ isCompact_Icc z.val hDom, ?_⟩
  have hD := (maximalPuncturedFlow_jointSmooth g hg hn hs).1
  have hDa : (z.val, a) ∈ D := ⟨z.property.1, ha⟩
  have hDb : (z.val, b) ∈ D := ⟨z.property.1, hb⟩
  have hDaNear : ∀ᶠ q in 𝓝 z.val, (q, a) ∈ D :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hD.mem_nhds hDa)
  have hDbNear : ∀ᶠ q in 𝓝 z.val, (q, b) ∈ D :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hD.mem_nhds hDb)
  let L (q : CotangentBundle M) := T (F (q, a)).1
  let R (q : CotangentBundle M) := T (F (q, b)).1
  have hL : ContinuousAt L z.val := pulseTimeEndpoint_continuousAt T hTc g hg hn hs hDa
  have hR : ContinuousAt R z.val := pulseTimeEndpoint_continuousAt T hTc g hg hn hs hDb
  have hEnds0 : (L z.val < -1 ∧ 1 < R z.val) ∨ (1 < L z.val ∧ R z.val < -1) := by
    dsimp only [L, R, F]
    rw [maximalPuncturedFlow_eq_curve g hg hn hs z.val z.property.1 a,
      maximalPuncturedFlow_eq_curve g hg hn hs z.val z.property.1 b]
    exact hEnds
  have hEndsNear : ∀ᶠ q in 𝓝 z.val, (L q < -1 ∧ 1 < R q) ∨ (1 < L q ∧ R q < -1) := by
    rcases hEnds0 with ⟨hLa, hRb⟩ | ⟨hLa, hRb⟩
    · filter_upwards [hL.preimage_mem_nhds (Iio_mem_nhds hLa), hR.preimage_mem_nhds (Ioi_mem_nhds hRb)] with q hq hq'
      exact Or.inl ⟨hq, hq'⟩
    · filter_upwards [hL.preimage_mem_nhds (Ioi_mem_nhds hLa), hR.preimage_mem_nhds (Iio_mem_nhds hRb)] with q hq hq'
      exact Or.inr ⟨hq, hq'⟩
  filter_upwards [hDaNear, hDbNear, hEndsNear] with q hqa hqb he hq h0
  let q₀ : PuncturedNullCotangent g hn := ⟨q, hq, h0⟩
  let B := maximalPuncturedTrajectory g hg hn hs q hq
  let γ := fun t => (B.curve t).1
  have ha' : a ∈ B.domain := by obtain ⟨_, ht⟩ := hqa; exact ht
  have hb' : b ∈ B.domain := by obtain ⟨_, ht⟩ := hqb; exact ht
  have hF (t : ℝ) : (F (q, t)).1 = γ t :=
    congrArg (fun p : CotangentBundle M => p.1) (maximalPuncturedFlow_eq_curve g hg hn hs q hq t)
  change (T (F (q, a)).1 < -1 ∧ 1 < T (F (q, b)).1) ∨
    (1 < T (F (q, a)).1 ∧ T (F (q, b)).1 < -1) at he
  rw [hF a, hF b] at he
  have hOutside := timeStripPulse_zero_outside_window T f γ (by norm_num : (-1 : ℝ) < 1)
    hSupport ha' hb' hab (hT q₀).1 he
  change (∫ t in Icc a b, f ((F (q, t)).1)) = pulseIntegral f γ B.domain
  simp_rw [hF]
  exact (pulseIntegral_eq_integral_window f γ (B.domain_interval.out ha' hb') hOutside).symm

end Burnett.Geometry.CausalOrbitPulse
