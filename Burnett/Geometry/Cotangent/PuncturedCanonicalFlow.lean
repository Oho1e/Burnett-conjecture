import Burnett.Geometry.Cotangent.SmoothCanonicalLocalFlow

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 3800

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter
open scoped ContDiff Topology Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonCrossingEnergy

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

private theorem exists_maximal_punctured_phaseTrajectory (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (q : CotangentBundle M) (hq : q ∈ puncturedCotangent) :
    ∃ A : CanonicalTrajectory g q, ∀ B : CanonicalTrajectory g q,
      B.domain ⊆ A.domain ∧ EqOn A.curve B.curve B.domain := by
  obtain ⟨_, _, _, _, _, hUq, _, _, _, hTraj⟩ := exists_smooth_canonicalHamilton_localFlow g hg hn hs q hq
  obtain ⟨A, _, _⟩ := hTraj q hUq
  exact exists_maximal_canonicalTrajectory g hg hn hs q A

/-- The actual maximal trajectory chosen at any punctured initial phase. -/
def maximalPuncturedTrajectory (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (q : CotangentBundle M)
    (hq : q ∈ puncturedCotangent) : CanonicalTrajectory g q :=
  Classical.choose (exists_maximal_punctured_phaseTrajectory g hg hn hs q hq)

theorem maximalPuncturedTrajectory_spec (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (q : CotangentBundle M)
    (hq : q ∈ puncturedCotangent) (B : CanonicalTrajectory g q) :
    let A := maximalPuncturedTrajectory g hg hn hs q hq
    B.domain ⊆ A.domain ∧ EqOn A.curve B.curve B.domain :=
  Classical.choose_spec (exists_maximal_punctured_phaseTrajectory g hg hn hs q hq) B

/-- The set of actual phase and time pairs on punctured canonical orbits. -/
def maximalPuncturedFlowDomain (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) : Set (CotangentBundle M × ℝ) :=
  {qt | ∃ hq : qt.1 ∈ puncturedCotangent, qt.2 ∈ (maximalPuncturedTrajectory g hg hn hs qt.1 hq).domain}

/-- Evaluation of the maximal actual phase map, considered on its domain. -/
def maximalPuncturedFlow (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (qt : CotangentBundle M × ℝ) : CotangentBundle M := by
  classical
  exact if hq : qt.1 ∈ puncturedCotangent then
    (maximalPuncturedTrajectory g hg hn hs qt.1 hq).curve qt.2 else qt.1

theorem maximalPuncturedFlow_eq_curve (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (q : CotangentBundle M)
    (hq : q ∈ puncturedCotangent) (t : ℝ) :
    maximalPuncturedFlow g hg hn hs (q, t) = (maximalPuncturedTrajectory g hg hn hs q hq).curve t := by
  classical
  exact dif_pos hq

/-- Recentering a true maximal orbit agrees with the selected maximal orbit
through its actual intermediate phase, with the translated domain included. -/
theorem maximalPuncturedFlow_restart (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (q : CotangentBundle M) (b s : ℝ)
    (hb : (q, b) ∈ maximalPuncturedFlowDomain g hg hn hs)
    (hs' : (maximalPuncturedFlow g hg hn hs (q, b), s) ∈ maximalPuncturedFlowDomain g hg hn hs) :
    (q, s + b) ∈ maximalPuncturedFlowDomain g hg hn hs ∧
      maximalPuncturedFlow g hg hn hs (q, s + b) =
        maximalPuncturedFlow g hg hn hs (maximalPuncturedFlow g hg hn hs (q, b), s) := by
  obtain ⟨hq, hb⟩ := hb
  let A := maximalPuncturedTrajectory g hg hn hs q hq
  have hf : maximalPuncturedFlow g hg hn hs (q, b) = A.curve b :=
    maximalPuncturedFlow_eq_curve g hg hn hs q hq b
  rw [hf] at hs' ⊢
  obtain ⟨hp, ht⟩ := hs'
  let B := maximalPuncturedTrajectory g hg hn hs (A.curve b) hp
  let C := CanonicalTrajectory.shift g hg hn hs A b hb
  have hC : s ∈ C.domain := shift_domain_maximal g hg hn hs A
    (fun D => (maximalPuncturedTrajectory_spec g hg hn hs q hq D).1) b hb B ht
  have hEq := canonicalCurve_eqOn_overlap g hg hn hs C.curve B.curve C.domain B.domain
    C.domain_open B.domain_open C.domain_interval B.domain_interval C.integral B.integral
    0 C.zero_mem B.zero_mem (C.initial.trans B.initial.symm) ⟨hC, ht⟩
  refine ⟨⟨hq, hC⟩, ?_⟩
  rw [maximalPuncturedFlow_eq_curve g hg hn hs _ hq,
      maximalPuncturedFlow_eq_curve g hg hn hs _ hp]
  exact hEq

/-- The actual maximal flow agrees near zero with the jointly smooth local
canonical phase map, with actual domain membership throughout the neighborhood. -/
theorem eventually_maximalPuncturedFlow_smooth_initial (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (q : CotangentBundle M) (hq : q ∈ puncturedCotangent) :
    ∀ᶠ z in 𝓝 (q, (0 : ℝ)), z ∈ maximalPuncturedFlowDomain g hg hn hs ∧
      ContMDiffAt (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞
        (maximalPuncturedFlow g hg hn hs) z := by
  obtain ⟨U, δ, hδ, Φ, hU, hqU, hUp, hΦ, _, hTraj⟩ := exists_smooth_canonicalHamilton_localFlow g hg hn hs q hq
  let J : Set ℝ := Ioo (-δ) δ
  have hzJ : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hOpen : IsOpen (U ×ˢ J) := hU.prod isOpen_Ioo
  have hOn (z : CotangentBundle M × ℝ) (hz : z ∈ U ×ˢ J) :
      z ∈ maximalPuncturedFlowDomain g hg hn hs ∧ maximalPuncturedFlow g hg hn hs z = Φ z := by
    obtain ⟨A, hD, hA⟩ := hTraj z.1 hz.1
    have ht : z.2 ∈ A.domain := hD.symm ▸ hz.2
    have hp := hUp hz.1
    obtain ⟨hsub, hEq⟩ := maximalPuncturedTrajectory_spec g hg hn hs z.1 hp A
    refine ⟨⟨hp, hsub ht⟩, ?_⟩
    calc
      maximalPuncturedFlow g hg hn hs z = (maximalPuncturedTrajectory g hg hn hs z.1 hp).curve z.2 :=
        maximalPuncturedFlow_eq_curve g hg hn hs z.1 hp z.2
      _ = A.curve z.2 := hEq ht
      _ = Φ z := congrFun hA z.2
  filter_upwards [hOpen.mem_nhds (show (q, (0 : ℝ)) ∈ U ×ˢ J from ⟨hqU, hzJ⟩)] with z hz
  have hGerm : maximalPuncturedFlow g hg hn hs =ᶠ[𝓝 z] Φ := by
    filter_upwards [hOpen.mem_nhds hz] with r hr
    exact (hOn r hr).2
  exact ⟨(hOn z hz).1, (hΦ.contMDiffAt (hOpen.mem_nhds hz)).congr_of_eventuallyEq hGerm⟩

end Burnett.Geometry.CotangentHamiltonInitialFamily
