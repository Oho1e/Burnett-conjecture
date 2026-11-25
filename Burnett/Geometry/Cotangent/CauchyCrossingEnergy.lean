import Burnett.Geometry.Cotangent.NullTrajectoryContinuation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.CotangentHamiltonCauchySlice

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The intrinsic base velocity is the actual derivative of the cotangent
projection applied to the true canonical tangent vector. -/
def canonicalBaseVelocity (g : Field (M := M)) (p : CotangentBundle M) :
    TangentSpace Model p.1 :=
  mfderiv CotangentModelWithCorners Model (fun q : CotangentBundle M => q.1) p (canonicalHamilton g p)

theorem canonicalBaseVelocity_eq_projectedHamilton (g : Field (M := M))
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hc : p ∈ cotangentSource c) :
    canonicalBaseVelocity g p = projectedHamilton g c p := by
  rw [canonicalBaseVelocity, canonicalHamilton,
    intrinsicHamilton_projection g p.1 p (mem_chart_source CoordinateSpace _)]
  exact projectedHamilton_chart_independent g hn hs p.1 c p (mem_chart_source CoordinateSpace _) hc

/-- The projected base curve of the given trajectory has the intrinsic Hamilton base velocity
in the original affine parameter. -/
theorem canonicalTrajectory_hasMFDerivAt_base (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (t : ℝ) (ht : t ∈ A.domain) :
    HasMFDerivAt 𝓘(ℝ) Model (fun s => (A.curve s).1) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (canonicalBaseVelocity g (A.curve t))) := by
  let c := (A.curve t).1
  have hc : A.curve t ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨J, hJ, htJ, _, hJcurve⟩ :=
    canonicalCurve_chart_near g hg hn hs c A.curve A.domain A.domain_open A.integral t ht hc
  rw [canonicalBaseVelocity_eq_projectedHamilton g hn hs c (A.curve t) hc]
  exact hamiltonCurve_projected_derivative g c A.curve J hJ hJcurve t htJ

theorem canonicalBaseVelocity_nonzero_null (g : Field (M := M))
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0) :
    canonicalBaseVelocity g p ≠ 0 ∧ g p.1 (canonicalBaseVelocity g p) (canonicalBaseVelocity g p) = 0 := by
  have hc : p ∈ cotangentSource p.1 := mem_chart_source CoordinateSpace _
  rw [canonicalBaseVelocity_eq_projectedHamilton g hn hs p.1 p hc]
  exact ⟨projectedHamilton_ne_zero g hn hs p.1 p hc hp,
    (projectedHamilton_self g hn hs p.1 p hc).trans hnull⟩

/-- Intrinsic regular causal paths. Orientation of the parameter is immaterial to the
symmetric crossing property. These paths have nonzero causal velocities at every time. -/
def RegularCausalOn (g : Field (M := M)) (γ : ℝ → M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∃ v : TangentSpace Model (γ t),
    HasMFDerivAt 𝓘(ℝ) Model γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
    v ≠ 0 ∧ g (γ t) v v ≤ 0

theorem canonicalTrajectory_regularCausalOn_base [T2Space M] (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0) :
    RegularCausalOn g (fun t => (A.curve t).1) A.domain := by
  intro t ht
  have hp' := A.punctured g hg hn hs hp ht
  have hnull' := (A.dualEnergy_constant g hg hn hs ht).trans hnull
  obtain ⟨hne, hzero⟩ := canonicalBaseVelocity_nonzero_null g hn hs (A.curve t) hp' hnull'
  exact ⟨canonicalBaseVelocity g (A.curve t), canonicalTrajectory_hasMFDerivAt_base g hg hn hs A t ht,
    hne, hzero.le⟩

end Burnett.Geometry.CotangentHamiltonCauchySlice

namespace Burnett.Geometry.CotangentHamiltonCauchySlice

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- A local intrinsic defining map of an actual smooth spacelike slice.
The tangent hyperplane is the kernel of the genuine manifold differential. -/
structure SmoothSpacelikeDefiningMapAt (g : Field (M := M)) (S : Set M) (m : M) (f : M → ℝ) : Prop where
  localModel : ∃ U : Set M, IsOpen U ∧ m ∈ U ∧ ContMDiffOn Model 𝓘(ℝ) ∞ f U ∧
    ∀ y ∈ U, y ∈ S ↔ f y = 0
  regular : Function.Surjective (mfderiv Model 𝓘(ℝ) f m)
  spacelike : SpacelikeLevelAt g f m

def SmoothSpacelikeSlice (g : Field (M := M)) (S : Set M) : Prop :=
  ∀ m ∈ S, ∃ f : M → ℝ, SmoothSpacelikeDefiningMapAt g S m f

/-- At an actual hit of a smooth spacelike defining level, the derivative of
the defining function along the original null trajectory is nonzero.
Every atlas chart containing the point computes the same base velocity. -/
theorem canonicalTrajectory_spacelike_hit_transverse [T2Space M]
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (S : Set M) (t : ℝ) (ht : t ∈ A.domain) (hhit : (A.curve t).1 ∈ S)
    (f : M → ℝ) (hf : SmoothSpacelikeDefiningMapAt g S (A.curve t).1 f) :
    let d : ℝ := mfderiv Model 𝓘(ℝ) f (A.curve t).1 (canonicalBaseVelocity g (A.curve t))
    f (A.curve t).1 = 0 ∧ HasDerivAt (fun s => f (A.curve s).1) d t ∧ d ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] t, (A.curve s).1 ∉ S := by
  intro d
  let c := (A.curve t).1
  have hc : A.curve t ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨U, hU, htU, hfU, hlevel⟩ := hf.localModel
  have hfAt : ContMDiffAt Model 𝓘(ℝ) ∞ f (A.curve t).1 := hfU.contMDiffAt (hU.mem_nhds htU)
  have hevent : ∀ᶠ y in 𝓝 (A.curve t).1, y ∈ S ↔ f y = 0 := by
    filter_upwards [hU.mem_nhds htU] with y hy
    exact hlevel y hy
  obtain ⟨J, hJ, htJ, _, hJcurve⟩ :=
    canonicalCurve_chart_near g hg hn hs c A.curve A.domain A.domain_open A.integral t ht hc
  have hd : HasDerivAt (fun s => f (A.curve s).1) d t := by
    change HasDerivAt (fun s => f (A.curve s).1)
      (mfderiv Model 𝓘(ℝ) f (A.curve t).1 (canonicalBaseVelocity g (A.curve t))) t
    rw [canonicalBaseVelocity_eq_projectedHamilton g hn hs c (A.curve t) hc]
    exact hamiltonCurve_level_derivative g c A.curve J hJ hJcurve t htJ f
      (hfAt.mdifferentiableAt (by simp))
  have hne : d ≠ 0 := by
    change mfderiv Model 𝓘(ℝ) f (A.curve t).1 (canonicalBaseVelocity g (A.curve t)) ≠ 0
    rw [canonicalBaseVelocity_eq_projectedHamilton g hn hs c (A.curve t) hc]
    exact projectedHamilton_transverse g hn hs c (A.curve t) hc (A.punctured g hg hn hs hp ht)
      ((A.dualEnergy_constant g hg hn hs ht).trans hnull) f hf.spacelike
  have hzero : f (A.curve t).1 = 0 := (hlevel _ htU).mp hhit
  have hcontinuous : ContinuousAt (fun s => (A.curve s).1) t :=
    (canonicalTrajectory_hasMFDerivAt_base g hg hn hs A t ht).continuousAt
  have hloc : ∀ᶠ s in 𝓝 t, (A.curve s).1 ∈ S ↔ f (A.curve s).1 = 0 :=
    hcontinuous.tendsto.eventually hevent
  refine ⟨hzero, hd, hne, ?_⟩
  filter_upwards [hloc.filter_mono nhdsWithin_le_nhds, hd.eventually_ne hne] with s hs hd'
  intro hhit'
  exact hd' ((hs.mp hhit').trans hzero.symm)

end Burnett.Geometry.CotangentHamiltonCauchySlice

namespace Burnett.Geometry.CotangentHamiltonCauchySlice

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonMaximalCurve Burnett.Geometry.CotangentHamiltonAffineReparam

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The ambient Cauchy crossing law restricted to the regular causal paths needed here.
It requires a unique time of intersection for every such inextendible path. -/
def RegularCauchySliceProperty (g : Field (M := M)) (S : Set M) : Prop :=
  ∀ (γ : ℝ → M) (I : Set ℝ), IsOpen I → I.OrdConnected → I.Nonempty →
    RegularCausalOn g γ I → (¬ HasIncreasingContinuousExtension γ I) →
      ∃! t : ℝ, t ∈ I ∧ γ t ∈ S

variable [T2Space M]

/-- The unique orbit crossing follows from the crossing law on manifold causal curves,
with actual causality and inextendibility proved for this same trajectory. -/
theorem maximal_null_orbit_unique_cauchy_crossing (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain)
    (S : Set M) (hC : RegularCauchySliceProperty g S) :
    UniqueCrossing S A.domain A.curve :=
  hC (fun t => (A.curve t).1) A.domain A.domain_open A.domain_interval ⟨0, A.zero_mem⟩
    (canonicalTrajectory_regularCausalOn_base g hg hn hs A hp hnull)
    (maximal_null_base_no_increasing_continuous_extension g hg hn hs hL A hp hnull hmax)

/-- Given an actual smooth spacelike slice with the ambient Cauchy crossing law,
one genuine maximal null orbit through the initial phase point crosses it once and transversely. -/
theorem exists_maximal_null_orbit_unique_transverse_crossing (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g)
    (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (hS : SmoothSpacelikeSlice g S) :
    ∃ A : CanonicalTrajectory g p,
      (∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain ∧ EqOn A.curve D.curve D.domain) ∧
      ∃ t : ℝ, t ∈ A.domain ∧ (A.curve t).1 ∈ S ∧
        (∀ s ∈ A.domain, (A.curve s).1 ∈ S → s = t) ∧
        ∃ f : M → ℝ, SmoothSpacelikeDefiningMapAt g S (A.curve t).1 f ∧
          f (A.curve t).1 = 0 ∧
          let d : ℝ := mfderiv Model 𝓘(ℝ) f (A.curve t).1 (canonicalBaseVelocity g (A.curve t))
          HasDerivAt (fun s => f (A.curve s).1) d t ∧ d ≠ 0 := by
  obtain ⟨A, hmax, _⟩ := exists_maximal_null_canonicalTrajectory g hg hn hs p hp hnull
  have hcross := maximal_null_orbit_unique_cauchy_crossing g hg hn hs hL A hp hnull
    (fun D => (hmax D).1) S hC
  obtain ⟨t, ⟨ht, hhit⟩, huniq⟩ := hcross
  obtain ⟨f, hf⟩ := hS (A.curve t).1 hhit
  obtain ⟨hzero, hd, hne, _⟩ :=
    canonicalTrajectory_spacelike_hit_transverse g hg hn hs A hp hnull S t ht hhit f hf
  exact ⟨A, hmax, t, ht, hhit, fun s hs' hhit' => huniq s ⟨hs', hhit'⟩,
    f, hf, hzero, hd, hne⟩

end Burnett.Geometry.CotangentHamiltonCauchySlice

namespace Burnett.Geometry.CotangentHamiltonCrossingEnergy

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonTimeReversal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- Translation of the parameter preserves the true canonical manifold integral curve. -/
theorem canonicalIntegralCurve_shifted (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I) (b : ℝ) :
    IsMIntegralCurveOn (I := CotangentModelWithCorners) (shiftedCurve b γ) (canonicalHamilton g)
      (shiftedDomain b I) := by
  intro t ht
  let c := (γ (t + b)).1
  have hc : γ (t + b) ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨J, hJ, htJ, _, hchart⟩ :=
    canonicalCurve_chart_near g hg hn hs c γ I hI hγ (t + b) ht hc
  have hJo : IsOpen (shiftedDomain b J) := hJ.preimage (continuous_id.add continuous_const)
  have hS := shiftedCurve_hamilton g c γ J hchart b
  have hderiv := ((hamiltonCurve_actual_integralOn g c (shiftedCurve b γ) (shiftedDomain b J)
    hJo hS) t htJ).hasMFDerivAt (hJo.mem_nhds htJ)
  let q := shiftedCurve b γ t
  have he : intrinsicHamilton g c q = canonicalHamilton g q :=
    intrinsicHamilton_chart_independent_all g hg hn hs c q.1 q
      (hS.1 t htJ) (mem_chart_source CoordinateSpace _)
  change HasMFDerivAt 𝓘(ℝ) CotangentModelWithCorners (shiftedCurve b γ) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (intrinsicHamilton g c q)) at hderiv
  rw [he] at hderiv
  exact hderiv.hasMFDerivWithinAt

/-- Recenter a true trajectory at one of its actual times. -/
def CanonicalTrajectory.shift (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (b : ℝ) (hb : b ∈ A.domain) :
    CanonicalTrajectory g (A.curve b) where
  domain := shiftedDomain b A.domain
  curve := shiftedCurve b A.curve
  domain_open := A.domain_open.preimage (continuous_id.add continuous_const)
  domain_interval := by
    refine ⟨fun t ht u hu s hsu => ?_⟩
    change s + b ∈ A.domain
    exact A.domain_interval.out ht hu ⟨add_le_add_right hsu.1 b, add_le_add_right hsu.2 b⟩
  zero_mem := by
    change 0 + b ∈ A.domain
    simpa only [zero_add] using hb
  initial := by simp only [shiftedCurve, zero_add]
  integral := canonicalIntegralCurve_shifted g hg hn hs A.curve A.domain A.domain_open A.integral b

/-- Recentering at an actual time keeps the full maximal interval in the translated parameter. -/
theorem shift_domain_maximal [T2Space M] (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain)
    (b : ℝ) (hb : b ∈ A.domain) (D : CanonicalTrajectory g (A.curve b)) :
    D.domain ⊆ (CanonicalTrajectory.shift g hg hn hs A b hb).domain := by
  let A₀ := CanonicalTrajectory.shift g hg hn hs A b hb
  obtain ⟨B, hB⟩ := exists_maximal_canonicalTrajectory g hg hn hs (A.curve b) A₀
  have hneg : -b ∈ A₀.domain := by
    change -b + b ∈ A.domain
    simpa only [neg_add_cancel] using A.zero_mem
  have hnegB := (hB A₀).1 hneg
  have hnow : B.curve (-b) = p := by
    calc
      B.curve (-b) = A₀.curve (-b) := (hB A₀).2 hneg
      _ = p := by
        change A.curve (-b + b) = p
        simpa only [neg_add_cancel] using A.initial
  let C₀ := CanonicalTrajectory.shift g hg hn hs B (-b) hnegB
  let C : CanonicalTrajectory g p :=
    ⟨C₀.domain, C₀.curve, C₀.domain_open, C₀.domain_interval, C₀.zero_mem,
      C₀.initial.trans hnow, C₀.integral⟩
  intro t ht
  change t + b ∈ A.domain
  apply hmax C
  change t + b + -b ∈ B.domain
  simpa only [add_assoc, add_neg_cancel, add_zero] using (hB D).1 ht

/-- Simultaneous positive fiber and affine time scaling of a true trajectory. -/
def CanonicalTrajectory.positiveScale (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (a : ℝ) (ha : 0 < a) :
    CanonicalTrajectory g (cotangentScale a p) where
  domain := scaledDomain a A.domain
  curve := scaledCurve a A.curve
  domain_open := A.domain_open.preimage (continuous_const.mul continuous_id)
  domain_interval := by
    refine ⟨fun t ht u hu s hsu => ?_⟩
    change a * s ∈ A.domain
    exact A.domain_interval.out ht hu
      ⟨mul_le_mul_of_nonneg_left hsu.1 ha.le, mul_le_mul_of_nonneg_left hsu.2 ha.le⟩
  zero_mem := by
    change a * 0 ∈ A.domain
    simpa only [mul_zero] using A.zero_mem
  initial := (scaledCurve_initial a A.curve).trans (congrArg (cotangentScale a) A.initial)
  integral := canonicalIntegralCurve_scaled_of_ne_zero g hg hn hs A.curve A.domain A.domain_open
    A.integral ha.ne'

/-- A positive fiber scale and the associated time scale preserve maximality of the true orbit. -/
theorem positiveScale_domain_maximal (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain)
    (a : ℝ) (ha : 0 < a) (D : CanonicalTrajectory g (cotangentScale a p)) :
    D.domain ⊆ (CanonicalTrajectory.positiveScale g hg hn hs A a ha).domain := by
  let D₀ := CanonicalTrajectory.positiveScale g hg hn hs D a⁻¹ (inv_pos.mpr ha)
  have hcancel : cotangentScale a⁻¹ (cotangentScale a p) = p := by
    rw [cotangentScale_mul, inv_mul_cancel₀ ha.ne', cotangentScale_one]
  let E : CanonicalTrajectory g p :=
    ⟨D₀.domain, D₀.curve, D₀.domain_open, D₀.domain_interval, D₀.zero_mem,
      D₀.initial.trans hcancel, D₀.integral⟩
  intro t ht
  change a * t ∈ A.domain
  apply hmax E
  change a⁻¹ * (a * t) ∈ D.domain
  simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using ht

end Burnett.Geometry.CotangentHamiltonCrossingEnergy

namespace Burnett.Geometry.CotangentHamiltonCrossingEnergy

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonCauchySlice

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- The full actual punctured null cotangent bundle for the original quadratic energy. -/
abbrev PuncturedNullCotangent (g : Field (M := M)) (hn : IsNondegenerate g) :=
  {p : CotangentBundle M // p ∈ puncturedCotangent ∧ dualEnergy g hn p = 0}

private noncomputable def chosenMaximalNullTrajectory (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn) :
    CanonicalTrajectory g z.val :=
  Classical.choose (exists_maximal_null_canonicalTrajectory g hg hn hs z.val z.property.1 z.property.2)

private theorem chosenMaximalNullTrajectory_spec (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn) :
    let A := chosenMaximalNullTrajectory g hg hn hs z
    (∀ D : CanonicalTrajectory g z.val, D.domain ⊆ A.domain ∧ EqOn A.curve D.curve D.domain) ∧
    ∀ t ∈ A.domain, A.curve t ∈ puncturedCotangent ∧ dualEnergy g hn (A.curve t) = 0 :=
  Classical.choose_spec (exists_maximal_null_canonicalTrajectory g hg hn hs z.val z.property.1 z.property.2)

private theorem chosenMaximalNullTrajectory_uniqueCrossing (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (z : PuncturedNullCotangent g hn) :
    let A := chosenMaximalNullTrajectory g hg hn hs z
    UniqueCrossing S A.domain A.curve :=
  maximal_null_orbit_unique_cauchy_crossing g hg hn hs hL
    (chosenMaximalNullTrajectory g hg hn hs z) z.property.1 z.property.2
    (fun D => ((chosenMaximalNullTrajectory_spec g hg hn hs z).1 D).1) S hC

/-- The actual phase point at the unique Cauchy crossing of the maximal orbit from z. -/
noncomputable def globalCrossingPoint (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (z : PuncturedNullCotangent g hn) :
    CotangentBundle M :=
  let A := chosenMaximalNullTrajectory g hg hn hs z
  A.curve (crossingTime S A.domain A.curve
    (chosenMaximalNullTrajectory_uniqueCrossing g hg hn hs hL S hC z))

/-- Any actual trajectory through the same initial phase agrees with the global crossing point
when it hits the slice. -/
theorem globalCrossingPoint_eq_of_orbit_hit (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (z : PuncturedNullCotangent g hn)
    (A : CanonicalTrajectory g z.val) {t : ℝ} (ht : t ∈ A.domain) (hhit : (A.curve t).1 ∈ S) :
    globalCrossingPoint g hg hn hs hL S hC z = A.curve t := by
  let B := chosenMaximalNullTrajectory g hg hn hs z
  have hmax : A.domain ⊆ B.domain ∧ EqOn B.curve A.curve A.domain :=
    (chosenMaximalNullTrajectory_spec g hg hn hs z).1 A
  have hh : (B.curve t).1 ∈ S := by
    rw [hmax.2 ht]
    exact hhit
  let hUnique := chosenMaximalNullTrajectory_uniqueCrossing g hg hn hs hL S hC z
  have htime : t = crossingTime S B.domain B.curve hUnique :=
    crossingTime_unique S B.domain B.curve hUnique t ⟨hmax.1 ht, hh⟩
  change B.curve (crossingTime S B.domain B.curve hUnique) = A.curve t
  rw [← htime]
  exact hmax.2 ht

theorem globalCrossingPoint_spec (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (z : PuncturedNullCotangent g hn) :
    let q := globalCrossingPoint g hg hn hs hL S hC z
    q.1 ∈ S ∧ q ∈ puncturedCotangent ∧ dualEnergy g hn q = 0 := by
  let A := chosenMaximalNullTrajectory g hg hn hs z
  let hUnique := chosenMaximalNullTrajectory_uniqueCrossing g hg hn hs hL S hC z
  let t := crossingTime S A.domain A.curve hUnique
  have ht : t ∈ A.domain ∧ (A.curve t).1 ∈ S := crossingTime_spec S A.domain A.curve hUnique
  exact ⟨ht.2, (chosenMaximalNullTrajectory_spec g hg hn hs z).2 t ht.1⟩

/-- The norm at the actual unique crossing, defined throughout the full punctured null bundle. -/
noncomputable def globalCrossingEnergy (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (z : PuncturedNullCotangent g hn) : ℝ :=
  cotangentNorm r (globalCrossingPoint g hg hn hs hL S hC z)

theorem globalCrossingEnergy_pos (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (z : PuncturedNullCotangent g hn) :
    0 < globalCrossingEnergy r g hg hn hs hL S hC z :=
  cotangentNorm_pos r (globalCrossingPoint_spec g hg hn hs hL S hC z).2.1

theorem globalCrossingEnergy_eq_crossingEnergy (r : Metric (M := M))
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (z : PuncturedNullCotangent g hn) (A : CanonicalTrajectory g z.val)
    (hA : UniqueCrossing S A.domain A.curve) :
    globalCrossingEnergy r g hg hn hs hL S hC z = crossingEnergy r S A.domain A.curve hA := by
  let t := crossingTime S A.domain A.curve hA
  have ht : t ∈ A.domain ∧ (A.curve t).1 ∈ S := crossingTime_spec S A.domain A.curve hA
  change cotangentNorm r (globalCrossingPoint g hg hn hs hL S hC z) = cotangentNorm r (A.curve t)
  rw [globalCrossingPoint_eq_of_orbit_hit g hg hn hs hL S hC z A ht.1 ht.2]

end Burnett.Geometry.CotangentHamiltonCrossingEnergy

namespace Burnett.Geometry.CotangentHamiltonCrossingEnergy

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonCauchySlice

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- A true trajectory from a punctured null phase gives an actual punctured null phase
at each time of its domain. -/
def nullPhaseAt (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (z : PuncturedNullCotangent g hn) (A : CanonicalTrajectory g z.val)
    (b : ℝ) (hb : b ∈ A.domain) : PuncturedNullCotangent g hn :=
  ⟨A.curve b, A.punctured g hg hn hs z.property.1 hb,
    (A.dualEnergy_constant g hg hn hs hb).trans z.property.2⟩

/-- The positive fiber scaling on the actual punctured null cotangent bundle. -/
def positiveScaleNullPhase (g : Field (M := M)) (hn : IsNondegenerate g)
    (z : PuncturedNullCotangent g hn) (a : ℝ) (ha : 0 < a) : PuncturedNullCotangent g hn :=
  ⟨cotangentScale a z.val, smul_ne_zero ha.ne' z.property.1, by
    rw [dualEnergy_cotangentScale, z.property.2, mul_zero]⟩

/-- Crossing energy is invariant under recentering at any actual time of a true maximal orbit. -/
theorem globalCrossingEnergy_along_maximal (r : Metric (M := M))
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (z : PuncturedNullCotangent g hn) (A : CanonicalTrajectory g z.val)
    (hmax : ∀ D : CanonicalTrajectory g z.val, D.domain ⊆ A.domain)
    (b : ℝ) (hb : b ∈ A.domain) :
    globalCrossingEnergy r g hg hn hs hL S hC (nullPhaseAt g hg hn hs z A b hb) =
      globalCrossingEnergy r g hg hn hs hL S hC z := by
  let w := nullPhaseAt g hg hn hs z A b hb
  let B : CanonicalTrajectory g w.val := CanonicalTrajectory.shift g hg hn hs A b hb
  have hA := maximal_null_orbit_unique_cauchy_crossing g hg hn hs hL A z.property.1 z.property.2 hmax S hC
  have hB := maximal_null_orbit_unique_cauchy_crossing g hg hn hs hL B w.property.1 w.property.2
    (shift_domain_maximal g hg hn hs A hmax b hb) S hC
  calc
    globalCrossingEnergy r g hg hn hs hL S hC w = crossingEnergy r S B.domain B.curve hB :=
      globalCrossingEnergy_eq_crossingEnergy r g hg hn hs hL S hC w B hB
    _ = crossingEnergy r S A.domain A.curve hA := shifted_crossingEnergy r S A.domain A.curve hA b
    _ = globalCrossingEnergy r g hg hn hs hL S hC z :=
      (globalCrossingEnergy_eq_crossingEnergy r g hg hn hs hL S hC z A hA).symm

/-- Crossing energy has degree one under positive fiber scaling of the actual null bundle. -/
theorem globalCrossingEnergy_positiveScale (r : Metric (M := M))
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (z : PuncturedNullCotangent g hn) (a : ℝ) (ha : 0 < a) :
    globalCrossingEnergy r g hg hn hs hL S hC (positiveScaleNullPhase g hn z a ha) =
      a * globalCrossingEnergy r g hg hn hs hL S hC z := by
  let A := chosenMaximalNullTrajectory g hg hn hs z
  let hmax (D : CanonicalTrajectory g z.val) : D.domain ⊆ A.domain :=
    ((chosenMaximalNullTrajectory_spec g hg hn hs z).1 D).1
  let w := positiveScaleNullPhase g hn z a ha
  let B : CanonicalTrajectory g w.val := CanonicalTrajectory.positiveScale g hg hn hs A a ha
  have hA := chosenMaximalNullTrajectory_uniqueCrossing g hg hn hs hL S hC z
  have hB := maximal_null_orbit_unique_cauchy_crossing g hg hn hs hL B w.property.1 w.property.2
    (positiveScale_domain_maximal g hg hn hs A hmax a ha) S hC
  calc
    globalCrossingEnergy r g hg hn hs hL S hC w = crossingEnergy r S B.domain B.curve hB :=
      globalCrossingEnergy_eq_crossingEnergy r g hg hn hs hL S hC w B hB
    _ = a * crossingEnergy r S A.domain A.curve hA := scaled_crossingEnergy r S A.domain A.curve hA ha
    _ = a * globalCrossingEnergy r g hg hn hs hL S hC z := by
      rw [globalCrossingEnergy_eq_crossingEnergy r g hg hn hs hL S hC z A hA]

end Burnett.Geometry.CotangentHamiltonCrossingEnergy

namespace Burnett.Geometry.CotangentHamiltonSmoothCrossing

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A transverse scalar zero in a Banach parameter and real time gives a locally smooth
time function. This uses the smooth inverse theorem on the map (u,t) ↦ (u,F(u,t)). -/
theorem exists_smooth_time_of_transverse_zero
    (F : E × ℝ → ℝ) (u₀ : E) (t₀ d : ℝ)
    (hF : ContDiffAt ℝ ∞ F (u₀, t₀)) (hzero : F (u₀, t₀) = 0)
    (hT : HasDerivAt (fun t : ℝ => F (u₀, t)) d t₀) (hd : d ≠ 0) :
    ∃ τ : E → ℝ, τ u₀ = t₀ ∧ ContDiffAt ℝ ∞ τ u₀ ∧ ∀ᶠ u in 𝓝 u₀, F (u, τ u) = 0 := by
  let DF := fderiv ℝ F (u₀, t₀)
  have hDF : HasFDerivAt F DF (u₀, t₀) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => (u₀, t)) ((0 : E), (1 : ℝ)) t₀ :=
    (hasDerivAt_const t₀ u₀).prodMk (hasDerivAt_id t₀)
  have hDFtime : DF (0, 1) = d := (hDF.comp_hasDerivAt t₀ ht).unique hT
  have hDFvertical (t : ℝ) : DF (0, t) = t * d := by
    rw [show ((0 : E), t) = t • ((0 : E), (1 : ℝ)) by simp]
    rw [map_smul, hDFtime, smul_eq_mul]
  let L : E × ℝ →L[ℝ] E × ℝ := (ContinuousLinearMap.fst ℝ E ℝ).prod DF
  have hKer : LinearMap.ker L.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨u, t⟩ h
    have hu : u = 0 := congrArg Prod.fst h
    have hv : DF (u, t) = 0 := congrArg Prod.snd h
    rw [hu, hDFvertical t] at hv
    exact Prod.ext hu ((mul_eq_zero.mp hv).resolve_right hd)
  have hSurj : Function.Surjective L := by
    rintro ⟨u, y⟩
    let t := (y - DF (u, 0)) / d
    refine ⟨(u, t), Prod.ext rfl ?_⟩
    change DF (u, t) = y
    rw [show (u, t) = (u, 0) + (0, t) by simp, map_add, hDFvertical t]
    dsimp [t]
    rw [div_mul_cancel₀ _ hd]
    ring
  let D : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
    ContinuousLinearEquiv.ofBijective L hKer (LinearMap.range_eq_top.mpr hSurj)
  let G (z : E × ℝ) : E × ℝ := (z.1, F z)
  have hG : ContDiffAt ℝ ∞ G (u₀, t₀) := contDiff_fst.contDiffAt.prodMk hF
  have hGd : HasFDerivAt G (D : (E × ℝ) →L[ℝ] (E × ℝ)) (u₀, t₀) := by
    have hDL : (D : (E × ℝ) →L[ℝ] (E × ℝ)) = L :=
      ContinuousLinearEquiv.coe_ofBijective L hKer (LinearMap.range_eq_top.mpr hSurj)
    rw [hDL]
    exact (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.prodMk hDF
  let e := hG.toOpenPartialHomeomorph G hGd (by simp)
  have hsource : (u₀, t₀) ∈ e.source := hG.mem_toOpenPartialHomeomorph_source hGd (by simp)
  have hGa : G (u₀, t₀) = (u₀, 0) := Prod.ext rfl hzero
  have htarget : (u₀, (0 : ℝ)) ∈ e.target := by
    rw [← hGa]
    exact hG.image_mem_toOpenPartialHomeomorph_target hGd (by simp)
  have hInv : ContDiffAt ℝ ∞ (fun z => e.symm z) (u₀, (0 : ℝ)) := by
    rw [← hGa]
    exact hG.to_localInverse hGd (by simp)
  let T (u : E) := (e.symm (u, 0)).2
  let Z (u : E) : E × ℝ := (u, 0)
  have hZ : ContDiff ℝ ∞ Z := contDiff_id.prodMk contDiff_const
  have hTdiff : ContDiffAt ℝ ∞ T u₀ :=
    contDiff_snd.contDiffAt.comp u₀ (hInv.comp u₀ hZ.contDiffAt)
  have hTa : T u₀ = t₀ := by
    have h := e.left_inv hsource
    change e.symm (G (u₀, t₀)) = (u₀, t₀) at h
    rw [hGa] at h
    exact congrArg Prod.snd h
  have hnear : ∀ᶠ u in 𝓝 u₀, (u, (0 : ℝ)) ∈ e.target :=
    hZ.continuous.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds htarget)
  refine ⟨T, hTa, hTdiff, ?_⟩
  filter_upwards [hnear] with u hu
  have h := e.right_inv hu
  change G (e.symm (u, 0)) = (u, 0) at h
  have h₁ : (e.symm (u, 0)).1 = u := congrArg Prod.fst h
  have h₂ : F (e.symm (u, 0)) = 0 := congrArg Prod.snd h
  rw [show e.symm (u, 0) = (u, T u) from Prod.ext h₁ rfl] at h₂
  exact h₂

end Burnett.Geometry.CotangentHamiltonSmoothCrossing

namespace Burnett.Geometry.CotangentHamiltonSmoothCrossing

open Set Filter Bundle
open scoped Topology ContDiff Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentHamiltonMaximalCurve Burnett.Geometry.CotangentHamiltonCauchySlice
open Burnett.Geometry.CotangentHamiltonCrossingEnergy

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [T2Space M] in
/-- The actual auxiliary cotangent norm is smooth at every genuine nonzero covector. -/
theorem cotangentNorm_contMDiffAt_punctured (r : Metric (M := M)) (q : CotangentBundle M)
    (hq : q ∈ puncturedCotangent) :
    ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ (cotangentNorm r) q := by
  have hnormSq := contMDiff_dualEnergy r.inner (ManifoldBilinear.isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) r.symm
  have hs := (Real.contDiffAt_sqrt (n := ∞) (auxiliary_dualEnergy_pos r hq).ne').contMDiffAt
  exact hs.comp q hnormSq.contMDiffAt

end Burnett.Geometry.CotangentHamiltonSmoothCrossing

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter Metric
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve

/-- A genuine local phase flow from Picard–Lindelöf, on one open product around
the initial point and zero time, with image in the prescribed open phase set. -/
theorem exists_continuous_localFlow_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {x₀ : E} {V : Set E} (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ U : Set E, ∃ δ > (0 : ℝ), ∃ Φ : E × ℝ → E,
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ ContinuousOn Φ (U ×ˢ Ioo (-δ) δ) ∧
      MapsTo Φ (U ×ˢ Ioo (-δ) δ) V ∧
      (∀ x ∈ U, Φ (x, 0) = x) ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s => Φ (x, s)) (f (Φ (x, t))) t := by
  obtain ⟨ε,hε,a,r,L,K,hr,hp⟩ := IsPicardLindelof.of_contDiffAt_one hf 0
  obtain ⟨Φ,hΦ,hCont⟩ := hp.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hΦ hCont
  have hxBall : x₀ ∈ closedBall x₀ (r : ℝ) := mem_closedBall_self (by positivity)
  have hzeroClosed : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hClosed : closedBall x₀ (r : ℝ) ×ˢ Icc (-ε) ε ∈ 𝓝 (x₀, (0 : ℝ)) := by
    have ho : ball x₀ (r : ℝ) ×ˢ Ioo (-ε) ε ∈ 𝓝 (x₀, (0 : ℝ)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self (by exact_mod_cast hr),
        by show -ε < 0 ∧ 0 < ε; exact ⟨by linarith, hε⟩⟩
    exact mem_of_superset ho (prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  have hCenter : Φ (x₀, 0) = x₀ := (hΦ x₀ hxBall).1
  have hNearby : Φ ⁻¹' V ∈ 𝓝 (x₀, (0 : ℝ)) :=
    ((hCont (x₀, 0) ⟨hxBall, hzeroClosed⟩).continuousAt hClosed).preimage_mem_nhds
      (hV.mem_nhds (hCenter.symm ▸ hx₀))
  rw [nhds_prod_eq] at hNearby
  obtain ⟨W,hW,T,hT,hWT⟩ := mem_prod_iff.mp hNearby
  obtain ⟨δ₀,hδ₀,hTδ⟩ := Metric.mem_nhds_iff.mp hT
  let δ := min ε δ₀
  have hδ : 0 < δ := lt_min hε hδ₀
  let U := (ball x₀ (r : ℝ) ∩ interior W) ∩ V
  have hU : IsOpen U := (isOpen_ball.inter isOpen_interior).inter hV
  have hxU : x₀ ∈ U := ⟨⟨mem_ball_self (by exact_mod_cast hr),
    mem_interior_iff_mem_nhds.mpr hW⟩, hx₀⟩
  have hJε : Ioo (-δ) δ ⊆ Ioo (-ε) ε := fun t ht =>
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hJT : Ioo (-δ) δ ⊆ T := by
    apply subset_trans _ hTδ
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    intro t ht
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hb (x : E) (hx : x ∈ U) : x ∈ closedBall x₀ (r : ℝ) := ball_subset_closedBall hx.1.1
  refine ⟨U,δ,hδ,Φ,hU,hxU,inter_subset_right,?_,?_,fun x hx => (hΦ x (hb x hx)).1,?_⟩
  · exact hCont.mono (prod_mono (fun _ hx => hb _ hx) (hJε.trans Ioo_subset_Icc_self))
  · intro z hz
    exact hWT ⟨interior_subset hz.1.1.2,hJT hz.2⟩
  · intro x hx t ht
    have ht' := hJε ht
    exact ((hΦ x (hb x hx)).2 t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

end Burnett.Geometry.CotangentHamiltonInitialFamily
