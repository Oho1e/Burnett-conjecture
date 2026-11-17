import Burnett.Counterexamples.RotatingNull.AngularHamilton
import Burnett.Counterexamples.RotatingNull.RotatingTensor
import Burnett.Counterexamples.RotatingNull.HamiltonIdentification
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The genuine interval unit-phase measure model for X03

The positive measure lives on the intrinsic interval unit phase, with the
physical Euclidean square length equal to one, retaining both orientations.
Compact angular fibers over compact base sets strictly inside the interval
are proved compact. Local finiteness is required only on this original
space, as supplied by the original Radon premise; no local finiteness is
assumed for the ambient pushforward across the interval boundary.

All smooth compact symmetric tensor tests in these flat coordinates are
used in the moment interface. Their two sides are genuinely integrable.
The diagonal 00 and off-diagonal 12/21 half tests yield the exact component
moments. Transport uses the actual canonical Hamiltonian and the full
punctured smooth, positive-one-homogeneous, compact BASE support class.
For the separated symbols actually consumed, Hamilton integrability is
proved from genuine continuous compact support on the unit phase.
-/


noncomputable section
namespace Burnett.RotatingNullMoments.MeasureModel
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Function
open scoped BigOperators ContDiff Topology
open Burnett.RicciSymbol

abbrev Base := Burnett.CubicExplicit.Space
abbrev Phase := Base × Covector

def unitShell : Set Covector := {ξ | euclideanSquare ξ = 1}

def UnitPhase (I : Set ℝ) := {p : Phase | p.1 0 ∈ I ∧ euclideanSquare p.2 = 1}

instance instTopologicalSpaceUnitPhase (I : Set ℝ) : TopologicalSpace (UnitPhase I) := inferInstanceAs (TopologicalSpace {p : Phase | p.1 0 ∈ I ∧ euclideanSquare p.2 = 1})
instance instMeasurableSpaceUnitPhase (I : Set ℝ) : MeasurableSpace (UnitPhase I) := inferInstanceAs (MeasurableSpace {p : Phase | p.1 0 ∈ I ∧ euclideanSquare p.2 = 1})
instance instBorelSpaceUnitPhase (I : Set ℝ) : BorelSpace (UnitPhase I) := inferInstanceAs (BorelSpace {p : Phase | p.1 0 ∈ I ∧ euclideanSquare p.2 = 1})
instance instT2SpaceUnitPhase (I : Set ℝ) : T2Space (UnitPhase I) := inferInstanceAs (T2Space {p : Phase | p.1 0 ∈ I ∧ euclideanSquare p.2 = 1})

theorem continuous_euclideanSquare : Continuous euclideanSquare := by
  apply continuous_finset_sum
  intro i _
  exact (continuous_apply i).pow 2

theorem unitShell_norm_le (ξ : Covector) (hξ : ξ ∈ unitShell) : ‖ξ‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  change |ξ i| ≤ 1
  apply abs_le_of_sq_le_sq _ zero_le_one
  calc
    (ξ i)^2 ≤ ∑ j, (ξ j)^2 := Finset.single_le_sum (fun j _ => sq_nonneg (ξ j)) (Finset.mem_univ i)
    _ = (1 : ℝ)^2 := by simpa only [one_pow] using hξ

theorem unitShell_compact : IsCompact unitShell := by
  have hc : IsClosed unitShell := isClosed_eq continuous_euclideanSquare continuous_const
  apply (isCompact_closedBall (0 : Covector) 1).of_isClosed_subset hc
  intro ξ hξ
  simpa only [mem_closedBall, dist_zero_right] using unitShell_norm_le ξ hξ

theorem unitPhase_covector_ne_zero (I : Set ℝ) (p : UnitPhase I) : p.val.2 ≠ 0 := by
  intro h
  have hn := p.property.2
  rw [h] at hn
  norm_num [euclideanSquare] at hn

/-- Compact base sets strictly inside I have genuinely compact full angular fibers. -/
theorem compact_phase_over_base (I : Set ℝ) (K : Set Base) (hK : IsCompact K)
    (hKI : K ⊆ {x | x 0 ∈ I}) : IsCompact {p : UnitPhase I | p.val.1 ∈ K} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace unitShell := isCompact_iff_compactSpace.mp unitShell_compact
  let F : K × unitShell → UnitPhase I :=
    fun q => ⟨(q.1.val, q.2.val), hKI q.1.property, q.2.property⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have heq : F '' (univ : Set (K × unitShell)) = {p : UnitPhase I | p.val.1 ∈ K} := by
    ext p
    constructor
    · rintro ⟨⟨x, ξ⟩, _, rfl⟩
      exact x.property
    · intro hp
      refine ⟨(⟨p.val.1, hp⟩, ⟨p.val.2, p.property.2⟩), mem_univ _, ?_⟩
      rfl
  rw [← heq]
  exact isCompact_univ.image hF

/-- No local-finiteness hypothesis is imposed after extending μ across the I boundary. -/
theorem integrable_compact_base_weight (I : Set ℝ) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (f : Base → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) (w : UnitPhase I → ℝ) (hw : Continuous w) :
    Integrable (fun p : UnitPhase I => f p.val.1 * w p) μ := by
  have hp : HasCompactSupport (fun p : UnitPhase I => f p.val.1 * w p) := by
    apply HasCompactSupport.intro (compact_phase_over_base I (tsupport f) hc ht)
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
  exact ((hf.comp (continuous_fst.comp continuous_subtype_val)).mul hw).integrable_of_hasCompactSupport hp

theorem integrable_component_test (I : Set ℝ) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (f : Base → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) (a b : Index) :
    Integrable (fun p : UnitPhase I => f p.val.1 * p.val.2 a * p.val.2 b) μ := by
  have h := integrable_compact_base_weight I μ f hf hc ht
    (fun p => p.val.2 a * p.val.2 b)
    (((continuous_apply a).comp (continuous_snd.comp continuous_subtype_val)).mul
      ((continuous_apply b).comp (continuous_snd.comp continuous_subtype_val)))
  convert h using 1
  funext p
  ring

/-- All real smooth compact symmetric tensor tests inside the interval. -/
def IsTensorTest (I : Set ℝ) (S : Base → Tensor2) : Prop :=
  ContDiff ℝ ∞ S ∧ HasCompactSupport S ∧ tsupport S ⊆ {x | x 0 ∈ I} ∧
    ∀ x a b, S x a b = S x b a

def baseContraction (c : ℝ) (S : Base → Tensor2) (x : Base) : ℝ :=
  ∑ a, ∑ b, tensor c (x 0) a b * S x a b

def phaseContraction (I : Set ℝ) (S : Base → Tensor2) (p : UnitPhase I) : ℝ :=
  ∑ a, ∑ b, S p.val.1 a b * p.val.2 a * p.val.2 b

/-- The tensor moment identity uses the prescribed rotating T, not Einstein(m). -/
def HasTensorMoments (I : Set ℝ) (c : ℝ) (μ : Measure (UnitPhase I)) : Prop :=
  ∀ S : Base → Tensor2, IsTensorTest I S →
    (∫ p, phaseContraction I S p ∂μ) = ∫ x, baseContraction c S x

def timeTest (f : Base → ℝ) (x : Base) : Tensor2 :=
  fun a b => if a = 0 ∧ b = 0 then f x else 0

def mixedTest (f : Base → ℝ) (x : Base) : Tensor2 :=
  fun a b => if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then f x / 2 else 0

theorem timeTest_smooth (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (timeTest f) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  unfold timeTest
  split_ifs
  · exact hf
  · exact contDiff_const

theorem mixedTest_smooth (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (mixedTest f) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  unfold mixedTest
  split_ifs
  · exact hf.div_const 2
  · exact contDiff_const

theorem timeTest_support (f : Base → ℝ) : tsupport (timeTest f) ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  by_contra hf
  apply hx
  have hz : f x = 0 := by
    by_contra h
    exact hf h
  funext a b
  simp [timeTest, hz]

theorem mixedTest_support (f : Base → ℝ) : tsupport (mixedTest f) ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  by_contra hf
  apply hx
  have hz : f x = 0 := by
    by_contra h
    exact hf h
  funext a b
  simp [mixedTest, hz]

theorem timeTest_isTensorTest (I : Set ℝ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) : IsTensorTest I (timeTest f) := by
  refine ⟨timeTest_smooth f hf, ?_, (timeTest_support f).trans ht, ?_⟩
  · exact hc.of_isClosed_subset (isClosed_tsupport _) (timeTest_support f)
  · intro x a b
    simp [timeTest, and_comm]

theorem mixedTest_isTensorTest (I : Set ℝ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) : IsTensorTest I (mixedTest f) := by
  refine ⟨mixedTest_smooth f hf, ?_, (mixedTest_support f).trans ht, ?_⟩
  · exact hc.of_isClosed_subset (isClosed_tsupport _) (mixedTest_support f)
  · intro x a b
    simp [mixedTest, and_comm, or_comm]

theorem timeTest_phase (I : Set ℝ) (f : Base → ℝ) (p : UnitPhase I) :
    phaseContraction I (timeTest f) p = f p.val.1 * (p.val.2 0)^2 := by
  simp [phaseContraction, timeTest, Fin.sum_univ_succ]
  ring

theorem mixedTest_phase (I : Set ℝ) (f : Base → ℝ) (p : UnitPhase I) :
    phaseContraction I (mixedTest f) p = f p.val.1 * p.val.2 1 * p.val.2 2 := by
  simp [phaseContraction, mixedTest, Fin.sum_univ_succ]
  ring

theorem timeTest_base (c : ℝ) (f : Base → ℝ) (x : Base) :
    baseContraction c (timeTest f) x = 2*c * f x := by
  simp [baseContraction, timeTest, Fin.sum_univ_succ, tensor_components]

theorem mixedTest_base (c : ℝ) (f : Base → ℝ) (x : Base) :
    baseContraction c (mixedTest f) x = 2*c * (Real.cos (x 0) * Real.sin (x 0)) * f x := by
  simp [baseContraction, mixedTest, Fin.sum_univ_succ, tensor_components, direction]
  ring

theorem moment00_of_tensor_moments (I : Set ℝ) (c : ℝ) (μ : Measure (UnitPhase I))
    (hm : HasTensorMoments I c μ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    (∫ p : UnitPhase I, f p.val.1 * (p.val.2 0)^2 ∂μ) = ∫ x : Base, 2*c * f x := by
  have h := hm (timeTest f) (timeTest_isTensorTest I f hf hc ht)
  simpa only [timeTest_phase, timeTest_base] using h

theorem moment12_of_tensor_moments (I : Set ℝ) (c : ℝ) (μ : Measure (UnitPhase I))
    (hm : HasTensorMoments I c μ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    (∫ p : UnitPhase I, f p.val.1 * p.val.2 1 * p.val.2 2 ∂μ) =
      ∫ x : Base, 2*c * (Real.cos (x 0) * Real.sin (x 0)) * f x := by
  have h := hm (mixedTest f) (mixedTest_isTensorTest I f hf hc ht)
  simpa only [mixedTest_phase, mixedTest_base] using h

theorem tensor_component_support (S : Base → Tensor2) (a b : Index) :
    tsupport (fun x => S x a b) ⊆ tsupport S := by
  apply closure_mono
  intro x hx
  by_contra hs
  have hz : S x = 0 := by
    by_contra h
    exact hs h
  exact hx (by change S x a b = 0; rw [hz]; rfl)

theorem tensor_test_phase_integrable (I : Set ℝ) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (S : Base → Tensor2) (hS : IsTensorTest I S) :
    Integrable (phaseContraction I S) μ := by
  apply integrable_finset_sum
  intro a _
  apply integrable_finset_sum
  intro b _
  exact integrable_component_test I μ (fun x => S x a b)
    ((continuous_apply b).comp ((continuous_apply a).comp hS.1.continuous))
    (hS.2.1.of_isClosed_subset (isClosed_tsupport _) (tensor_component_support S a b))
    ((tensor_component_support S a b).trans hS.2.2.1) a b

theorem tensor_test_base_integrable (I : Set ℝ) (c : ℝ) (S : Base → Tensor2) (hS : IsTensorTest I S) :
    Integrable (baseContraction c S) := by
  apply integrable_finset_sum
  intro a _
  apply integrable_finset_sum
  intro b _
  have ht : Continuous (fun x : Base => tensor c (x 0) a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp (tensor_spacetime_smooth c).continuous)
  have hs : Continuous (fun x : Base => S x a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp hS.1.continuous)
  have hc : HasCompactSupport (fun x : Base => S x a b) :=
    hS.2.1.of_isClosed_subset (isClosed_tsupport _) (tensor_component_support S a b)
  exact (ht.mul hs).integrable_of_hasCompactSupport hc.mul_left

def ambientMeasure (I : Set ℝ) (μ : Measure (UnitPhase I)) : Measure Phase :=
  Measure.map (fun p : UnitPhase I => p.val) μ

theorem unitPhase_measurableSet (I : Set ℝ) (hI : IsOpen I) :
    MeasurableSet {p : Phase | p.1 0 ∈ I ∧ euclideanSquare p.2 = 1} :=
  ((hI.preimage ((Burnett.CubicExplicit.coord 0).continuous.comp continuous_fst)).measurableSet).inter
    ((isClosed_eq (continuous_euclideanSquare.comp continuous_snd) continuous_const).measurableSet)

theorem unitPhase_measurableEmbedding (I : Set ℝ) (hI : IsOpen I) :
    MeasurableEmbedding (fun p : UnitPhase I => p.val) :=
  MeasurableEmbedding.subtype_coe (unitPhase_measurableSet I hI)

theorem ambient_integral (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I)) (f : Phase → ℝ) :
    (∫ p : Phase, f p ∂ambientMeasure I μ) = ∫ p : UnitPhase I, f p.val ∂μ :=
  (unitPhase_measurableEmbedding I hI).integral_map f

theorem ambient_unit_ae (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I)) :
    ∀ᵐ p : Phase ∂ambientMeasure I μ, euclideanSquare p.2 = 1 :=
  (unitPhase_measurableEmbedding I hI).ae_map_iff.mpr (Filter.Eventually.of_forall fun p => p.property.2)

theorem ambient_nonzero_ae (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I)) :
    ∀ᵐ p : Phase ∂ambientMeasure I μ, p.2 ≠ 0 :=
  (unitPhase_measurableEmbedding I hI).ae_map_iff.mpr
    (Filter.Eventually.of_forall fun p => unitPhase_covector_ne_zero I p)

/-- The null support is precisely the null-ray premise of the original representation. -/
def IsNullSupported (I : Set ℝ) (μ : Measure (UnitPhase I)) : Prop :=
  ∀ᵐ p : UnitPhase I ∂μ, symbolNorm NullScreen.minkowskiInverse p.val.2 = 0

theorem ambient_null_ae (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I))
    (hn : IsNullSupported I μ) :
    ∀ᵐ p : Phase ∂ambientMeasure I μ, symbolNorm NullScreen.minkowskiInverse p.2 = 0 :=
  (unitPhase_measurableEmbedding I hI).ae_map_iff.mpr hn

theorem ambient_component_integrable (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (f : Base → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) (a b : Index) :
    Integrable (fun p : Phase => f p.1 * p.2 a * p.2 b) (ambientMeasure I μ) :=
  (unitPhase_measurableEmbedding I hI).integrable_map_iff.mpr
    (integrable_component_test I μ f hf hc ht a b)

theorem ambient_moment00 (I : Set ℝ) (hI : IsOpen I) (c : ℝ) (μ : Measure (UnitPhase I))
    (hm : HasTensorMoments I c μ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    (∫ p : Phase, f p.1 * (p.2 0)^2 ∂ambientMeasure I μ) = ∫ x : Base, 2*c * f x := by
  rw [ambient_integral I hI]
  exact moment00_of_tensor_moments I c μ hm f hf hc ht

theorem ambient_moment12 (I : Set ℝ) (hI : IsOpen I) (c : ℝ) (μ : Measure (UnitPhase I))
    (hm : HasTensorMoments I c μ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    (∫ p : Phase, f p.1 * p.2 1 * p.2 2 ∂ambientMeasure I μ) =
      ∫ x : Base, 2*c * (Real.cos (x 0) * Real.sin (x 0)) * f x := by
  rw [ambient_integral I hI]
  exact moment12_of_tensor_moments I c μ hm f hf hc ht

/-- The original punctured, positive-one-homogeneous, compact-base test class. -/
def IsTransportTest (I : Set ℝ) (a : Base → Covector → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun p : Phase => a p.1 p.2) {p | p.2 ≠ 0} ∧
    (∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r → a x (r • ξ) = r * a x ξ) ∧
    ∃ K : Set Base, IsCompact K ∧ K ⊆ {x | x 0 ∈ I} ∧ ∀ x ∉ K, ∀ ξ : Covector, ξ ≠ 0 → a x ξ = 0

def HasHamiltonTransport (I : Set ℝ) (μ : Measure (UnitPhase I)) : Prop :=
  ∀ a : Base → Covector → ℝ, IsTransportTest I a →
    (∫ p : UnitPhase I, CanonicalHamilton.canonicalHamilton a p.val.1 p.val.2 ∂μ) = 0

theorem separatedTest_isTransportTest (I : Set ℝ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    IsTransportTest I (separatedTest f) := by
  refine ⟨separatedTest_smooth f hf, ?_, tsupport f, hc, ht, ?_⟩
  · intro x ξ _ r _
    exact separatedTest_homogeneous f x r ξ
  · intro x hx ξ _
    exact separatedTest_zero_outside_base_support f x hx ξ

theorem ambient_transport (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I))
    (ht : HasHamiltonTransport I μ) (a : Base → Covector → ℝ) (ha : IsTransportTest I a) :
    (∫ p : Phase, CanonicalHamilton.canonicalHamilton a p.1 p.2 ∂ambientMeasure I μ) = 0 := by
  rw [ambient_integral I hI]
  exact ht a ha

theorem continuous_oddAngular_on_unit (I : Set ℝ) :
    Continuous (fun p : UnitPhase I => oddAngular p.val.2) :=
  oddAngular_smooth.continuousOn.comp_continuous (continuous_snd.comp continuous_subtype_val)
    (fun p => unitPhase_covector_ne_zero I p)

theorem continuous_flatHamilton_separated_on_unit (I : Set ℝ) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : UnitPhase I => flatHamilton (separatedTest f) p.val.1 p.val.2) := by
  have hd (i : Index) : Continuous (fun x : Base => Burnett.CubicExplicit.D i f x) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hv (i : Index) : Continuous (fun p : UnitPhase I => raiseCovector NullScreen.minkowskiInverse p.val.2 i) := by
    unfold raiseCovector
    apply continuous_finset_sum
    intro j _
    exact continuous_const.mul ((continuous_apply j).comp (continuous_snd.comp continuous_subtype_val))
  have hs : Continuous (fun p : UnitPhase I => oddAngular p.val.2 *
      ∑ i, raiseCovector NullScreen.minkowskiInverse p.val.2 i * Burnett.CubicExplicit.D i f p.val.1) := by
    apply (continuous_oddAngular_on_unit I).mul
    apply continuous_finset_sum
    intro i _
    exact (hv i).mul ((hd i).comp (continuous_fst.comp continuous_subtype_val))
  convert hs using 1
  funext p
  exact flatHamilton_separated f (hf.differentiable (by simp)) p.val.1 p.val.2

theorem separated_Hamilton_integrable (I : Set ℝ) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    Integrable (fun p : UnitPhase I => CanonicalHamilton.canonicalHamilton (separatedTest f) p.val.1 p.val.2) μ := by
  have hp : HasCompactSupport (fun p : UnitPhase I => flatHamilton (separatedTest f) p.val.1 p.val.2) := by
    apply HasCompactSupport.intro (compact_phase_over_base I (tsupport f) hc ht)
    intro p hp
    rw [flatHamilton_separated f (hf.differentiable (by simp))]
    have hz : fderiv ℝ f p.val.1 = 0 := fderiv_of_notMem_tsupport ℝ hp
    simp [Burnett.CubicExplicit.D, hz]
  have h : Integrable (fun p : UnitPhase I => flatHamilton (separatedTest f) p.val.1 p.val.2) μ :=
    (continuous_flatHamilton_separated_on_unit I f hf).integrable_of_hasCompactSupport hp
  convert h using 1
  funext p
  exact CanonicalHamilton.canonicalHamilton_eq_flatHamilton _ _ _

theorem ambient_separated_Hamilton_integrable (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    Integrable (fun p : Phase => CanonicalHamilton.canonicalHamilton (separatedTest f) p.1 p.2) (ambientMeasure I μ) :=
  (unitPhase_measurableEmbedding I hI).integrable_map_iff.mpr (separated_Hamilton_integrable I μ f hf hc ht)

theorem ambient_moment00_integrable (I : Set ℝ) (hI : IsOpen I) (μ : Measure (UnitPhase I))
    [IsLocallyFiniteMeasure μ] (f : Base → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x | x 0 ∈ I}) :
    Integrable (fun p : Phase => f p.1 * (p.2 0)^2) (ambientMeasure I μ) := by
  convert ambient_component_integrable I hI μ f hf hc ht 0 0 using 1
  funext p
  ring

end Burnett.RotatingNullMoments.MeasureModel
