import Burnett.Geometry.IntrinsicRicciTrace
import Burnett.Geometry.ManifoldLorentzSignature
import Burnett.Geometry.ManifoldMetricTransition
import Burnett.Geometry.ManifoldVolumeRegularity
import Burnett.Analysis.TransportWard.Weyl.EulerActionConsumer
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Pointwise vanishing of the actual coordinate Euler density in vacuum. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped BigOperators ContDiff Manifold Matrix.Norms.Elementwise Topology

open private contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private eulerFluxTerm contDiffOn_eulerFluxTerm from Burnett.Analysis.TransportWard.Weyl.EulerActionDivergence

local notation "E" => CoordinateSpace

/-- The actual Euler density is smooth on the nonsingular open chart domain. -/
theorem contDiffOn_coordinateDensityEuler
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g : E → ι → ℝ)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hND : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0) (i : ι) :
    ContDiffOn ℝ ∞ (fun y => coordinateDensityEuler S g y i) U := by
  have hG := (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hCoeff (s t : ActionSlot ι) :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ (metricActionCoefficient S s t)
        (assembleMetricComponents S (g y)) (S i)) U := by
    have hd : ContDiffOn ℝ ∞ (fun A : Mat => fderiv ℝ (metricActionCoefficient S s t) A)
        nonsingularMetricDomain :=
      (contDiffOn_metricActionCoefficient S s t).fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)
    exact (hd.clm_apply contDiffOn_const).comp hG hND
  have hLocal (s t : ActionSlot ι) :
      ContDiffOn ℝ ∞ (fun y => ((1 / 2) * fderiv ℝ (metricActionCoefficient S s t)
        (assembleMetricComponents S (g y)) (S i)) * coordinateMetricFirstJet g y s *
          coordinateMetricFirstJet g y t) U :=
    ((contDiffOn_const.mul (hCoeff s t)).mul
      (contDiffOn_coordinateMetricFirstJet hU g hg s)).mul
        (contDiffOn_coordinateMetricFirstJet hU g hg t)
  have hFlux (a : Index) (t : ActionSlot ι) :
      ContDiffOn ℝ ∞ (fun y =>
        fderiv ℝ (eulerFluxTerm S g a i t) y (coordinateBasis a)) U :=
    ((contDiffOn_eulerFluxTerm S g hU hg hND a i t).fderiv_of_isOpen hU (by simp)).clm_apply
      contDiffOn_const
  unfold coordinateDensityEuler
  exact (ContDiffOn.sum fun s _ => ContDiffOn.sum fun t _ => hLocal s t).sub
    (ContDiffOn.sum fun a _ => ContDiffOn.sum fun t _ => hFlux a t)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [T2Space M]

/-- Test a single field direction, whose matrix is symmetric, and use the
positivity of coordinate Lebesgue measure on nonempty open subsets. -/
theorem coordinateDensityEuler_eq_zero_of_intrinsicVacuum
    {ι : Type*} [Fintype ι] (S : ι → Mat) (hS : ∀ i, IsSymmetricTensor (S i))
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (hVac : IntrinsicRicciTrace.IsVacuum B) (c : M) (g : E → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g (chartAt E c).target)
    (hMatch : EqOn (assembledCoordinateMetric S g) (metricComponents (coordinateBilinear B c))
      (chartAt E c).target) (x : E) (hx : x ∈ (chartAt E c).target) (i : ι) :
    coordinateDensityEuler S g x i = 0 := by
  classical
  let U := (chartAt E c).target
  let f : E → ℝ := fun y => coordinateDensityEuler S g y i
  have hU : IsOpen U := (chartAt E c).open_target
  have hND (y : E) (hy : y ∈ U) : Matrix.det (assembleMetricComponents S (g y)) ≠ 0 := by
    change Matrix.det (assembledCoordinateMetric S g y) ≠ 0
    rw [hMatch hy]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c hy
  have hf : ContinuousOn f U := (contDiffOn_coordinateDensityEuler S g hU hg hND i).continuousOn
  have hae : ∀ᵐ y ∂(volume : Measure E), y ∈ U → f y = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn hU.measurableSet)
    intro ψ hψ hCompact hInside
    let K := tsupport ψ
    let h (y : E) (j : ι) : ℝ := if i = j then ψ y else 0
    have hSmooth : ContDiffOn ℝ ∞ h U := by
      apply contDiffOn_pi.mpr
      intro j
      by_cases hij : i = j
      · simpa only [h, if_pos hij] using hψ.contDiffOn (s := U)
      · simpa only [h, if_neg hij] using
          (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℝ)) U)
    have hZero (y : E) (hy : y ∉ K) : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have hSupport (y : E) (hy : y ∈ U \ K) : h y = 0 := by
      funext j
      simp [h, hZero y hy.2]
    have ht := integral_coordinateDensityEuler_eq_zero_of_intrinsicVacuum S hS B hB hSig hVac c
      hCompact hInside g h hg hSmooth hMatch hSupport
    have hs : (∫ y in K, ψ y * f y) = 0 := by
      simpa only [h, f, ite_mul, zero_mul, Fintype.sum_ite_eq] using ht
    suffices (∫ y, ψ y * f y) = 0 by simpa only [smul_eq_mul] using this
    have hGlobal := setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (μ := (volume : Measure E)) (f := fun y => ψ y * f y) (fun y hy => by
        change ψ y * f y = 0
        rw [hZero y hy, zero_mul])
    exact hGlobal.symm.trans hs
  have hRestrict : f =ᵐ[(volume : Measure E).restrict U] (fun _ => (0 : ℝ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hae
  exact Measure.eqOn_open_of_ae_eq hRestrict hU hf continuousOn_const hx

/-- Independent lower metric slots, with one coordinate for each symmetric pair. -/
abbrev SymmetricMetricSlot := {p : Index × Index // p.1 ≤ p.2}

private def orderedMetricSlot (a b : Index) : SymmetricMetricSlot :=
  ⟨(min a b, max a b), (min_le_left a b).trans (le_max_left a b)⟩

/-- A unit variation in one slot acts in both transposed positions of the lower metric. -/
def symmetricMetricDirection (i : SymmetricMetricSlot) : Mat :=
  fun a b => if orderedMetricSlot a b = i then 1 else 0

theorem symmetricMetricDirection_isSymmetric (i : SymmetricMetricSlot) :
    IsSymmetricTensor (symmetricMetricDirection i) := by
  intro a b
  have hab : orderedMetricSlot a b = orderedMetricSlot b a :=
    Subtype.ext (Prod.ext (min_comm a b) (max_comm a b))
  simp only [symmetricMetricDirection, hab]

private theorem assemble_symmetricMetricDirection_apply
    (z : SymmetricMetricSlot → ℝ) (a b : Index) :
    assembleMetricComponents symmetricMetricDirection z a b = z (orderedMetricSlot a b) := by
  simp only [assembleMetricComponents_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    symmetricMetricDirection, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

/-- Reading an independent slot from the actual assembled matrix recovers its input. -/
theorem assemble_symmetricMetricDirection_at_slot
    (z : SymmetricMetricSlot → ℝ) (i : SymmetricMetricSlot) :
    assembleMetricComponents symmetricMetricDirection z i.1.1 i.1.2 = z i := by
  rw [assemble_symmetricMetricDirection_apply]
  have hi : orderedMetricSlot i.1.1 i.1.2 = i :=
    Subtype.ext (Prod.ext (min_eq_left i.2) (max_eq_right i.2))
  rw [hi]

/-- The independent entries of the original lower metric in the preferred chart. -/
def symmetricChartMetricComponents (B : Field (M := M)) (c : M) (y : E)
    (i : SymmetricMetricSlot) : ℝ :=
  metricComponents (coordinateBilinear B c) y i.1.1 i.1.2

omit [T2Space M] in
theorem assembledCoordinateMetric_symmetricChartMetricComponents
    (B : Field (M := M)) (hSym : IsSymmetric B) (c : M) :
    assembledCoordinateMetric symmetricMetricDirection (symmetricChartMetricComponents B c) =
      metricComponents (coordinateBilinear B c) := by
  funext y a b
  change assembleMetricComponents symmetricMetricDirection (symmetricChartMetricComponents B c y)
    a b = _
  rw [assemble_symmetricMetricDirection_apply]
  change metricComponents (coordinateBilinear B c) y (min a b) (max a b) = _
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, max_eq_right hab]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, max_eq_left hba]
    exact FiberMetric.covariant_symmetric _
      (coordinateBilinear_symmetric B hSym c y) coordinateBasis b a

/-- The actual lower chart field of the original intrinsic vacuum metric has
pointwise zero Euler density in every independent symmetric direction. -/
theorem coordinateDensityEuler_symmetricChartMetricComponents_eq_zero
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (hVac : IntrinsicRicciTrace.IsVacuum B) (c : M)
    (x : E) (hx : x ∈ (chartAt E c).target) (i : SymmetricMetricSlot) :
    coordinateDensityEuler symmetricMetricDirection (symmetricChartMetricComponents B c) x i = 0 := by
  have hg : ContDiffOn ℝ ∞ (symmetricChartMetricComponents B c) (chartAt E c).target :=
    contDiffOn_pi.mpr (fun j => ManifoldBilinear.contDiffOn_metricComponents B hB c j.1.1 j.1.2)
  have hMatch : EqOn (assembledCoordinateMetric symmetricMetricDirection (symmetricChartMetricComponents B c))
      (metricComponents (coordinateBilinear B c)) (chartAt E c).target :=
    fun y _ => congrFun (assembledCoordinateMetric_symmetricChartMetricComponents B hSig.isSymmetric c) y
  exact coordinateDensityEuler_eq_zero_of_intrinsicVacuum symmetricMetricDirection
    symmetricMetricDirection_isSymmetric B hB hSig hVac c (symmetricChartMetricComponents B c)
    hg hMatch x hx i

end Burnett.V03.Palatini
