import Burnett.Geometry.IntrinsicRicciTrace
import Burnett.Geometry.ManifoldLorentzSignature
import Burnett.Geometry.ManifoldMetricTransition
import Burnett.Geometry.ManifoldVolumeRegularity
import Burnett.Analysis.TransportWard.Weyl.PointwiseVacuum
import Burnett.Analysis.TransportWard.Weyl.AffineActionHessian

/-! Formal self-adjointness of the full linearized coordinate density Euler operator. -/

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped BigOperators ContDiff Manifold Matrix.Norms.Elementwise Topology

open private coordinateMetricFirstJet_line contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private eulerFluxTerm from Burnett.Analysis.TransportWard.Weyl.EulerActionDivergence
open private integrableOn_and_integral_coordinateDivergence_eq_zero from Burnett.Analysis.TransportWard.Weyl.EulerActionIntegral

local notation "E" => CoordinateSpace
local notation "P" => MetricParameterSpace

private abbrev fieldVariationDomain {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) (U : Set E) : Set P :=
  nonsingularVariationDomain (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) U

private theorem isOpen_fieldVariationDomain {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) :
    IsOpen (fieldVariationDomain S g h U) := by
  have hComp (q : E → ι → ℝ) (hq : ContDiffOn ℝ ∞ q U) (i j : Index) :
      ContDiffOn ℝ ∞ (fun y => assembledCoordinateMetric S q y i j) U :=
    contDiffOn_pi.mp
      (contDiffOn_pi.mp ((assembleMetricComponents S).contDiff.comp_contDiffOn hq) i) j
  exact isOpen_nonsingularVariationDomain _ _ hU (hComp g hg) (hComp h hh)

private theorem det_fieldVariation_ne_zero {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) {U : Set E} {z : P} (hz : z ∈ fieldVariationDomain S g h U) :
    Matrix.det (assembleMetricComponents S (g z.2 + z.1 • h z.2)) ≠ 0 := by
  have hn : Matrix.det
      (metricAffineVariation (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) z.1 z.2)
        ≠ 0 := hz.2
  simpa only [metricAffineVariation, assembledCoordinateMetric, map_add, map_smul] using hn

private theorem contDiffOn_parameterizedEulerBoundary
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ) {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hk : ContDiffOn ℝ ∞ k U) (a : Index) :
    ContDiffOn ℝ ∞ (fun z : P => eulerVariationBoundaryVector S
      (fun y => g y + z.1 • h y) k z.2 a) (fieldVariationDomain S g h U) := by
  let Ω := fieldVariationDomain S g h U
  have hsnd : ContDiffOn ℝ ∞ (Prod.snd : P → E) Ω := contDiff_snd.contDiffOn
  have hspace : MapsTo (Prod.snd : P → E) Ω U := fun _ hz => hz.1
  have hField : ContDiffOn ℝ ∞ (fun z : P => g z.2 + z.1 • h z.2) Ω :=
    (hg.comp hsnd hspace).add (contDiff_fst.contDiffOn.smul (hh.comp hsnd hspace))
  have hG := (assembleMetricComponents S).contDiff.comp_contDiffOn hField
  have hp (s : ActionSlot ι) : ContDiffOn ℝ ∞ (fun z : P =>
      coordinateMetricFirstJet (fun y => g y + z.1 • h y) z.2 s) Ω := by
    have hg₁ := (contDiffOn_coordinateMetricFirstJet hU g hg s).comp hsnd hspace
    have hh₁ := (contDiffOn_coordinateMetricFirstJet hU h hh s).comp hsnd hspace
    refine (hg₁.add (contDiff_fst.contDiffOn.mul hh₁)).congr ?_
    intro z hz
    have hgD := (hg.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp)
    have hhD := (hh.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp)
    exact congrFun (coordinateMetricFirstJet_line g h z.2 z.1 hgD hhD) s
  have hC (i : ι) (s : ActionSlot ι) : ContDiffOn ℝ ∞ (fun z : P =>
      metricActionCoefficient S (a, i) s (assembleMetricComponents S (g z.2 + z.1 • h z.2))) Ω :=
    (contDiffOn_metricActionCoefficient S (a, i) s).comp hG
      (fun _ hz => det_fieldVariation_ne_zero S g h hz)
  have hk' (i : ι) : ContDiffOn ℝ ∞ (fun z : P => k z.2 i) Ω :=
    ((contDiff_apply ℝ ℝ i).comp_contDiffOn hk).comp hsnd hspace
  unfold eulerVariationBoundaryVector eulerFluxTerm
  exact ContDiffOn.sum fun i _ => (hk' i).mul (ContDiffOn.sum fun s _ => (hC i s).mul (hp s))

/-- The true parameter derivative of the original Euler variation boundary flux. -/
def linearizedEulerBoundaryVector {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h k : E → ι → ℝ) (x : E) (a : Index) : ℝ :=
  deriv (fun t : ℝ => eulerVariationBoundaryVector S (fun y => g y + t • h y) k x a) 0

theorem contDiffOn_linearizedEulerBoundaryVector
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0) (a : Index) :
    ContDiffOn ℝ ∞ (fun y => linearizedEulerBoundaryVector S g h k y a) U := by
  let F := fun z : P => eulerVariationBoundaryVector S (fun y => g y + z.1 • h y) k z.2 a
  let Ω := fieldVariationDomain S g h U
  have hΩ : IsOpen Ω := isOpen_fieldVariationDomain S g h hU hg hh
  have hF : ContDiffOn ℝ ∞ F Ω := contDiffOn_parameterizedEulerBoundary S g h k hU hg hh hk a
  have h0 (y : E) (hy : y ∈ U) : (0, y) ∈ Ω :=
    zero_mem_nonsingularVariationDomain _ _ y hy (hn y hy)
  have hD : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z (1, 0)) Ω :=
    (hF.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hSlice : ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ F (0, y) (1, 0)) U :=
    hD.comp (contDiff_const.prodMk contDiff_id).contDiffOn h0
  refine hSlice.congr ?_
  intro y hy
  exact (hasDerivAt_parameterSlice F 0 y
    ((hF.contDiffAt (hΩ.mem_nhds (h0 y hy))).differentiableAt (by simp))).deriv

private theorem hasDerivAt_coordinateDivergence_parameterizedEulerBoundary
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hk : ContDiffOn ℝ ∞ k U) (x : E) (hx : x ∈ U)
    (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    HasDerivAt (fun t : ℝ => coordinateDivergence (eulerVariationBoundaryVector S
      (fun y => g y + t • h y) k) x)
      (coordinateDivergence (linearizedEulerBoundaryVector S g h k) x) 0 := by
  have hΩ := isOpen_fieldVariationDomain S g h hU hg hh
  have h0 : (0, x) ∈ fieldVariationDomain S g h U :=
    zero_mem_nonsingularVariationDomain _ _ x hx hn
  unfold coordinateDivergence linearizedEulerBoundaryVector
  exact HasDerivAt.fun_sum fun a _ =>
    hasDerivAt_coordinatePartial_parameterSlice _ hΩ
      (contDiffOn_parameterizedEulerBoundary S g h k hU hg hh hk a) x h0 a

private theorem hasDerivAt_coordinateEulerPairing_along_affine
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hk : ContDiffOn ℝ ∞ k U) (x : E) (hx : x ∈ U)
    (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    HasDerivAt (fun t : ℝ => ∑ i, k x i * coordinateDensityEuler S (fun y => g y + t • h y) x i)
      (coordinateActionHessianDensity S g h k x -
        coordinateDivergence (linearizedEulerBoundaryVector S g h k) x) 0 := by
  have hxU := hU.mem_nhds hx
  have hW := hasDerivAt_coordinateWeakActionVariation S g h k x
    ((hg.contDiffAt hxU).differentiableAt (by simp))
    ((hh.contDiffAt hxU).differentiableAt (by simp))
    ((hk.contDiffAt hxU).differentiableAt (by simp)) hn
  have hDiv := hasDerivAt_coordinateDivergence_parameterizedEulerBoundary S g h k hU hg hh hk x hx hn
  apply (hW.sub hDiv).congr_of_eventuallyEq
  let Ω := fieldVariationDomain S g h U
  have hΩ : IsOpen Ω := isOpen_fieldVariationDomain S g h hU hg hh
  have h0 : (0, x) ∈ Ω := zero_mem_nonsingularVariationDomain _ _ x hx hn
  have hNear : (fun t : ℝ => (t, x)) ⁻¹' Ω ∈ 𝓝 (0 : ℝ) :=
    (hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds h0
  filter_upwards [hNear] with t ht
  let Y := (fun y : E => (t, y)) ⁻¹' Ω
  have hY : IsOpen Y := hΩ.preimage (continuous_const.prodMk continuous_id)
  have hYU : Y ⊆ U := fun _ hy => hy.1
  have hYnd (y : E) (hy : y ∈ Y) :
      Matrix.det (assembleMetricComponents S (g y + t • h y)) ≠ 0 :=
    det_fieldVariation_ne_zero S g h (show (t, y) ∈ Ω from hy)
  have ht' := coordinateWeakActionVariation_eq_coordinateDensityEuler_add_divergence
    S (fun y => g y + t • h y) k hY
      ((hg.add (hh.const_smul t)).mono hYU) (hk.mono hYU) hYnd x ht
  exact eq_sub_iff_add_eq.mpr ht'.symm

/-- Actual linearization of the coordinate Euler density along the lower
metric variation, retaining the background dependence of every coefficient. -/
def linearizedCoordinateDensityEuler {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) (x : E) (i : ι) : ℝ :=
  deriv (fun t : ℝ => coordinateDensityEuler S (fun y => g y + t • h y) x i) 0

theorem hasDerivAt_linearizedCoordinateDensityEuler
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h : E → ι → ℝ)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (x : E) (hx : x ∈ U) (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) (i : ι) :
    HasDerivAt (fun t : ℝ => coordinateDensityEuler S (fun y => g y + t • h y) x i)
      (linearizedCoordinateDensityEuler S g h x i) 0 := by
  classical
  let k (_ : E) (j : ι) : ℝ := if i = j then 1 else 0
  have hk : ContDiffOn ℝ ∞ k U := contDiffOn_const
  have hp := hasDerivAt_coordinateEulerPairing_along_affine S g h k hU hg hh hk x hx hn
  have hd : HasDerivAt (fun t : ℝ => coordinateDensityEuler S (fun y => g y + t • h y) x i)
      (coordinateActionHessianDensity S g h k x -
        coordinateDivergence (linearizedEulerBoundaryVector S g h k) x) 0 := by
    simpa only [k, ite_mul, zero_mul, one_mul, Fintype.sum_ite_eq] using hp
  unfold linearizedCoordinateDensityEuler
  rw [hd.deriv]
  exact hd

/-- Green's identity at the level of the full density and the actual boundary vector. -/
theorem linearizedCoordinateDensityEuler_pairing_eq_hessian_sub_divergence
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hk : ContDiffOn ℝ ∞ k U) (x : E) (hx : x ∈ U)
    (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    (∑ i, k x i * linearizedCoordinateDensityEuler S g h x i) =
      coordinateActionHessianDensity S g h k x -
        coordinateDivergence (linearizedEulerBoundaryVector S g h k) x := by
  have hsum := HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_linearizedCoordinateDensityEuler S g h hU hg hh x hx hn i).const_mul (k x i)
  exact hsum.unique (hasDerivAt_coordinateEulerPairing_along_affine S g h k hU hg hh hk x hx hn)

theorem integral_linearizedCoordinateDensityEuler_eq_hessian
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (hk0 : ∀ y ∈ U \ K, k y = 0) :
    (∫ y in U, ∑ i, k y i * linearizedCoordinateDensityEuler S g h y i) =
      ∫ y in K, coordinateActionHessianDensity S g h k y := by
  let V := linearizedEulerBoundaryVector S g h k
  let A (y : E) := ∑ i, k y i * linearizedCoordinateDensityEuler S g h y i
  have hz (y : E) (hy : y ∈ U \ K) (a : Index) : V y a = 0 := by
    simp only [V, linearizedEulerBoundaryVector, eulerVariationBoundaryVector, hk0 y hy,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, deriv_const]
  have hD := integrableOn_and_integral_coordinateDivergence_eq_zero hU hK hKU V
    (contDiffOn_linearizedEulerBoundaryVector S g h k hU hg hh hk hn) hz
  have hH : IntegrableOn (coordinateActionHessianDensity S g h k) K (volume : Measure E) :=
    ((contDiffOn_coordinateActionHessianDensity S g h k hU hg hh hk hn).continuousOn.mono
      hKU).integrableOn_compact hK
  have hEq : EqOn A (fun y => coordinateActionHessianDensity S g h k y -
      coordinateDivergence V y) K := fun y hy =>
    linearizedCoordinateDensityEuler_pairing_eq_hessian_sub_divergence S g h k hU hg hh hk y
      (hKU hy) (hn y (hKU hy))
  have hA0 (y : E) (hy : y ∈ U \ K) : A y = 0 := by
    simp only [A, hk0 y hy, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  change (∫ y in U, A y) = _
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hKU hA0,
    setIntegral_congr_fun hK.measurableSet hEq, integral_sub hH hD.1, hD.2, sub_zero]

/-- The actual full linearized Euler operator is formally self-adjoint on
compact real field tests. No equation on the smooth background is used. -/
theorem integral_linearizedCoordinateDensityEuler_swap
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E → ι → ℝ) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (hh0 : ∀ y ∈ U \ K, h y = 0) (hk0 : ∀ y ∈ U \ K, k y = 0) :
    (∫ y in U, ∑ i, k y i * linearizedCoordinateDensityEuler S g h y i) =
      ∫ y in U, ∑ i, h y i * linearizedCoordinateDensityEuler S g k y i := by
  rw [integral_linearizedCoordinateDensityEuler_eq_hessian S g h k hU hK hKU hg hh hk hn hk0,
    integral_linearizedCoordinateDensityEuler_eq_hessian S g k h hU hK hKU hg hk hh hn hh0]
  exact setIntegral_congr_fun hK.measurableSet fun y hy =>
    coordinateActionHessianDensity_swap S g h k y (hn y (hKU hy))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The same symmetry for the actual lower metric in a chart, using its
independent symmetric directions for both compact tests. -/
theorem integral_linearizedCoordinateDensityEuler_actualChart_swap
    (B : Field (M := M)) (hB : IsSmooth B) (hSym : IsSymmetric B)
    (hND : IsNondegenerate B) (c : M) {K : Set E}
    (h h' : E → SymmetricMetricSlot → ℝ)
    (hK : IsCompact K) (hKU : K ⊆ (chartAt E c).target)
    (hh : ContDiffOn ℝ ∞ h (chartAt E c).target) (hh' : ContDiffOn ℝ ∞ h' (chartAt E c).target)
    (h0 : ∀ y ∈ (chartAt E c).target \ K, h y = 0)
    (h0' : ∀ y ∈ (chartAt E c).target \ K, h' y = 0) :
    (∫ y in (chartAt E c).target, ∑ i, h' y i * linearizedCoordinateDensityEuler
      symmetricMetricDirection (symmetricChartMetricComponents B c) h y i) =
    ∫ y in (chartAt E c).target, ∑ i, h y i * linearizedCoordinateDensityEuler
      symmetricMetricDirection (symmetricChartMetricComponents B c) h' y i := by
  let g := symmetricChartMetricComponents B c
  let S := symmetricMetricDirection
  have hg : ContDiffOn ℝ ∞ g (chartAt E c).target :=
    contDiffOn_pi.mpr (fun j => ManifoldBilinear.contDiffOn_metricComponents B hB c j.1.1 j.1.2)
  have hn (x : E) (hx : x ∈ (chartAt E c).target) :
      Matrix.det (assembleMetricComponents S (g x)) ≠ 0 := by
    change Matrix.det (assembledCoordinateMetric symmetricMetricDirection (symmetricChartMetricComponents B c) x)
      ≠ 0
    rw [assembledCoordinateMetric_symmetricChartMetricComponents B hSym c]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hND c hx
  exact integral_linearizedCoordinateDensityEuler_swap S g h h' (chartAt E c).open_target
    hK hKU hg hh hh' hn h0 h0'

end Burnett.V03.Palatini
