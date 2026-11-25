import Burnett.Geometry.GlobalLeviCivita
import Burnett.Geometry.ManifoldVolumeRegularity
import Burnett.Geometry.GramCoordinateBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Burnett.Geometry.SmoothMetricConnection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Burnett.Geometry.MetricJetNaturality
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Burnett.Geometry.BackgroundConnection
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.LeftRightNhds
import Burnett.Geometry.BasisFrame
import Burnett.Geometry.ManifoldBilinear
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Algebra.Order.Group.Pointwise.Bounds
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Burnett.Geometry.Cotangent.RadialExtension
import Burnett.Geometry.ManifoldLorentzSignature

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.RadialHamilton

open Matrix Set Module
open scoped ContDiff BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase)

def coordinateP (G : CoordinateSpace → Tensor2) (p : Phase) : ℝ :=
  symbolNorm (G p.1) p.2 / 2

theorem coordinateP_scale (G : CoordinateSpace → Tensor2) (p : Phase) (t : ℝ) :
    coordinateP G (p.1, t • p.2) = t^2 * coordinateP G p := by
  simp only [coordinateP, ← UnitNullAngular.dualPair_self, UnitNullAngular.dualPair_smul_self]
  ring

theorem contDiff_coordinateP_momentum (G : CoordinateSpace → Tensor2) (x : CoordinateSpace) :
    ContDiff ℝ ∞ (fun ξ : Covector => coordinateP G (x, ξ)) := by
  simp only [coordinateP, symbolNorm]
  exact (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_const.mul (contDiff_apply ℝ ℝ i)).mul (contDiff_apply ℝ ℝ j)).div_const 2

def phaseScale (t : ℝ) : Phase →L[ℝ] Phase :=
  (ContinuousLinearMap.fst ℝ CoordinateSpace Covector).prod
    (t • ContinuousLinearMap.snd ℝ CoordinateSpace Covector)

theorem phaseScale_apply (t : ℝ) (p : Phase) : phaseScale t p = (p.1, t • p.2) := rfl

theorem coordinateP_fderiv_base_scale (G : CoordinateSpace → Tensor2) (p : Phase) (t : ℝ) :
    fderiv ℝ (fun x => coordinateP G (x, t • p.2)) p.1 =
      t^2 • fderiv ℝ (fun y => coordinateP G (y, p.2)) p.1 := by
  have he : (fun x => coordinateP G (x, t • p.2)) = (t^2 : ℝ) • (fun y => coordinateP G (y, p.2)) :=
    funext (fun x => coordinateP_scale G (x,p.2) t)
  rw [he, fderiv_const_smul_of_field]
  rfl

theorem coordinateP_fderiv_momentum_scale (G : CoordinateSpace → Tensor2) (p : Phase)
    {t : ℝ} (ht : t ≠ 0) :
    fderiv ℝ (fun ξ => coordinateP G (p.1, ξ)) (t • p.2) =
      t • fderiv ℝ (fun ξ => coordinateP G (p.1, ξ)) p.2 := by
  let f := fun ξ : Covector => coordinateP G (p.1, ξ)
  let L : Covector →L[ℝ] Covector := t • ContinuousLinearMap.id ℝ Covector
  have hL : HasFDerivAt (fun ξ : Covector => t • ξ) L p.2 := L.hasFDerivAt
  have hF := (contDiff_coordinateP_momentum G p.1).differentiable (by simp) (t • p.2)
  have hC := hF.hasFDerivAt.comp p.2 hL
  have he : f ∘ (fun ξ : Covector => t • ξ) = (t^2 : ℝ) • f :=
    funext (fun ξ => coordinateP_scale G (p.1,ξ) t)
  change HasFDerivAt (f ∘ (fun ξ : Covector => t • ξ))
    ((fderiv ℝ f (t • p.2)).comp L) p.2 at hC
  rw [he] at hC
  have h := hC.fderiv
  rw [fderiv_const_smul_of_field] at h
  change fderiv ℝ f (t • p.2) = t • fderiv ℝ f p.2
  ext v
  change (t^2 : ℝ) • fderiv ℝ f p.2 = (fderiv ℝ f (t • p.2)).comp L at h
  have hv := congrArg (fun D : Covector →L[ℝ] ℝ => D v) h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, L,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv ⊢
  apply mul_left_cancel₀ ht
  rw [← hv]
  ring

def basePartial (F : Phase → ℝ) (p : Phase) (i : Index) : ℝ :=
  fderiv ℝ (fun x => F (x,p.2)) p.1 (coordinateBasis i)

def momentumPartial (F : Phase → ℝ) (p : Phase) (i : Index) : ℝ :=
  fderiv ℝ (fun ξ => F (p.1,ξ)) p.2 (Pi.single i 1)

def hamiltonVector (G : CoordinateSpace → Tensor2) (p : Phase) : Phase :=
  (WithLp.toLp 2 (momentumPartial (coordinateP G) p), fun i => -basePartial (coordinateP G) p i)

theorem hamiltonVector_base_scale (G : CoordinateSpace → Tensor2) (p : Phase)
    {t : ℝ} (ht : t ≠ 0) :
    (hamiltonVector G (phaseScale t p)).1 = t • (hamiltonVector G p).1 := by
  have h := coordinateP_fderiv_momentum_scale G p ht
  ext i
  change fderiv ℝ (fun ξ => coordinateP G (p.1,ξ)) (t • p.2) (Pi.single i 1) =
    t * fderiv ℝ (fun ξ => coordinateP G (p.1,ξ)) p.2 (Pi.single i 1)
  rw [h]
  rfl

theorem hamiltonVector_momentum_scale (G : CoordinateSpace → Tensor2) (p : Phase) (t : ℝ) :
    (hamiltonVector G (phaseScale t p)).2 = t^2 • (hamiltonVector G p).2 := by
  have h := coordinateP_fderiv_base_scale G p t
  funext i
  change -fderiv ℝ (fun x => coordinateP G (x,t • p.2)) p.1 (coordinateBasis i) =
    t^2 * (-fderiv ℝ (fun x => coordinateP G (x,p.2)) p.1 (coordinateBasis i))
  rw [h]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_neg]

theorem hamiltonVector_scale (G : CoordinateSpace → Tensor2) (p : Phase) {t : ℝ} (ht : t ≠ 0) :
    hamiltonVector G (phaseScale t p) = t • phaseScale t (hamiltonVector G p) := by
  apply Prod.ext
  · exact hamiltonVector_base_scale G p ht
  · change (hamiltonVector G (phaseScale t p)).2 = t • (t • (hamiltonVector G p).2)
    rw [hamiltonVector_momentum_scale, smul_smul, pow_two]

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter Module
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase)

theorem basePartial_eq_component {F : Phase → ℝ} {p : Phase}
    (hF : DifferentiableAt ℝ F p) (i : Index) :
    basePartial F p i = fderiv ℝ F p (coordinateBasis i, 0) := by
  exact DFunLike.congr_fun (hF.hasFDerivAt.comp p.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).fderiv (coordinateBasis i)

theorem momentumPartial_eq_component {F : Phase → ℝ} {p : Phase}
    (hF : DifferentiableAt ℝ F p) (i : Index) :
    momentumPartial F p i = fderiv ℝ F p (0, Pi.single i 1) := by
  exact DFunLike.congr_fun (hF.hasFDerivAt.comp p.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv (Pi.single i 1)

private theorem apply_sum_coordinateBasis (D : CoordinateSpace →L[ℝ] ℝ)
    (w : CoordinateSpace) : D w = ∑ i, w i * D (coordinateBasis i) := by
  have hw := congrArg D (coordinateBasis.sum_repr w)
  simpa only [map_sum, map_smul, smul_eq_mul, coordinateBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr] using hw.symm

private theorem apply_sum_covectorBasis (D : Covector →L[ℝ] ℝ)
    (w : Covector) : D w = ∑ i, w i * D (Pi.single i 1) := by
  have hw := congrArg D ((Pi.basisFun ℝ Index).sum_repr w)
  simpa only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_repr, Pi.basisFun_apply] using hw.symm

/-- Evaluation of the ordinary phase-space derivative on the canonical Hamilton vector. -/
theorem fderiv_apply_hamiltonVector (G : CoordinateSpace → Tensor2) {F : Phase → ℝ} {p : Phase}
    (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (hamiltonVector G p) =
      ∑ i, (momentumPartial (coordinateP G) p i * basePartial F p i -
        basePartial (coordinateP G) p i * momentumPartial F p i) := by
  let D := fderiv ℝ F p
  let v := hamiltonVector G p
  have hv : v = (v.1, (0 : Covector)) + ((0 : CoordinateSpace), v.2) := by
    ext <;> simp
  have hL := apply_sum_coordinateBasis (D.comp (ContinuousLinearMap.inl ℝ CoordinateSpace Covector)) v.1
  have hR := apply_sum_covectorBasis (D.comp (ContinuousLinearMap.inr ℝ CoordinateSpace Covector)) v.2
  change D v = _
  rw [hv, map_add]
  change (D.comp (ContinuousLinearMap.inl ℝ CoordinateSpace Covector)) v.1 +
    (D.comp (ContinuousLinearMap.inr ℝ CoordinateSpace Covector)) v.2 = _
  rw [hL, hR, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change momentumPartial (coordinateP G) p i * D (coordinateBasis i, 0) +
    (-basePartial (coordinateP G) p i) * D (0, Pi.single i 1) = _
  rw [← basePartial_eq_component hF i, ← momentumPartial_eq_component hF i]
  ring

theorem fderiv_coordinateP_apply_hamiltonVector (G : CoordinateSpace → Tensor2) {p : Phase}
    (hP : DifferentiableAt ℝ (coordinateP G) p) :
    fderiv ℝ (coordinateP G) p (hamiltonVector G p) = 0 := by
  rw [fderiv_apply_hamiltonVector G hP]
  exact Finset.sum_eq_zero fun i _ => by ring

open Burnett.Geometry.ManifoldMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem contDiffOn_coordinateP_chartInverse
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (c : M) :
    ContDiffOn ℝ ∞ (coordinateP (UnitNullAngular.chartInverse g c))
      ((chartAt CoordinateSpace c).target ×ˢ (univ : Set Covector)) := by
  unfold coordinateP
  simp only [← UnitNullAngular.dualPair_self]
  exact
    (UnitNullAngular.contDiffOn_dualPair _ (UnitNullAngular.chartInverse_smooth g hg hgn c)
      (W := (chartAt CoordinateSpace c).target ×ˢ (univ : Set Covector))
      (fun (_ : Phase) hp => hp.1) contDiffOn_snd contDiffOn_snd).div_const 2

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The canonical momentum function is one half of genuine inverse-metric energy in this chart. -/
theorem coordinateP_cotangentChart (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (c : M) {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    coordinateP (chartInverse g c) (cotangentChart c p) = dualEnergy g hgn p / 2 := by
  rw [dualEnergy_chart g hgn hgs c p hp]
  rfl

def puncturedPhaseTarget (c : M) : Set Phase :=
  phaseTarget c ∩ {p | p.2 ≠ 0}

omit [IsManifold Model ∞ M] in
theorem isOpen_puncturedPhaseTarget (c : M) : IsOpen (puncturedPhaseTarget c) := by
  refine (isOpen_phaseTarget c).inter ?_
  exact (isClosed_singleton.preimage continuous_snd).isOpen_compl

omit [IsManifold Model ∞ M] in
theorem phaseScale_mem_puncturedPhaseTarget (c : M) {p : Phase} (hp : p ∈ puncturedPhaseTarget c)
    {t : ℝ} (ht : t ≠ 0) : phaseScale t p ∈ puncturedPhaseTarget c :=
  ⟨⟨hp.1.1, trivial⟩, smul_ne_zero ht hp.2⟩

theorem cotangentChart_scale (c : M) (t : ℝ) (p : CotangentBundle M) :
    cotangentChart c (cotangentScale t p) = phaseScale t (cotangentChart c p) := by
  simp only [cotangentChart, phaseScale_apply, cotangentScale_projection, cotangentScale_coords]

theorem cotangentChartInverse_mem_punctured {c : M} {p : Phase} (hp : p ∈ puncturedPhaseTarget c) :
    cotangentChartInverse c p ∈ puncturedCotangent := by
  intro h0
  have hz : cotangentCoords c (cotangentChartInverse c p) = 0 := by
    funext i
    simp [cotangentCoords, cotangentTrivialization_apply, h0]
  exact hp.2 ((congrArg Prod.snd (cotangentChart_right_inv c hp.1)).symm.trans hz)

def coordinateNorm (r : Metric (M := M)) (c : M) (p : Phase) : ℝ :=
  Real.sqrt (symbolNorm (chartInverse r.inner c p.1) p.2)

theorem coordinateNorm_cotangentChart (r : Metric (M := M)) (c : M)
    {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    coordinateNorm r c (cotangentChart c p) = cotangentNorm r p := by
  unfold cotangentNorm
  rw [dualEnergy_chart r.inner (GlobalLeviCivita.inner_nondegenerate r) r.symm c p hp]
  rfl

theorem coordinateNorm_pos (r : Metric (M := M)) (c : M) {p : Phase}
    (hp : p ∈ puncturedPhaseTarget c) : 0 < coordinateNorm r c p := by
  rw [← cotangentChart_right_inv c hp.1,
    coordinateNorm_cotangentChart r c (cotangentChartInverse_mapsTo c hp.1)]
  exact cotangentNorm_pos r (cotangentChartInverse_mem_punctured hp)

theorem coordinateNorm_scale (r : Metric (M := M)) (c : M) (p : Phase) {t : ℝ} (ht : 0 < t) :
    coordinateNorm r c (phaseScale t p) = t * coordinateNorm r c p := by
  simp only [coordinateNorm, phaseScale_apply, ← UnitNullAngular.dualPair_self,
    UnitNullAngular.dualPair_smul_self, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht]

theorem contDiffAt_coordinateNorm (r : Metric (M := M)) (c : M) {p : Phase}
    (hp : p ∈ puncturedPhaseTarget c) : ContDiffAt ℝ ∞ (coordinateNorm r c) p := by
  have hP := (contDiffOn_coordinateP_chartInverse r.inner (ManifoldBilinear.isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) c).contDiffAt ((isOpen_phaseTarget c).mem_nhds hp.1)
  let E : Phase → ℝ := fun q => 2 * coordinateP (chartInverse r.inner c) q
  have hE : ContDiffAt ℝ ∞ E p := contDiffAt_const.mul hP
  have hident (q : Phase) : E q = symbolNorm (chartInverse r.inner c q.1) q.2 := by
    unfold E coordinateP
    ring
  have hh : coordinateNorm r c = Real.sqrt ∘ E := funext (fun q => by simp [coordinateNorm, hident])
  have hnonzero : E p ≠ 0 := by
    intro h0
    have hz : coordinateNorm r c p = 0 := by rw [hh, Function.comp_apply, h0, Real.sqrt_zero]
    exact (coordinateNorm_pos r c hp).ne' hz
  rw [hh]
  exact (Real.contDiffAt_sqrt hnonzero).comp p hE

def coordinateNormalize (r : Metric (M := M)) (c : M) (p : Phase) : Phase :=
  phaseScale ((coordinateNorm r c p)⁻¹) p

theorem coordinateNormalize_cotangentChart (r : Metric (M := M)) (c : M)
    {p : CotangentBundle M} (hp : p ∈ cotangentSource c) :
    coordinateNormalize r c (cotangentChart c p) = cotangentChart c (cotangentNormalize r p) := by
  simp only [coordinateNormalize, coordinateNorm_cotangentChart r c hp,
    cotangentNormalize, cotangentChart_scale]

theorem coordinateNormalize_scale (r : Metric (M := M)) (c : M) (p : Phase)
    {t : ℝ} (ht : 0 < t) :
    coordinateNormalize r c (phaseScale t p) = coordinateNormalize r c p := by
  unfold coordinateNormalize
  rw [coordinateNorm_scale r c p ht]
  simp only [phaseScale_apply, smul_smul]
  have h : (t * coordinateNorm r c p)⁻¹ * t = (coordinateNorm r c p)⁻¹ := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
  rw [h]

theorem contDiffAt_coordinateNormalize (r : Metric (M := M)) (c : M) {p : Phase}
    (hp : p ∈ puncturedPhaseTarget c) : ContDiffAt ℝ ∞ (coordinateNormalize r c) p := by
  have hN := (contDiffAt_coordinateNorm r c hp).inv (coordinateNorm_pos r c hp).ne'
  exact contDiffAt_fst.prodMk (hN.smul contDiffAt_snd)

def radialCoefficient (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M)
    (p : Phase) : ℝ :=
  fderiv ℝ (coordinateNorm r c) p (hamiltonVector G p)

def angularVector (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M)
    (p : Phase) : Phase :=
  fderiv ℝ (coordinateNormalize r c) p (hamiltonVector G p)

theorem radialCoefficient_scale (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M)
    {p : Phase} (hp : p ∈ puncturedPhaseTarget c) {t : ℝ} (ht : 0 < t) :
    radialCoefficient G r c (phaseScale t p) = t^2 * radialCoefficient G r c p := by
  have hN := (contDiffAt_coordinateNorm r c (phaseScale_mem_puncturedPhaseTarget c hp ht.ne')).differentiableAt (by simp)
  have h := (hN.hasFDerivAt.comp p (phaseScale t).hasFDerivAt).fderiv
  have he : coordinateNorm r c ∘ phaseScale t = t • coordinateNorm r c :=
    funext (fun q => coordinateNorm_scale r c q ht)
  rw [he, fderiv_const_smul_of_field] at h
  change t • fderiv ℝ (coordinateNorm r c) p =
    (fderiv ℝ (coordinateNorm r c) (phaseScale t p)).comp (phaseScale t) at h
  have hv := congrArg (fun D : Phase →L[ℝ] ℝ => D (hamiltonVector G p)) h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul] at hv
  simp only [radialCoefficient, hamiltonVector_scale G p ht.ne', map_smul, smul_eq_mul, ← hv]
  ring

theorem angularVector_scale (G : CoordinateSpace → Tensor2) (r : Metric (M := M)) (c : M)
    {p : Phase} (hp : p ∈ puncturedPhaseTarget c) {t : ℝ} (ht : 0 < t) :
    angularVector G r c (phaseScale t p) = t • angularVector G r c p := by
  have hN := (contDiffAt_coordinateNormalize r c
    (phaseScale_mem_puncturedPhaseTarget c hp ht.ne')).differentiableAt (by simp)
  have h := (hN.hasFDerivAt.comp p (phaseScale t).hasFDerivAt).fderiv
  have he : coordinateNormalize r c ∘ phaseScale t = coordinateNormalize r c :=
    funext (fun q => coordinateNormalize_scale r c q ht)
  rw [he] at h
  have hv := congrArg (fun D : Phase →L[ℝ] Phase => D (hamiltonVector G p)) h
  simp only [ContinuousLinearMap.comp_apply] at hv
  simp only [angularVector, hamiltonVector_scale G p ht.ne', map_smul, ← hv]

theorem fderiv_radialChart_apply_hamiltonVector (G : CoordinateSpace → Tensor2)
    (r : Metric (M := M)) (c : M) {p : Phase} (hp : p ∈ puncturedPhaseTarget c)
    {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (fun q => (coordinateNorm r c q, coordinateNormalize r c q))
        (phaseScale t p) (hamiltonVector G (phaseScale t p)) =
      (t^2 * radialCoefficient G r c p, t • angularVector G r c p) := by
  have hs := phaseScale_mem_puncturedPhaseTarget c hp ht.ne'
  have hN := (contDiffAt_coordinateNorm r c hs).differentiableAt (by simp)
  have hA := (contDiffAt_coordinateNormalize r c hs).differentiableAt (by simp)
  rw [(hN.hasFDerivAt.prodMk hA.hasFDerivAt).fderiv]
  change (radialCoefficient G r c (phaseScale t p), angularVector G r c (phaseScale t p)) = _
  rw [radialCoefficient_scale G r c hp ht, angularVector_scale G r c hp ht]

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem coordinateNormalize_mem_puncturedPhaseTarget (r : Metric (M := M)) (c : M)
    {p : Phase} (hp : p ∈ puncturedPhaseTarget c) :
    coordinateNormalize r c p ∈ puncturedPhaseTarget c :=
  phaseScale_mem_puncturedPhaseTarget c hp (inv_ne_zero (coordinateNorm_pos r c hp).ne')

theorem coordinateNorm_coordinateNormalize (r : Metric (M := M)) (c : M)
    {p : Phase} (hp : p ∈ puncturedPhaseTarget c) :
    coordinateNorm r c (coordinateNormalize r c p) = 1 := by
  rw [coordinateNormalize, coordinateNorm_scale r c p (inv_pos.mpr (coordinateNorm_pos r c hp)),
    inv_mul_cancel₀ (coordinateNorm_pos r c hp).ne']

theorem coordinateNormalize_of_norm_one (r : Metric (M := M)) (c : M) {p : Phase}
    (hp : coordinateNorm r c p = 1) :
    coordinateNormalize r c p = p := by
  simp [coordinateNormalize, phaseScale_apply, hp]

theorem fderiv_coordinateNorm_apply_angularVector (G : CoordinateSpace → Tensor2)
    (r : Metric (M := M)) (c : M) {p : Phase} (hp : p ∈ puncturedPhaseTarget c) :
    fderiv ℝ (coordinateNorm r c) (coordinateNormalize r c p) (angularVector G r c p) = 0 := by
  have hA := (contDiffAt_coordinateNormalize r c hp).differentiableAt (by simp)
  have hN := (contDiffAt_coordinateNorm r c
    (coordinateNormalize_mem_puncturedPhaseTarget r c hp)).differentiableAt (by simp)
  have h := (hN.hasFDerivAt.comp p hA.hasFDerivAt).fderiv
  have hs : ∀ᶠ q in 𝓝 p, q ∈ puncturedPhaseTarget c :=
    (isOpen_puncturedPhaseTarget c).mem_nhds hp
  have he : (coordinateNorm r c ∘ coordinateNormalize r c) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) :=
    hs.mono fun _ hq => coordinateNorm_coordinateNormalize r c hq
  have hc : fderiv ℝ (fun _ : Phase => (1 : ℝ)) p = 0 := (hasFDerivAt_const (1 : ℝ) p).fderiv
  rw [he.fderiv_eq, hc] at h
  exact (congrArg (fun D : Phase →L[ℝ] ℝ => D (hamiltonVector G p)) h).symm

theorem coordinateP_coordinateNormalize (G : CoordinateSpace → Tensor2)
    (r : Metric (M := M)) (c : M) (p : Phase) :
    coordinateP G (coordinateNormalize r c p) =
      ((coordinateNorm r c p)⁻¹)^2 * coordinateP G p :=
  coordinateP_scale G p (coordinateNorm r c p)⁻¹

theorem fderiv_coordinateP_apply_angularVector
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (r : Metric (M := M)) (c : M)
    {p : Phase} (hp : p ∈ puncturedPhaseTarget c) (hn : coordinateP (chartInverse g c) p = 0) :
    fderiv ℝ (coordinateP (chartInverse g c)) (coordinateNormalize r c p)
      (angularVector (chartInverse g c) r c p) = 0 := by
  let G := chartInverse g c
  let P := coordinateP G
  let R := fun q => ((coordinateNorm r c q)⁻¹)^2
  have hA := (contDiffAt_coordinateNormalize r c hp).differentiableAt (by simp)
  have hPs := contDiffOn_coordinateP_chartInverse g hg hgn c
  have hP : DifferentiableAt ℝ P p := (hPs.contDiffAt ((isOpen_phaseTarget c).mem_nhds hp.1)).differentiableAt (by simp)
  have hPN : DifferentiableAt ℝ P (coordinateNormalize r c p) := (hPs.contDiffAt ((isOpen_phaseTarget c).mem_nhds
    (coordinateNormalize_mem_puncturedPhaseTarget r c hp).1)).differentiableAt (by simp)
  have hNi := (contDiffAt_coordinateNorm r c hp).inv (coordinateNorm_pos r c hp).ne'
  have hR : DifferentiableAt ℝ R p := (hNi.differentiableAt (by simp)).pow 2
  have h := (hPN.hasFDerivAt.comp p hA.hasFDerivAt).fderiv
  have he : P ∘ coordinateNormalize r c = R * P :=
    funext (coordinateP_coordinateNormalize G r c)
  change fderiv ℝ (P ∘ coordinateNormalize r c) p =
    (fderiv ℝ P (coordinateNormalize r c p)).comp (fderiv ℝ (coordinateNormalize r c) p) at h
  rw [he, (hR.hasFDerivAt.mul hP.hasFDerivAt).fderiv] at h
  have hv := congrArg (fun D : Phase →L[ℝ] ℝ => D (hamiltonVector G p)) h
  have hh := fderiv_coordinateP_apply_hamiltonVector G (p := p) hP
  change P p = 0 at hn
  change fderiv ℝ P p (hamiltonVector G p) = 0 at hh
  change fderiv ℝ P (coordinateNormalize r c p)
    ((fderiv ℝ (coordinateNormalize r c) p) (hamiltonVector G p)) = 0
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, hn, hh, zero_mul, mul_zero, zero_add]
    using hv.symm

/-- On the unit-null set, the angular component annihilates both defining differentials. -/
theorem angularVector_annihilates_unitNull_constraints
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (r : Metric (M := M)) (c : M)
    {p : Phase} (hp : p ∈ puncturedPhaseTarget c) (hu : coordinateNorm r c p = 1)
    (hn : coordinateP (chartInverse g c) p = 0) :
    fderiv ℝ (coordinateNorm r c) p (angularVector (chartInverse g c) r c p) = 0 ∧
      fderiv ℝ (coordinateP (chartInverse g c)) p (angularVector (chartInverse g c) r c p) = 0 := by
  have ha := coordinateNormalize_of_norm_one r c hu
  constructor
  · simpa only [ha] using fderiv_coordinateNorm_apply_angularVector (chartInverse g c) r c hp
  · simpa only [ha] using fderiv_coordinateP_apply_angularVector g hg hgn r c hp hn

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem contDiffOn_hamiltonVector_chartInverse
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (c : M) :
    ContDiffOn ℝ ∞ (hamiltonVector (chartInverse g c)) (phaseTarget c) := by
  let P := coordinateP (chartInverse g c)
  have hP : ContDiffOn ℝ ∞ P (phaseTarget c) := contDiffOn_coordinateP_chartInverse g hg hgn c
  have hD := hP.fderiv_of_isOpen (m := ∞) (isOpen_phaseTarget c) (by simp)
  have hd (p : Phase) (hp : p ∈ phaseTarget c) : DifferentiableAt ℝ P p :=
    (hP.contDiffAt ((isOpen_phaseTarget c).mem_nhds hp)).differentiableAt (by simp)
  have hbase (i : Index) : ContDiffOn ℝ ∞ (fun p => basePartial P p i) (phaseTarget c) :=
    (hD.clm_apply (contDiffOn_const (c := (coordinateBasis i, (0 : Covector))))).congr
      (fun p hp => basePartial_eq_component (hd p hp) i)
  have hmom (i : Index) : ContDiffOn ℝ ∞ (fun p => momentumPartial P p i) (phaseTarget c) :=
    (hD.clm_apply (contDiffOn_const (c := ((0 : CoordinateSpace), Pi.single i 1)))).congr
      (fun p hp => momentumPartial_eq_component (hd p hp) i)
  exact (contDiffOn_piLp' 2 hmom).prodMk (contDiffOn_pi.2 (fun i => (hbase i).neg))

theorem contDiffOn_radialCoefficient_chartInverse
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (r : Metric (M := M)) (c : M) :
    ContDiffOn ℝ ∞ (radialCoefficient (chartInverse g c) r c) (puncturedPhaseTarget c) := by
  have hN : ContDiffOn ℝ ∞ (coordinateNorm r c) (puncturedPhaseTarget c) :=
    fun _ hp => (contDiffAt_coordinateNorm r c hp).contDiffWithinAt
  exact (hN.fderiv_of_isOpen (isOpen_puncturedPhaseTarget c) (by simp)).clm_apply
    ((contDiffOn_hamiltonVector_chartInverse g hg hgn c).mono (fun _ hp => hp.1))

theorem contDiffOn_angularVector_chartInverse
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (r : Metric (M := M)) (c : M) :
    ContDiffOn ℝ ∞ (angularVector (chartInverse g c) r c) (puncturedPhaseTarget c) := by
  have hA : ContDiffOn ℝ ∞ (coordinateNormalize r c) (puncturedPhaseTarget c) :=
    fun _ hp => (contDiffAt_coordinateNormalize r c hp).contDiffWithinAt
  exact (hA.fderiv_of_isOpen (isOpen_puncturedPhaseTarget c) (by simp)).clm_apply
    ((contDiffOn_hamiltonVector_chartInverse g hg hgn c).mono (fun _ hp => hp.1))

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.RadialHamilton

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The radial-chart derivative of the inverse-metric Hamilton field on a genuine unit-null ray. -/
theorem actual_unitNull_hamilton_radial_chart
    (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (r : Metric (M := M)) (c : M) {p : CotangentBundle M}
    (hp : p ∈ cotangentSource c) (hu : p ∈ cotangentUnitNull r g hgn)
    {t : ℝ} (ht : 0 < t) :
    let q := cotangentChart c p
    let qt := cotangentChart c (cotangentScale t p)
    let G := chartInverse g c
    let Φ := fun z => (coordinateNorm r c z, coordinateNormalize r c z)
    Φ qt = (t, q) ∧
    fderiv ℝ Φ qt (hamiltonVector G qt) =
      (t^2 * radialCoefficient G r c q, t • angularVector G r c q) ∧
    fderiv ℝ (coordinateNorm r c) q (angularVector G r c q) = 0 ∧
    fderiv ℝ (coordinateP G) q (angularVector G r c q) = 0 := by
  dsimp only
  have hN : coordinateNorm r c (cotangentChart c p) = 1 := by
    rw [coordinateNorm_cotangentChart r c hp, cotangentNorm, hu.1, Real.sqrt_one]
  have hP : coordinateP (chartInverse g c) (cotangentChart c p) = 0 := by
    rw [coordinateP_cotangentChart g hgn hgs c hp, hu.2, zero_div]
  have hq : cotangentChart c p ∈ puncturedPhaseTarget c := by
    refine ⟨cotangentChart_mapsTo c hp, ?_⟩
    intro hξ
    have hzero : coordinateNorm r c (cotangentChart c p) = 0 := by
      simp [coordinateNorm, hξ, symbolNorm]
    exact one_ne_zero (hN.symm.trans hzero)
  rw [cotangentChart_scale]
  refine ⟨?_, fderiv_radialChart_apply_hamiltonVector _ r c hq ht,
    angularVector_annihilates_unitNull_constraints g hg hgn r c hq hN hP⟩
  simp only [coordinateNorm_scale r c _ ht, hN, mul_one,
    coordinateNormalize_scale r c _ ht, coordinateNormalize_of_norm_one r c hN]

end Burnett.Geometry.RadialHamilton

namespace Burnett.Geometry.CotangentHamiltonNaturality

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.ChartVolume
open Burnett.Geometry.ActualChartSecondJet Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem coordinatePairing_eq_actual (c : M) (p : CotangentBundle M) (v : CoordinateSpace) :
    (∑ i : Index, cotangentCoords c p i * v i) = (cotangentTrivialization c p).2 v := by
  have h := congrArg (fun z : CoordinateSpace => (cotangentTrivialization c p).2 z)
    (coordinateBasis.sum_repr v)
  simpa [map_sum, map_smul, smul_eq_mul, cotangentCoords, coordinateBasis,
    EuclideanSpace.basisFun_repr, mul_comm] using h

/-- The actual continuous-dual coordinate transition, obtained from genuine tangent frames. -/
theorem actual_covector_transition (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) (v : CoordinateSpace) :
    (cotangentTrivialization c p).2 v =
      (cotangentTrivialization d p).2
        (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c p.1) v) := by
  rw [cotangentTrivialization_apply, cotangentTrivialization_apply]
  exact congrArg p.2 (tangentFrame_change c d p.1 hc hd v)

theorem actual_covector_transition_matrix (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) :
    cotangentCoords c p =
      (derivativeMatrix (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c p.1)))ᵀ *ᵥ
        cotangentCoords d p := by
  funext i
  change (cotangentTrivialization c p).2 (coordinateBasis i) = _
  rw [actual_covector_transition c d p hc hd, ← coordinatePairing_eq_actual]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    MetricJetNaturality.derivativeMatrix_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The actual chart transition on the real cotangent bundle. -/
def cotangentTransition (c d : M) (z : Phase) : Phase :=
  cotangentChart d (cotangentChartInverse c z)

def transitionSource (c d : M) : Set Phase :=
  {z | z.1 ∈ (chartTransition c d).source}

theorem cotangentTransition_fst (c d : M) (z : Phase) :
    (cotangentTransition c d z).1 = chartTransition c d z.1 := rfl

omit [IsManifold Model ∞ M] in
theorem transitionSource_isOpen (c d : M) : IsOpen (transitionSource c d) :=
  (chartTransition c d).open_source.preimage continuous_fst

theorem cotangentTransition_chart (c d : M) (p : CotangentBundle M)
    (hc : p ∈ cotangentSource c) :
    cotangentTransition c d (cotangentChart c p) = cotangentChart d p := by
  rw [cotangentTransition, cotangentChart_left_inv c hc]

theorem chart_mem_transitionSource (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) :
    cotangentChart c p ∈ transitionSource c d := by
  change chartAt CoordinateSpace c p.1 ∈ (chartAt CoordinateSpace c).symm.source ∩
    (chartAt CoordinateSpace c).symm ⁻¹' (chartAt CoordinateSpace d).source
  exact ⟨(chartAt CoordinateSpace c).mapsTo hc, by
    simpa only [mem_preimage, (chartAt CoordinateSpace c).left_inv hc] using hd⟩

theorem cotangentTransition_contDiffOn (c d : M) :
    ContDiffOn ℝ ∞ (cotangentTransition c d) (transitionSource c d) := by
  have hi : ContMDiffOn CoordinatePhaseModel CotangentModelWithCorners ∞
      (cotangentChartInverse c) (transitionSource c d) :=
    (contMDiffOn_cotangentChartInverse c).mono (fun _ hz => ⟨hz.1, trivial⟩)
  have hm : MapsTo (cotangentChartInverse c) (transitionSource c d) (cotangentSource d) := by
    intro z hz
    exact hz.2
  have h := (contMDiffOn_cotangentChart d).comp hi hm
  simp only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffOn

theorem cotangentTransition_fderiv_fst (c d : M) (z : Phase) (hz : z ∈ transitionSource c d)
    (V : Phase) :
    (fderiv ℝ (cotangentTransition c d) z V).1 =
      fderiv ℝ (chartTransition c d) z.1 V.1 := by
  have hΦ : DifferentiableAt ℝ (cotangentTransition c d) z :=
    ((cotangentTransition_contDiffOn c d).contDiffAt
      ((transitionSource_isOpen c d).mem_nhds hz)).differentiableAt (by simp)
  have hφ : DifferentiableAt ℝ (chartTransition c d) z.1 :=
    ((contDiffOn_chartTransition_infty c d).contDiffAt
      ((chartTransition c d).open_source.mem_nhds hz)).differentiableAt (by simp)
  have hb : HasFDerivAt (fun w : Phase => (cotangentTransition c d w).1)
      ((fderiv ℝ (chartTransition c d) z.1).comp (ContinuousLinearMap.fst ℝ CoordinateSpace Covector)) z := by
    exact hφ.hasFDerivAt.comp z hasFDerivAt_fst
  exact congrArg (fun L : Phase →L[ℝ] CoordinateSpace => L V) (hΦ.hasFDerivAt.fst.unique hb)

/-- The coordinate expression of the canonical Liouville pairing ξ·δx. -/
def canonicalPairing (z V : Phase) : ℝ := ∑ i : Index, z.2 i * V.1 i

theorem canonicalPairing_chart (c : M) (p : CotangentBundle M) (V : Phase) :
    canonicalPairing (cotangentChart c p) V = (cotangentTrivialization c p).2 V.1 :=
  coordinatePairing_eq_actual c p V.1

/-- Actual cotangent chart changes preserve the canonical Liouville pairing on their true derivative. -/
theorem canonicalPairing_actual_transition (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) (V : Phase) :
    canonicalPairing (cotangentChart d p)
      (fderiv ℝ (cotangentTransition c d) (cotangentChart c p) V) =
        canonicalPairing (cotangentChart c p) V := by
  rw [canonicalPairing_chart, canonicalPairing_chart,
    cotangentTransition_fderiv_fst c d _ (chart_mem_transitionSource c d p hc hd)]
  exact (actual_covector_transition c d p hc hd V.1).symm

theorem coordinateP_actual_chart_compatible (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) :
    coordinateP (chartInverse g d) (cotangentChart d p) =
      coordinateP (chartInverse g c) (cotangentChart c p) := by
  rw [coordinateP_cotangentChart g hgn hgs d hd,
    coordinateP_cotangentChart g hgn hgs c hc]

end Burnett.Geometry.CotangentHamiltonNaturality

namespace Burnett.Geometry.CotangentSymplecticTransition

open Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_liouville_pullback (B : E →L[ℝ] E →L[ℝ] ℝ) (Φ : E → E) (x : E)
    (hΦ : DifferentiableAt ℝ Φ x) (hD : DifferentiableAt ℝ (fderiv ℝ Φ) x) (u v : E) :
    fderiv ℝ (fun y => B (Φ y) (fderiv ℝ Φ y v)) x u =
      B (fderiv ℝ Φ x u) (fderiv ℝ Φ x v) + B (Φ x) (fderiv ℝ (fderiv ℝ Φ) x u v) := by
  have hB : DifferentiableAt ℝ (fun y => B (Φ y)) x := B.differentiableAt.comp x hΦ
  have hv : DifferentiableAt ℝ (fun y => fderiv ℝ Φ y v) x := hD.clm_apply (differentiableAt_const v)
  rw [fderiv_clm_apply hB hv, fderiv_clm_apply hD (differentiableAt_const v)]
  have hb : fderiv ℝ (fun y => B (Φ y)) x = B.comp (fderiv ℝ Φ x) :=
    (B.hasFDerivAt.comp x hΦ.hasFDerivAt).fderiv
  rw [hb]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [fderiv_const_apply]
  simp only [ContinuousLinearMap.zero_apply, map_zero, zero_add]
  ring

/-- Differentiating a local Liouville identity and using actual Schwarz symmetry gives
preservation of the antisymmetrized bilinear form. -/
theorem liouville_identity_implies_symplectic
    (B : E →L[ℝ] E →L[ℝ] ℝ) (Φ : E → E) (x : E)
    (hΦ : ContDiffAt ℝ 2 Φ x)
    (hLiouville : ∀ v : E, (fun y => B (Φ y) (fderiv ℝ Φ y v)) =ᶠ[𝓝 x] fun y => B y v)
    (u v : E) :
    B (fderiv ℝ Φ x u) (fderiv ℝ Φ x v) - B (fderiv ℝ Φ x v) (fderiv ℝ Φ x u) =
      B u v - B v u := by
  have hd : DifferentiableAt ℝ Φ x := hΦ.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have he (u v : E) :
      B (fderiv ℝ Φ x u) (fderiv ℝ Φ x v) + B (Φ x) (fderiv ℝ (fderiv ℝ Φ) x u v) = B u v := by
    calc
      _ = fderiv ℝ (fun y => B (Φ y) (fderiv ℝ Φ y v)) x u :=
        (fderiv_liouville_pullback B Φ x hd hD u v).symm
      _ = fderiv ℝ (fun y => B y v) x u :=
        congrArg (fun D : E →L[ℝ] ℝ => D u) (hLiouville v).fderiv_eq
      _ = B u v := by
        exact congrArg (fun D : E →L[ℝ] ℝ => D u) (B.flip v).fderiv
  have huv := he u v
  have hvu := he v u
  have hs := hΦ.isSymmSndFDerivAt (by norm_num)
  rw [hs.eq v u] at hvu
  linarith

end Burnett.Geometry.CotangentSymplecticTransition

namespace Burnett.Geometry.CotangentSymplecticTransition

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.ChartVolume
open Burnett.Geometry.ActualChartSecondJet Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentHamiltonNaturality

/-- The continuous bilinear form whose evaluation is the local Liouville pairing. -/
def canonicalBilinear : Phase →L[ℝ] Phase →L[ℝ] ℝ :=
  ∑ i : Index,
    ((ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ CoordinateSpace Covector)).smulRight
      ((EuclideanSpace.proj i : CoordinateSpace →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ CoordinateSpace Covector))

theorem canonicalBilinear_apply (z V : Phase) : canonicalBilinear z V = canonicalPairing z V := by
  simp [canonicalBilinear, canonicalPairing, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]

/-- Canonical symplectic form, with the Hamilton convention i_H ω = dP. -/
def canonicalSymplectic (U V : Phase) : ℝ := canonicalBilinear V U - canonicalBilinear U V

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem actual_liouville_identity_on_overlap (c d : M) (z : Phase)
    (hz : z ∈ transitionSource c d) (V : Phase) :
    canonicalBilinear (cotangentTransition c d z) (fderiv ℝ (cotangentTransition c d) z V) =
      canonicalBilinear z V := by
  simp only [canonicalBilinear_apply]
  let p := cotangentChartInverse c z
  have hc : p.1 ∈ (chartAt CoordinateSpace c).source :=
    cotangentChartInverse_mapsTo c ⟨hz.1, trivial⟩
  have hd : p.1 ∈ (chartAt CoordinateSpace d).source := hz.2
  have he : cotangentChart c p = z := cotangentChart_right_inv c ⟨hz.1, trivial⟩
  have h := canonicalPairing_actual_transition c d p hc hd V
  rw [he] at h
  exact h

theorem actual_cotangentTransition_symplectic (c d : M) (z : Phase)
    (hz : z ∈ transitionSource c d) (U V : Phase) :
    canonicalSymplectic (fderiv ℝ (cotangentTransition c d) z U)
      (fderiv ℝ (cotangentTransition c d) z V) = canonicalSymplectic U V := by
  have hC : ContDiffAt ℝ 2 (cotangentTransition c d) z :=
    ((cotangentTransition_contDiffOn c d).contDiffAt
      ((transitionSource_isOpen c d).mem_nhds hz)).of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hL (W : Phase) :
      (fun y => canonicalBilinear (cotangentTransition c d y)
        (fderiv ℝ (cotangentTransition c d) y W)) =ᶠ[𝓝 z] fun y => canonicalBilinear y W := by
    filter_upwards [(transitionSource_isOpen c d).mem_nhds hz] with y hy
    exact actual_liouville_identity_on_overlap c d y hy W
  exact liouville_identity_implies_symplectic canonicalBilinear (cotangentTransition c d) z hC hL V U

theorem actual_cotangentTransition_mapsTo (c d : M) (z : Phase) (hz : z ∈ transitionSource c d) :
    cotangentTransition c d z ∈ transitionSource d c := by
  have hc : (cotangentChartInverse c z).1 ∈ (chartAt CoordinateSpace c).source :=
    cotangentChartInverse_mapsTo c ⟨hz.1, trivial⟩
  exact chart_mem_transitionSource d c (cotangentChartInverse c z) hz.2 hc

theorem actual_cotangentTransition_inverse (c d : M) (z : Phase) (hz : z ∈ transitionSource c d) :
    cotangentTransition d c (cotangentTransition c d z) = z := by
  unfold cotangentTransition
  rw [cotangentChart_left_inv d hz.2]
  exact cotangentChart_right_inv c ⟨hz.1, trivial⟩

theorem actual_cotangentTransition_derivative_inverse (c d : M) (z : Phase)
    (hz : z ∈ transitionSource c d) :
    (fderiv ℝ (cotangentTransition d c) (cotangentTransition c d z)).comp
      (fderiv ℝ (cotangentTransition c d) z) = ContinuousLinearMap.id ℝ Phase := by
  have hD : DifferentiableAt ℝ (cotangentTransition c d) z :=
    ((cotangentTransition_contDiffOn c d).contDiffAt
      ((transitionSource_isOpen c d).mem_nhds hz)).differentiableAt (by simp)
  have hI : DifferentiableAt ℝ (cotangentTransition d c) (cotangentTransition c d z) :=
    ((cotangentTransition_contDiffOn d c).contDiffAt
      ((transitionSource_isOpen d c).mem_nhds (actual_cotangentTransition_mapsTo c d z hz))).differentiableAt (by simp)
  have he : (cotangentTransition d c ∘ cotangentTransition c d) =ᶠ[𝓝 z] id := by
    filter_upwards [(transitionSource_isOpen c d).mem_nhds hz] with y hy
    exact actual_cotangentTransition_inverse c d y hy
  rw [← fderiv_comp z hI hD, he.fderiv_eq, fderiv_id]

theorem actual_cotangentTransition_derivative_surjective (c d : M) (z : Phase)
    (hz : z ∈ transitionSource c d) : Function.Surjective (fderiv ℝ (cotangentTransition c d) z) := by
  have hinj : Function.Injective (fderiv ℝ (cotangentTransition c d) z) := by
    intro U V h
    have hh := congrArg (fderiv ℝ (cotangentTransition d c) (cotangentTransition c d z)) h
    simpa only [← ContinuousLinearMap.comp_apply, actual_cotangentTransition_derivative_inverse c d z hz,
      ContinuousLinearMap.id_apply] using hh
  exact LinearMap.surjective_of_injective (f := (fderiv ℝ (cotangentTransition c d) z).toLinearMap) hinj

end Burnett.Geometry.CotangentSymplecticTransition

namespace Burnett.Geometry.CotangentSymplecticTransition

open Set Filter Bundle Matrix Module
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.ChartVolume
open Burnett.Geometry.ActualChartSecondJet Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentHamiltonNaturality

theorem canonicalSymplectic_formula (U V : Phase) :
    canonicalSymplectic U V = ∑ i : Index, (V.2 i * U.1 i - U.2 i * V.1 i) := by
  simp only [canonicalSymplectic, canonicalBilinear_apply, canonicalPairing, Finset.sum_sub_distrib]

theorem canonicalSymplectic_sub_left (U V W : Phase) :
    canonicalSymplectic (U - V) W = canonicalSymplectic U W - canonicalSymplectic V W := by
  simp only [canonicalSymplectic, map_sub, ContinuousLinearMap.sub_apply]
  ring

theorem canonicalSymplectic_nondegenerate (U : Phase)
    (hU : ∀ V : Phase, canonicalSymplectic U V = 0) : U = 0 := by
  have hx : U.1 = 0 := by
    ext i
    have h := hU ((0 : CoordinateSpace), Pi.single i 1)
    simpa [canonicalSymplectic_formula, Pi.single_apply] using h
  have hξ : U.2 = 0 := by
    ext i
    have h := hU (coordinateBasis i, (0 : Covector))
    simpa [canonicalSymplectic_formula, coordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply] using h
  exact Prod.ext hx hξ

theorem phase_linear_decomposition (D : Phase →L[ℝ] ℝ) (V : Phase) :
    D V = (∑ i : Index, V.1 i * D (coordinateBasis i, 0)) +
      ∑ i : Index, V.2 i * D (0, Pi.single i 1) := by
  have hL : D (V.1, 0) = ∑ i : Index, V.1 i * D (coordinateBasis i, 0) := by
    have h := congrArg (D.comp (ContinuousLinearMap.inl ℝ CoordinateSpace Covector))
      (coordinateBasis.sum_repr V.1)
    simpa only [map_sum, map_smul, smul_eq_mul, coordinateBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr] using h.symm
  have hR : D (0, V.2) = ∑ i : Index, V.2 i * D (0, Pi.single i 1) := by
    have h := congrArg (D.comp (ContinuousLinearMap.inr ℝ CoordinateSpace Covector))
      ((Pi.basisFun ℝ Index).sum_repr V.2)
    simpa only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_repr, Pi.basisFun_apply] using h.symm
  calc
    _ = D (V.1, 0) + D (0, V.2) := by rw [← map_add]; congr 1; ext <;> simp
    _ = _ := by rw [hL, hR]

theorem canonicalSymplectic_hamiltonVector (G : CoordinateSpace → Tensor2) (z V : Phase)
    (hP : DifferentiableAt ℝ (coordinateP G) z) :
    canonicalSymplectic (hamiltonVector G z) V = fderiv ℝ (coordinateP G) z V := by
  rw [canonicalSymplectic_formula, phase_linear_decomposition]
  simp only [← basePartial_eq_component hP, ← momentumPartial_eq_component hP]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change V.2 i * momentumPartial (coordinateP G) z i -
    (-basePartial (coordinateP G) z i) * V.1 i =
      V.1 i * basePartial (coordinateP G) z i + V.2 i * momentumPartial (coordinateP G) z i
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem actual_coordinateP_transition (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (hgs : ManifoldBilinear.IsSymmetric g)
    (c d : M) (z : Phase) (hz : z ∈ transitionSource c d) :
    coordinateP (chartInverse g d) (cotangentTransition c d z) = coordinateP (chartInverse g c) z := by
  let p := cotangentChartInverse c z
  have hc : p.1 ∈ (chartAt CoordinateSpace c).source :=
    cotangentChartInverse_mapsTo c ⟨hz.1, trivial⟩
  have hd : p.1 ∈ (chartAt CoordinateSpace d).source := hz.2
  have he : cotangentChart c p = z := cotangentChart_right_inv c ⟨hz.1, trivial⟩
  have h := coordinateP_actual_chart_compatible g hgn hgs c d p hc hd
  rw [he] at h
  exact h

/-- Canonical Hamilton vector fields for the same actual metric transform by the actual derivative
of the actual cotangent chart change. -/
theorem actual_hamiltonVector_transition (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c d : M) (z : Phase) (hz : z ∈ transitionSource c d) :
    fderiv ℝ (cotangentTransition c d) z (hamiltonVector (chartInverse g c) z) =
      hamiltonVector (chartInverse g d) (cotangentTransition c d z) := by
  let Φ := cotangentTransition c d
  let A := fderiv ℝ Φ z
  have hD : DifferentiableAt ℝ Φ z :=
    ((cotangentTransition_contDiffOn c d).contDiffAt
      ((transitionSource_isOpen c d).mem_nhds hz)).differentiableAt (by simp)
  have hPc : DifferentiableAt ℝ (coordinateP (chartInverse g c)) z :=
    ((contDiffOn_coordinateP_chartInverse g hg hgn c).contDiffAt
      ((isOpen_phaseTarget c).mem_nhds ⟨hz.1, trivial⟩)).differentiableAt (by simp)
  have hPd : DifferentiableAt ℝ (coordinateP (chartInverse g d)) (Φ z) :=
    ((contDiffOn_coordinateP_chartInverse g hg hgn d).contDiffAt
      ((isOpen_phaseTarget d).mem_nhds
        ⟨(actual_cotangentTransition_mapsTo c d z hz).1, trivial⟩)).differentiableAt (by simp)
  have he : (coordinateP (chartInverse g d) ∘ Φ) =ᶠ[𝓝 z] coordinateP (chartInverse g c) := by
    filter_upwards [(transitionSource_isOpen c d).mem_nhds hz] with y hy
    exact actual_coordinateP_transition g hgn hgs c d y hy
  have hchain : (fderiv ℝ (coordinateP (chartInverse g d)) (Φ z)).comp A =
      fderiv ℝ (coordinateP (chartInverse g c)) z := by
    rw [← fderiv_comp z hPd hD, he.fderiv_eq]
  apply sub_eq_zero.mp
  apply canonicalSymplectic_nondegenerate
  intro W
  obtain ⟨V, rfl⟩ := actual_cotangentTransition_derivative_surjective c d z hz W
  rw [canonicalSymplectic_sub_left, actual_cotangentTransition_symplectic c d z hz,
    canonicalSymplectic_hamiltonVector _ _ _ hPc, canonicalSymplectic_hamiltonVector _ _ _ hPd]
  have hh := congrArg (fun L : Phase →L[ℝ] ℝ => L V) hchain
  change _ = _ at hh
  exact sub_eq_zero.mpr hh.symm

theorem actual_hamiltonVector_chart_compatible (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c d : M) (p : CotangentBundle M)
    (hc : p.1 ∈ (chartAt CoordinateSpace c).source)
    (hd : p.1 ∈ (chartAt CoordinateSpace d).source) :
    fderiv ℝ (cotangentTransition c d) (cotangentChart c p)
      (hamiltonVector (chartInverse g c) (cotangentChart c p)) =
        hamiltonVector (chartInverse g d) (cotangentChart d p) := by
  have h := actual_hamiltonVector_transition g hg hgn hgs c d (cotangentChart c p)
    (chart_mem_transitionSource c d p hc hd)
  rw [cotangentTransition_chart c d p hc] at h
  exact h

end Burnett.Geometry.CotangentSymplecticTransition
