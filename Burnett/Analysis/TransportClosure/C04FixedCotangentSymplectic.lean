import Burnett.Geometry.Cotangent.HamiltonianCoordinates
import Burnett.Geometry.Cotangent.FixedChartNaturality

/-! The canonical symplectic form for the actual fixed-atlas cotangent transitions. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FixedCotangentChart

open Bundle Filter Set
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.MaximalChart
open Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentSymplecticTransition
open scoped ContDiff Manifold Topology BigOperators

open private covectorCLM_basis_values from Burnett.Geometry.Cotangent.FixedChartNaturality

/-- The Liouville pairing is the cotangent part of the point evaluated on the base
part of the direction. -/
def phaseBilinear : Phase →L[ℝ] Phase →L[ℝ] ℝ :=
  ∑ i : Index,
    ((ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ CoordinateSpace Covector)).smulRight
      ((EuclideanSpace.proj i : CoordinateSpace →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ CoordinateSpace Covector))

theorem phaseBilinear_apply (z V : Phase) : phaseBilinear z V = covectorCLM z.2 V.1 := by
  simp [phaseBilinear, covectorCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]

/-- In the sign convention of the paper's Hamilton field, this is
`V.2 (U.1) - U.2 (V.1)` as a sum over the coordinate basis. -/
def phaseSymplectic (U V : Phase) : ℝ :=
  phaseBilinear V U - phaseBilinear U V

theorem phaseSymplectic_apply (U V : Phase) :
    phaseSymplectic U V = (∑ i : Index, V.2 i * U.1 i) -
      (∑ i : Index, U.2 i * V.1 i) := by
  simp [phaseSymplectic, phaseBilinear_apply, covectorCLM, ContinuousLinearMap.sum_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem transitionReverse (c d : AtlasChart M) :
    (c.transition d).symm = d.transition c := by
  simp only [AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

theorem fixedPhaseTransition_mapsTo_overlap (c d : AtlasChart M) :
    MapsTo (fixedPhaseTransition c d) (phaseOverlap c d) (phaseOverlap d c) := by
  intro z hz
  change (c.transition d) z.1 ∈ (d.transition c).source
  rw [← transitionReverse c d]
  exact (c.transition d).mapsTo hz

/-- Smoothness on the actual overlap, with the backward Jacobian evaluated at the
forward base point. -/
theorem contDiffOn_fixedPhaseTransition (c d : AtlasChart M) :
    ContDiffOn ℝ ∞ (fixedPhaseTransition c d) (phaseOverlap c d) := by
  let U := phaseOverlap c d
  let e := c.transition d
  let e' := d.transition c
  have hbase : ContDiffOn ℝ ∞ (fun z : Phase => e z.1) U :=
    (c.smooth_transition d).comp contDiff_fst.contDiffOn (fun _ hz => hz)
  have hderiv : ContDiffOn ℝ ∞ (fderiv ℝ e') e'.source :=
    (d.smooth_transition c).fderiv_of_isOpen e'.open_source (by simp)
  have hD : ContDiffOn ℝ ∞ (fun z : Phase => fderiv ℝ e' (e z.1)) U :=
    hderiv.comp hbase (fixedPhaseTransition_mapsTo_overlap c d)
  have hcov : ContDiff ℝ ∞ covectorCLM := by
    unfold covectorCLM
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).smul contDiff_const
  apply hbase.prodMk
  apply contDiffOn_pi.mpr
  intro i
  exact (hcov.comp contDiff_snd).contDiffOn.clm_apply
    (hD.clm_apply contDiff_const.contDiffOn)

theorem fixedPhaseTransition_fderiv_fst (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) (V : Phase) :
    (fderiv ℝ (fixedPhaseTransition c d) z V).1 = fderiv ℝ (c.transition d) z.1 V.1 := by
  have hΦ : DifferentiableAt ℝ (fixedPhaseTransition c d) z :=
    ((contDiffOn_fixedPhaseTransition c d).contDiffAt
      ((isOpen_phaseOverlap c d).mem_nhds hz)).differentiableAt (by simp)
  have hφ : DifferentiableAt ℝ (c.transition d) z.1 :=
    ((c.smooth_transition d).contDiffAt
      ((c.transition d).open_source.mem_nhds hz)).differentiableAt (by simp)
  have hb : HasFDerivAt (fun y : Phase => (fixedPhaseTransition c d y).1)
      ((fderiv ℝ (c.transition d) z.1).comp
        (ContinuousLinearMap.fst ℝ CoordinateSpace Covector)) z :=
    hφ.hasFDerivAt.comp z hasFDerivAt_fst
  exact DFunLike.congr_fun (hΦ.hasFDerivAt.fst.unique hb) V

theorem covectorCLM_fixedPhaseTransition_snd (c d : AtlasChart M) (z : Phase) :
    covectorCLM (fixedPhaseTransition c d z).2 =
      (covectorCLM z.2).comp (fderiv ℝ (d.transition c) ((c.transition d) z.1)) :=
  covectorCLM_basis_values ((covectorCLM z.2).comp
    (fderiv ℝ (d.transition c) ((c.transition d) z.1)))

theorem fixedPhaseTransition_liouville (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) (V : Phase) :
    phaseBilinear (fixedPhaseTransition c d z) (fderiv ℝ (fixedPhaseTransition c d) z V) =
      phaseBilinear z V := by
  rw [phaseBilinear_apply, phaseBilinear_apply, covectorCLM_fixedPhaseTransition_snd,
    fixedPhaseTransition_fderiv_fst c d z hz V]
  have h := DFunLike.congr_fun (chartTransition_fderiv_leftInverse c d (x := z.1) hz) V.1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  simp only [ContinuousLinearMap.comp_apply, h]

/-- The actual cotangent transition of any two compatible fixed charts preserves the
canonical symplectic form at every point of their open overlap. -/
theorem fixedPhaseTransition_symplectic (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) (U V : Phase) :
    phaseSymplectic (fderiv ℝ (fixedPhaseTransition c d) z U)
      (fderiv ℝ (fixedPhaseTransition c d) z V) = phaseSymplectic U V := by
  have hC : ContDiffAt ℝ 2 (fixedPhaseTransition c d) z :=
    ((contDiffOn_fixedPhaseTransition c d).contDiffAt
      ((isOpen_phaseOverlap c d).mem_nhds hz)).of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hL (W : Phase) :
      (fun y => phaseBilinear (fixedPhaseTransition c d y)
        (fderiv ℝ (fixedPhaseTransition c d) y W)) =ᶠ[𝓝 z] fun y => phaseBilinear y W := by
    filter_upwards [(isOpen_phaseOverlap c d).mem_nhds hz] with y hy
    exact fixedPhaseTransition_liouville c d y hy W
  exact liouville_identity_implies_symplectic phaseBilinear (fixedPhaseTransition c d) z hC hL V U

/-- The reverse lift is the actual local inverse, on the same overlap. -/
theorem fixedPhaseTransition_inverse (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) :
    fixedPhaseTransition d c (fixedPhaseTransition c d z) = z := by
  have hBase : d.transition c ((c.transition d) z.1) = z.1 := by
    rw [← transitionReverse c d]
    exact (c.transition d).left_inv hz
  apply Prod.ext hBase
  have hCLM : covectorCLM (fixedPhaseTransition d c (fixedPhaseTransition c d z)).2 =
      covectorCLM z.2 := by
    rw [covectorCLM_fixedPhaseTransition_snd, covectorCLM_fixedPhaseTransition_snd]
    change ((covectorCLM z.2).comp (fderiv ℝ (d.transition c) ((c.transition d) z.1))).comp
      (fderiv ℝ (c.transition d) ((d.transition c) ((c.transition d) z.1))) = _
    rw [hBase]
    apply ContinuousLinearMap.ext
    intro v
    have h := DFunLike.congr_fun (chartTransition_fderiv_leftInverse c d (x := z.1) hz) v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    simp only [ContinuousLinearMap.comp_apply, h]
  funext i
  simpa only [covectorCLM_apply_basis] using DFunLike.congr_fun hCLM (coordinateBasis i)

theorem fixedPhaseTransition_fderiv_leftInverse (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) :
    (fderiv ℝ (fixedPhaseTransition d c) (fixedPhaseTransition c d z)).comp
      (fderiv ℝ (fixedPhaseTransition c d) z) = ContinuousLinearMap.id ℝ Phase := by
  have hD : DifferentiableAt ℝ (fixedPhaseTransition c d) z :=
    ((contDiffOn_fixedPhaseTransition c d).contDiffAt
      ((isOpen_phaseOverlap c d).mem_nhds hz)).differentiableAt (by simp)
  have hr := fixedPhaseTransition_mapsTo_overlap c d hz
  have hI : DifferentiableAt ℝ (fixedPhaseTransition d c) (fixedPhaseTransition c d z) :=
    ((contDiffOn_fixedPhaseTransition d c).contDiffAt
      ((isOpen_phaseOverlap d c).mem_nhds hr)).differentiableAt (by simp)
  have he : (fixedPhaseTransition d c ∘ fixedPhaseTransition c d) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_phaseOverlap c d).mem_nhds hz] with y hy
    exact fixedPhaseTransition_inverse c d y hy
  rw [← fderiv_comp z hI hD, he.fderiv_eq, fderiv_id]

theorem fixedPhaseTransition_fderiv_surjective (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) :
    Function.Surjective (fderiv ℝ (fixedPhaseTransition c d) z) := by
  intro V
  refine ⟨fderiv ℝ (fixedPhaseTransition d c) (fixedPhaseTransition c d z) V, ?_⟩
  have h := fixedPhaseTransition_fderiv_leftInverse d c (fixedPhaseTransition c d z)
    (fixedPhaseTransition_mapsTo_overlap c d hz)
  rw [fixedPhaseTransition_inverse c d z hz] at h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun h V

variable [IsManifold Model ∞ M]

/-- Symplectic comparison centered at the coordinates of a single geometric cotangent
point, with the target point identified in its own actual fixed chart. -/
theorem fixedChartPhase_symplectic (c d : AtlasChart M) (p : CotangentBundle M)
    (hc : p.proj ∈ c.chart.source) (hd : p.proj ∈ d.chart.source) (U V : Phase) :
    fixedPhaseTransition c d (fixedChartPhase c p) = fixedChartPhase d p ∧
      phaseSymplectic (fderiv ℝ (fixedPhaseTransition c d) (fixedChartPhase c p) U)
        (fderiv ℝ (fixedPhaseTransition c d) (fixedChartPhase c p) V) =
          phaseSymplectic U V :=
  ⟨fixedPhaseTransition_fixedChartPhase c d p hc hd,
    fixedPhaseTransition_symplectic c d (fixedChartPhase c p)
      (fixedChartPhase_mem_overlap c d p hc hd) U V⟩

end Burnett.Geometry.FixedCotangentChart
