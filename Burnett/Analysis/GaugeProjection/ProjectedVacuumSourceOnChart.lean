import Burnett.Analysis.GaugeProjection.ProjectedLocalizedSourceL2
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Burnett.Analysis.GaugeProjection.LocalizedMetricSchwartzInputs

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open Burnett.A07 (coordinateDerivative)
open MeasureTheory Set
open scoped BigOperators ContDiff


private theorem partial_smooth (f : CoordinateSpace → ℝ) (a : Index)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarPartial f a) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem partial_tsupport (f : CoordinateSpace → ℝ) (a : Index) :
    tsupport (scalarPartial f a) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply support_fderiv_subset ℝ
  intro hz
  apply hx
  simp [scalarPartial, hz]

private theorem compact_of_tsupport_subset {f : CoordinateSpace → ℝ}
    {K : Set CoordinateSpace} (hK : IsCompact K) (h : tsupport f ⊆ K) :
    HasCompactSupport f := hK.of_isClosed_subset isClosed_closure h

private def complexCompactSchwartz (f : CoordinateSpace → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : SchwartzMap CoordinateSpace ℂ :=
  (hc.mono' (by
    intro x hx
    apply subset_tsupport f
    intro h
    simp [h] at hx)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hf)

private theorem complexCompactSchwartz_partial (f : CoordinateSpace → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (a : Index) (x : CoordinateSpace) :
    coordinateDerivative a (complexCompactSchwartz f hf hc) x = (scalarPartial f a x : ℂ) := by
  rw [coordinateDerivative, SchwartzMap.pderivCLM_apply]
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x
    (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y : ℂ)) x = _ at h
  change fderiv ℝ (fun y => (f y : ℂ)) x (EuclideanSpace.single a 1) = _
  rw [h]
  rfl

private theorem smooth_gauge (inv g : CoordinateSpace → Tensor2)
    (hi : SmoothCoordinateComponents inv) (hg : SmoothCoordinateComponents g) (j : Index) :
    ContDiff ℝ ∞ (fun x => coordinateGaugeCovector inv g x j) := by
  have h : (fun x => coordinateGaugeCovector inv g x j) = (fun x =>
      (∑ a, ∑ b, inv x a b * scalarPartial (fun y => g y b j) a x) -
      (∑ a, ∑ b, inv x a b * scalarPartial (fun y => g y a b) j x) / 2) := rfl
  rw [h]
  unfold SmoothCoordinateComponents at hi
  have hp (a b c : Index) : ContDiff ℝ ∞ (scalarPartial (fun x => g x b c) a) :=
    partial_smooth _ a (hg b c)
  fun_prop

private theorem metricMixedJet_symmetric (g : CoordinateSpace → Tensor2)
    (hg : SmoothCoordinateComponents g) (x : CoordinateSpace) (a b : Index) :
    coordinateSecondMetricJet g x a b = coordinateSecondMetricJet g x b a := by
  funext i j
  let f : CoordinateSpace → ℝ := fun y => g y i j
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have h := ((hg i j).contDiffAt (x := x)).isSymmSndFDerivAt (by simpa using h2)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hg i j).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have h' := h.eq (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
  change scalarPartial (scalarPartial f b) a x = scalarPartial (scalarPartial f a) b x
  have eval (v : CoordinateSpace) :
      fderiv ℝ (fun y => fderiv ℝ f y v) x = (fderiv ℝ (fderiv ℝ f) x).flip v := by
    have hD := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) v x)).fderiv
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using hD
  unfold scalarPartial
  rw [eval, eval]
  exact h'

private theorem metricSecondJet_symmetric (g : CoordinateSpace → Tensor2)
    (hs : ∀ x, IsSymmetricTensor (g x)) (x : CoordinateSpace) (a b : Index) :
    IsSymmetricTensor (coordinateSecondMetricJet g x a b) := by
  intro i j
  have h : (fun y => g y i j) = (fun y => g y j i) := funext fun y => hs y i j
  change scalarPartial (scalarPartial (fun y => g y i j) b) a x =
    scalarPartial (scalarPartial (fun y => g y j i) b) a x
  rw [h]

/-- The exact nondivergence source on the zero-extended cutoff fluctuation. -/
def localizedWaveSourceSchwartz (inv g g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hi : SmoothCoordinateComponents inv) (hg : SmoothCoordinateComponents g)
    (hg₀ : SmoothCoordinateComponents g₀) : ProjectionSchwartzMatrix := fun i j =>
  let z : CoordinateSpace → ℝ := fun x => χ x * (g x i j - g₀ x i j)
  have hz : ContDiff ℝ ∞ z := hχ.mul ((hg i j).sub (hg₀ i j))
  have hSecond (a b : Index) : ContDiff ℝ ∞ (scalarPartial (scalarPartial z b) a) :=
    partial_smooth _ a (partial_smooth _ b hz)
  have hSup : tsupport z ⊆ tsupport χ := tsupport_mul_subset_left
  have hs : ContDiff ℝ ∞ (fun x => scalarWaveAt (inv x) z x) := by
    unfold scalarWaveAt
    unfold SmoothCoordinateComponents at hi
    fun_prop
  have hS : HasCompactSupport (fun x => scalarWaveAt (inv x) z x) := by
    apply compact_of_tsupport_subset hc
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hOff
    have hZero (a b : Index) : scalarPartial (scalarPartial z b) a x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hOff (hSup (partial_tsupport z b (partial_tsupport (scalarPartial z b) a h))))
    exact hx (by simp [scalarWaveAt, hZero])
  complexCompactSchwartz _ hs hS

/-- The exact cutoff times the lowered contracted Christoffel vector. -/
def localizedGaugeSchwartz (inv g : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hi : SmoothCoordinateComponents inv) (hg : SmoothCoordinateComponents g) :
    Fin 4 → SchwartzMap CoordinateSpace ℂ := fun j =>
  complexCompactSchwartz (fun x => χ x * coordinateGaugeCovector inv g x j)
    (hχ.mul (smooth_gauge inv g hi hg j)) hc.mul_right

/-- The projected raw wave source has a uniform bound from the actual vacuum
equation and a fixed compact region controlling the first jet remainder. -/
theorem exists_norm_projection_of_localizedVacuumSource_le
    (inv g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hi : ∀ n, SmoothCoordinateComponents (inv n)) (hg : ∀ n, SmoothCoordinateComponents (g n))
    (hg₀ : SmoothCoordinateComponents g₀) (B : ℝ)
    (hInvSym : ∀ n x, x ∈ tsupport χ → IsSymmetricTensor (inv n x))
    (hSym : ∀ n x, IsSymmetricTensor (g n x))
    (hVac : ∀ n x, x ∈ tsupport χ → ∀ i j,
      coordinateRicci (fun y => christoffel (inv n y) (coordinateJet (g n) y)) x i j = 0)
    (hBound : ∀ n x, x ∈ tsupport χ → ‖localizedSourceJets (inv n) (g n) g₀ x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖projectionFullL2 (projectionMatrixToL2
        (localizedWaveSourceSchwartz (inv n) (g n) g₀ χ hχ hc (hi n) (hg n) hg₀))‖ ≤ C := by
  have hgd (n) : ∀ i j, Differentiable ℝ (fun x => g n x i j) :=
    fun i j => (hg n i j).differentiable (by simp)
  have hg₀d : ∀ i j, Differentiable ℝ (fun x => g₀ x i j) :=
    fun i j => (hg₀ i j).differentiable (by simp)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  choose C hC hRem using fun i j =>
    exists_localizedVacuumSourceRemainder_majorant inv g g₀ χ i j B hχ hc
      (fun n x a b => hgd n a b x) (fun x a b => hg₀d a b x) hBound
  let C' := ∑ i, ∑ j, C i j
  have hC' (i j : Index) : C i j ≤ C' := by
    exact (Finset.single_le_sum (f := fun j => C i j) (fun j _ => hC i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, C i j)
        (fun i _ => Finset.sum_nonneg fun j _ => hC i j) (Finset.mem_univ i))
  refine ⟨‖projectionFullL2‖ * (eLpNorm ((tsupport χ).indicator (fun _ => C')) 2 volume).toReal,
    by positivity, fun n => ?_⟩
  let Q := localizedWaveSourceSchwartz (inv n) (g n) g₀ χ hχ hc (hi n) (hg n) hg₀
  let V := localizedGaugeSchwartz (inv n) (g n) χ hχ hc (hi n) (hg n)
  let R : ProjectionSchwartzMatrix := fun i j =>
    Q i j - (coordinateDerivative i (V j) + coordinateDerivative j (V i))
  refine norm_projectionFullL2_localized_source_le Q R V ?_ (tsupport χ) hc C' ?_
  · intro i j x
    simp only [R, SchwartzMap.sub_apply, SchwartzMap.add_apply]
    ring
  · intro i j x
    have hv (a b : Index) : coordinateDerivative a (V b) x =
        (scalarPartial (fun y => χ y * coordinateGaugeCovector (inv n) (g n) y b) a x : ℂ) := by
      exact complexCompactSchwartz_partial _ _ _ a x
    change ‖Q i j x - (coordinateDerivative i (V j) x + coordinateDerivative j (V i) x)‖ ≤ _
    rw [hv, hv]
    by_cases hx : x ∈ tsupport χ
    · have hr (a b c : Index) : DifferentiableAt ℝ (fun y => coordinateJet (g n) y a b c) x :=
        (partial_smooth _ a (hg n b c)).differentiable (by simp) x
      have hr₀ (a b c : Index) : DifferentiableAt ℝ (fun y => coordinateJet g₀ y a b c) x :=
        (partial_smooth _ a (hg₀ b c)).differentiable (by simp) x
      have hId := localizedVacuumSource_eq_symmetrizedGauge_add_remainder
        (inv n) (g n) g₀ χ x i j hχd
        (fun a => (partial_smooth χ a hχ).differentiable (by simp) x)
        (hgd n) hg₀d hr hr₀ (fun a b => (hi n a b).differentiable (by simp) x) (hInvSym n x hx)
        (metricMixedJet_symmetric (g n) (hg n) x)
        (metricSecondJet_symmetric (g n) (hSym n) x)
        (fun b => (smooth_gauge (inv n) (g n) (hi n) (hg n) b).differentiable (by simp) x)
        (hVac n x hx i j)
      change ‖(scalarWaveAt (inv n x) (fun y => χ y * (g n y i j - g₀ y i j)) x : ℂ) - _‖ ≤ _
      rw [hId, Complex.ofReal_add, Complex.ofReal_add, add_sub_cancel_left, Complex.norm_real,
        Set.indicator_of_mem hx]
      exact (by simpa only [Set.indicator_of_mem hx] using hRem i j n x :
        ‖localizedVacuumSourceRemainder (inv n) (g n) g₀ χ x i j‖ ≤ C i j).trans (hC' i j)
    · let z : CoordinateSpace → ℝ := fun y => χ y * (g n y i j - g₀ y i j)
      have hs : tsupport z ⊆ tsupport χ := tsupport_mul_subset_left
      have hZero (a b : Index) : scalarPartial (scalarPartial z b) a x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h => hx (hs (partial_tsupport z b (partial_tsupport (scalarPartial z b) a h))))
      have hvZero (a b : Index) :
          scalarPartial (fun y => χ y * coordinateGaugeCovector (inv n) (g n) y b) a x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h => hx (tsupport_mul_subset_left (partial_tsupport _ a h)))
      change ‖(scalarWaveAt (inv n x) z x : ℂ) - _‖ ≤ _
      simp [hvZero, scalarWaveAt, hZero, Set.indicator_of_notMem hx]

end Burnett.P01
