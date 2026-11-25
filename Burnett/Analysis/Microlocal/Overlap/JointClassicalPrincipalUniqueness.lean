import Burnett.Analysis.Microlocal.Overlap.JointClassicalModulatedLimit
import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives

/-! The principal symbol of the same local classical operator is unique modulo compact remainders. -/
set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 6300000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.P01 (exists_projectedChartCutoff)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Analysis.HminusWeightedDual (complexTest)
open scoped ComplexConjugate FourierTransform InnerProduct RealInnerProductSpace Topology

local notation "E" => CoordinateSpace

open private inner_tendsto_zero_of_bounded_of_tendsto_zero
  from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

theorem tendsto_modulated_pairing_of_hasLocalClassicalRepresentation
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (a : E → E → ℂ) (L : Set E)
    (hT : HasLocalClassicalRepresentation T a L) (D₀ : ℝ) (hD : ∀ x η, ‖a x η‖ ≤ D₀)
    (hP : Continuous (uncurry (infraredAngularPrincipal a))) (ξ : E) (hξ : ξ ≠ 0)
    (hCont : ∀ x, ContinuousAt (a x) ξ) (hDegree : ∀ x, DegreeZero (a x))
    (v f : SchwartzMap E ℂ) (hv : HasCompactSupport (v : E → ℂ)) (hf : HasCompactSupport (f : E → ℂ))
    (hL : tsupport (f : E → ℂ) ⊆ L) :
    Tendsto (fun n : ℕ => inner ℂ ((compactModulatedSchwartz ((n : ℝ) • ξ) v hv).toLp 2 volume)
      (T ((compactModulatedSchwartz ((n : ℝ) • ξ) f hf).toLp 2 volume)))
      atTop (𝓝 (∫ x, conj (v x) * (a x ξ * f x))) := by
  obtain ⟨R, hR, hRep⟩ := hT
  have hA := tendsto_classicalLeftPairing_compactModulatedSchwartz a D₀ hD hP ξ hξ hCont hDegree v f hv hf
  have hS := tendsto_compactOperator_compactModulatedSchwartz ξ hξ f hf R hR
  have hSmall := inner_tendsto_zero_of_bounded_of_tendsto_zero
    (fun n : ℕ => (compactModulatedSchwartz ((n : ℝ) • ξ) v hv).toLp 2 volume) _ ‖v.toLp 2 volume‖
      (fun n => (norm_compactModulatedSchwartz_toLp ((n : ℝ) • ξ) v hv).le) hS
  have h := hA.add hSmall
  rw [add_zero] at h
  refine h.congr (fun n => ?_)
  exact (hRep (compactModulatedSchwartz ((n : ℝ) • ξ) v hv) (compactModulatedSchwartz ((n : ℝ) • ξ) f hf)
    ((compactModulatedSchwartz_tsupport ((n : ℝ) • ξ) f hf).trans hL)).symm

private theorem eqOn_interior_of_local_diagonal_pairings
    (a b : E → ℂ) (ha : Continuous a) (hb : Continuous b) (L : Set E)
    (hEq : ∀ f : D, tsupport (f : E → ℝ) ⊆ L →
      (∫ x, ((f : E → ℝ) x : ℂ) * (a x * ((f : E → ℝ) x : ℂ))) =
        ∫ x, ((f : E → ℝ) x : ℂ) * (b x * ((f : E → ℝ) x : ℂ))) :
    EqOn a b (interior L) := by
  intro x hx
  have hNonpos (ℓ : ℂ →L[ℝ] ℝ) : ℓ (a x - b x) ≤ 0 := by
    by_contra! hPos
    let V := interior L ∩ {y | 0 < ℓ (a y - b y)}
    have hVO : IsOpen V := isOpen_interior.inter (isOpen_lt continuous_const (ℓ.continuous.comp (ha.sub hb)))
    have hxV : x ∈ V := ⟨hx, hPos⟩
    obtain ⟨φ, hs, hc, hφV, W, _, hxW, _, hφW⟩ := exists_projectedChartCutoff
      (isCompact_singleton (x := x)) hVO (singleton_subset_iff.mpr hxV)
    let f : D := ⟨φ, hs, hc⟩
    have hfL : tsupport (f : E → ℝ) ⊆ L := hφV.trans (inter_subset_left.trans interior_subset)
    have hOne : φ x = 1 := hφW (hxW (mem_singleton x))
    let w (y : E) : ℂ := φ y
    let F (y : E) := w y * (a y * w y) - w y * (b y * w y)
    have hw : Continuous w := Complex.continuous_ofReal.comp hs.continuous
    have hwc : HasCompactSupport w := hc.comp_left Complex.ofReal_zero
    have hIa : Integrable (fun y => w y * (a y * w y)) :=
      (hw.mul (ha.mul hw)).integrable_of_hasCompactSupport hwc.mul_right
    have hIb : Integrable (fun y => w y * (b y * w y)) :=
      (hw.mul (hb.mul hw)).integrable_of_hasCompactSupport hwc.mul_right
    have hF : (∫ y, F y) = 0 := by
      rw [show (∫ y, F y) = (∫ y, w y * (a y * w y)) - (∫ y, w y * (b y * w y)) from integral_sub hIa hIb]
      exact sub_eq_zero.mpr (hEq f hfL)
    let J (y : E) : ℝ := φ y ^ 2 * ℓ (a y - b y)
    have hJ (y : E) : ℓ (F y) = J y := by
      change ℓ ((φ y : ℂ) * (a y * (φ y : ℂ)) - (φ y : ℂ) * (b y * (φ y : ℂ))) =
        φ y ^ 2 * ℓ (a y - b y)
      calc
        _ = ℓ ((φ y ^ 2) • (a y - b y)) := by
          congr 1
          rw [Complex.real_smul, Complex.ofReal_pow]
          ring
        _ = _ := by rw [map_smul, smul_eq_mul]
    have hJI : Integrable J := (ℓ.integrable_comp (hIa.sub hIb)).congr (Eventually.of_forall hJ)
    have hJI0 : (∫ y, J y) = 0 := by
      simp only [← hJ]
      have hFI : Integrable F := hIa.sub hIb
      rw [ℓ.integral_comp_comm hFI, hF, map_zero]
    have hNN (y : E) : 0 ≤ J y := by
      by_cases hy : y ∈ tsupport φ
      · exact mul_nonneg (sq_nonneg _) (hφV hy).2.le
      · simp only [J, image_eq_zero_of_notMem_tsupport hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, le_refl]
    have hAE := (integral_eq_zero_iff_of_nonneg hNN hJI).mp hJI0
    have hJCont : Continuous J := (hs.continuous.pow 2).mul (ℓ.continuous.comp (ha.sub hb))
    have hAt := congrFun ((volume : Measure E).eq_of_ae_eq hAE hJCont continuous_const) x
    change φ x ^ 2 * ℓ (a x - b x) = 0 at hAt
    rw [hOne, one_pow, one_mul] at hAt
    exact hPos.ne' hAt
  have hZero (ℓ : ℂ →L[ℝ] ℝ) : ℓ (a x - b x) = 0 := by
    have hOpp := hNonpos (-ℓ)
    exact le_antisymm (hNonpos ℓ) (neg_nonpos.mp hOpp)
  exact sub_eq_zero.mp (Complex.ext (hZero Complex.reCLM) (hZero Complex.imCLM))

/-- Two classical representations of the same actual local operator have
the same angular principal symbol everywhere in the common open right window. -/
theorem eqOn_interior_principalSymbol_of_same_local_operator
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (a b : E → E → ℂ) (L : Set E)
    (hTa : HasLocalClassicalRepresentation T a L) (hTb : HasLocalClassicalRepresentation T b L)
    (Dₐ Dᵦ : ℝ) (hDa : ∀ x η, ‖a x η‖ ≤ Dₐ) (hDb : ∀ x η, ‖b x η‖ ≤ Dᵦ)
    (hPa : Continuous (uncurry (infraredAngularPrincipal a))) (hPb : Continuous (uncurry (infraredAngularPrincipal b)))
    (ξ : E) (hξ : ξ ≠ 0) (hXa : Continuous (fun x => a x ξ)) (hXb : Continuous (fun x => b x ξ))
    (hCa : ∀ x, ContinuousAt (a x) ξ) (hCb : ∀ x, ContinuousAt (b x) ξ)
    (hSa : ∀ x, DegreeZero (a x)) (hSb : ∀ x, DegreeZero (b x)) :
    EqOn (fun x => a x ξ) (fun x => b x ξ) (interior L) := by
  apply eqOn_interior_of_local_diagonal_pairings _ _ hXa hXb L
  intro φ hφ
  let f := complexTest φ
  have hSupport : tsupport (f : E → ℂ) ⊆ tsupport (φ : E → ℝ) := by
    apply closure_mono
    intro x hx
    change ((φ : E → ℝ) x : ℂ) ≠ 0 at hx
    exact Complex.ofReal_ne_zero.mp hx
  have hfc : HasCompactSupport (f : E → ℂ) := (test_compactSupport φ).comp_left Complex.ofReal_zero
  have hLimA := tendsto_modulated_pairing_of_hasLocalClassicalRepresentation T a L hTa Dₐ hDa hPa ξ hξ hCa hSa
    f f hfc hfc (hSupport.trans hφ)
  have hLimB := tendsto_modulated_pairing_of_hasLocalClassicalRepresentation T b L hTb Dᵦ hDb hPb ξ hξ hCb hSb
    f f hfc hfc (hSupport.trans hφ)
  have h := tendsto_nhds_unique hLimA hLimB
  change (∫ x, conj ((φ : E → ℝ) x : ℂ) * (a x ξ * ((φ : E → ℝ) x : ℂ))) =
    (∫ x, conj ((φ : E → ℝ) x : ℂ) * (b x ξ * ((φ : E → ℝ) x : ℂ))) at h
  simpa only [Complex.conj_ofReal] using h

end Burnett.Microlocal.AtlasOverlapKernel
