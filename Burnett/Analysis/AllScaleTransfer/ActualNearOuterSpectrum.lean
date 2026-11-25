import Burnett.Analysis.AllScaleTransfer.ActualNearOuterAssembly
import Burnett.Analysis.AllScaleTransfer.SignedEndpointWindows

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Set Filter Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ENNReal BigOperators

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private theorem near_spectrum_projected_coordinate {ι : Type*} [Fintype ι] {b : E → ℝ} {C : ℝ}
    (P : CapLpRealization (ENNReal.ofReal 3) b C) (F U : ι → SchwartzMap E ℂ)
    (hAction : ∀ i x, U i x = radianAction b (F i) x) (i : ι) :
    (U i).toLp (ENNReal.ofReal 3) volume =
      fieldCoordinateLp i (P.fieldAction (schwartzFieldLp3 F)) := by
  let f : E → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 (fun i => F i x)
  let hf : MemLp f (ENNReal.ofReal 3) volume :=
    fieldArray_memLp (fun i x => F i x) (fun i => (F i).memLp _ volume)
  change _ = fieldCoordinateLp i (liftScalarLp P.action (hf.toLp f))
  rw [fieldCoordinateLp_liftScalarLp]
  have e : fieldCoordinateLp i (hf.toLp f) = (F i).toLp (ENNReal.ofReal 3) volume :=
    fieldCoordinateLp_toLp i hf
  rw [e]
  apply Lp.ext
  have hAct : (U i : E → ℂ) =ᵐ[volume] (fun x => radianAction b (F i) x) :=
    Eventually.of_forall (hAction i)
  exact ((U i).coeFn_toLp (ENNReal.ofReal 3) volume).trans
    (hAct.trans (P.schwartz_eq (F i)).symm)

private theorem normalized_finite_radial_annulus
    (A : E ≃L[ℝ] E) (J : Finset ℤ) (u : SchwartzMap E ℂ)
    (hs : tsupport (radianFourier (u : E → ℂ)) ⊆ finiteIntegerRadialFrequencySupport J) :
    EndpointFiniteAnnulus (pullbackTrilinearFactor A u) := by
  let K := A ⁻¹' finiteIntegerRadialFrequencySupport J
  have compactK : IsCompact K := A.toHomeomorph.isCompact_preimage.mpr
    (finiteIntegerRadialFrequencySupport_compact J)
  have zeroK : (0 : E) ∉ K := by
    change A 0 ∉ finiteIntegerRadialFrequencySupport J
    rw [map_zero]
    exact zero_notMem_finiteIntegerRadialFrequencySupport J
  obtain ⟨lo,hLo,hBall⟩ := Metric.mem_nhds_iff.mp
    (compactK.isClosed.isOpen_compl.mem_nhds (show (0 : E) ∈ Kᶜ from zeroK))
  obtain ⟨hi,hHi⟩ := (compactK.image continuous_norm).bddAbove
  apply endpointFiniteAnnulus_of_radian _ lo hi hLo
  intro p hp
  have physical : radianFourier (u : E → ℂ) (A p) ≠ 0 := by
    intro h
    have e := radianFourier_comp_inverseDual A (u : E → ℂ) p
    change radianFourier (pullbackTrilinearFactor A u : E → ℂ) p =
      linearJacobian A • radianFourier (u : E → ℂ) (A p) at e
    rw [h,smul_zero] at e
    exact hp e
  have pK : p ∈ K := hs (subset_tsupport _ physical)
  exact ⟨le_of_not_gt (fun h => hBall (mem_ball_zero_iff.mpr h) pK),
    hHi (mem_image_of_mem norm pK)⟩

/-- The exact near decomposition and the cap Hölder estimate use the
same actual projected factors. The rescaled local estimate receives the three
actual finite-annulus spectra and their individual enlarged-cap support. -/
theorem radian_near_finite_field_bound_with_spectra
    {ι ξ : Type*} [Fintype ι] [Fintype ξ]
    {metric : Form} {δ η inner outer enlarged D C₃ : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
      (enlargedCapMultiplier metric δ η outer enlarged γ) C₃)
    {q Cκ A C : ℝ} (hq : 3 < q) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hη : 0 < η)
    (hD : 0 < D) (hCκ : 0 ≤ Cκ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hAngular : ∀ v : FieldLp ι (ENNReal.ofReal 3),
      (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^(1/3 : ℝ) ≤
        ((Fintype.card ι : ℝ) * C) * (S.centers.card : ℝ)^(1/(3*(q-2))) * ‖v‖)
    {ϑ : ℝ → ℝ} (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (m : ξ → Joint → ℂ) (hm : ∀ k, AEStronglyMeasurable (m k) volume)
    (B : ℝ) (hBound : ∀ k p, ‖m k p‖ ≤ B)
    (J : Fin 3 → Finset ℤ) (ε : Fin 3 → ℤ → ℂ) (f : Fin 3 → ι → SchwartzMap E ℂ)
    (left middle right : ξ → ι)
    (chart : ∀ γ : ↑S.centers, NullCapChart metric γ) :
    let F (i : Fin 3) (a : ι) := finiteIntegerRadialTruncation (J i) (ε i) (f i a)
    let V (i : Fin 3) := schwartzFieldLp3 (F i)
    let dil (γ : ↑S.centers) := capFrequencyEquiv (chart γ) hδ.1.ne'
    let mCap (γ : ↑S.centers) (k : ξ) := capLocalizedNearSymbol S (m k) γ
    (∀ k p, radianTrilinearWeight (m k) (F 0 (left k)) (F 1 (middle k)) (F 2 (right k)) p ≠ 0 →
      |quadratic metric p.1| ≤ inner*η*‖p.1‖^2 ∧
        |quadratic metric p.2| ≤ outer*η*‖p.2‖^2 ∧
        |quadratic metric (-(p.1+p.2))| ≤ outer*η*‖-(p.1+p.2)‖^2 ∧
        angularNearWeight ϑ δ p.1 p.2 (-(p.1+p.2)) ≠ 0) →
    (∀ (γ : ↑S.centers) (k : ξ) (f' g' h' : SchwartzMap E ℂ),
      let P := tsupport (enlargedCapMultiplier metric δ η outer enlarged γ)
      EndpointFiniteAnnulus f' → EndpointFiniteAnnulus g' → EndpointFiniteAnnulus h' →
      (∀ p, radianFourier (f' : E → ℂ) p ≠ 0 → dil γ p ∈ P) →
      (∀ p, radianFourier (g' : E → ℂ) p ≠ 0 → dil γ p ∈ P) →
      (∀ p, radianFourier (h' : E → ℂ) p ≠ 0 → dil γ p ∈ P) →
      ‖radianTrilinearForm (((δ^2)⁻¹ • mCap γ k) ∘ pairedFrequencyEquiv (dil γ)) f' g' h'‖ ≤
        (Cκ * A) * (triLpMass f' g' h' 3 3 3).toReal) →
    ‖∑ k : ξ, radianTrilinearForm (m k) (F 0 (left k)) (F 1 (middle k)) (F 2 (right k))‖ ≤
      ((Cκ * (Fintype.card ξ : ℝ)) * ((Fintype.card ι : ℝ) * C)^3 * D^(1/(q-2))) *
        A * δ^(2*(q-3)/(q-2)) * ‖V 0‖ * ‖V 1‖ * ‖V 2‖ := by
  classical
  intro F V dil mCap hGeom hLocal
  have center (γ : ↑S.centers) : (γ : Vec) ≠ 0 := by
    intro h
    have hn := (S.centers_null γ.property).1
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  choose U hAction _hSpectrum hSupport using
    fun (γ : ↑S.centers) (i : Fin 3) (a : ι) =>
      exists_enlargedCap_finiteIntegerRadialTruncation_schwartz metric δ hη outer enlarged
        (center γ) (J i) (ε i) (f i a)
  have projected (γ : ↑S.centers) (i : Fin 3) (a : ι) :
      (U γ i a).toLp (ENNReal.ofReal 3) volume = fieldCoordinateLp a ((Pplus γ).fieldAction (V i)) :=
    near_spectrum_projected_coordinate (Pplus γ) (F i) (U γ i) (hAction γ i) a
  have decomposition (k : ξ) :
      radianTrilinearForm (m k) (F 0 (left k)) (F 1 (middle k)) (F 2 (right k)) =
      ∑ γ : ↑S.centers, radianTrilinearForm (mCap γ k)
        (U γ 0 (left k)) (U γ 1 (middle k)) (U γ 2 (right k)) := by
    let idx : Fin 3 → ι := ![left k,middle k,right k]
    obtain ⟨u,hAct,_,_,eq⟩ := exists_actual_nearCap_decomposition S hδ.1 hη hCut (m k) (hm k)
      B (hBound k) J ε (fun i => f i (idx i)) (hGeom k)
    refine eq.trans (Finset.sum_congr rfl fun γ _ => ?_)
    have same (i : Fin 3) : u γ i = U γ i (idx i) := by
      apply SchwartzMap.ext
      intro x
      exact (hAct γ i x).trans (hAction γ i (idx i) x).symm
    rw [same 0,same 1,same 2]
    rfl
  have exactSum :
      (∑ k : ξ, radianTrilinearForm (m k) (F 0 (left k)) (F 1 (middle k)) (F 2 (right k))) =
        ∑ γ : ↑S.centers, ∑ k : ξ, radianTrilinearForm (mCap γ k)
          (U γ 0 (left k)) (U γ 1 (middle k)) (U γ 2 (right k)) := by
    simp_rw [decomposition]
    exact Finset.sum_comm
  have normalized (γ : ↑S.centers) (k : ξ) :
      let f' := pullbackTrilinearFactor (dil γ) (U γ 0 (left k))
      let g' := pullbackTrilinearFactor (dil γ) (U γ 1 (middle k))
      let h' := pullbackTrilinearFactor (dil γ) (U γ 2 (right k))
      ‖radianTrilinearForm (mCap γ k ∘ pairedFrequencyEquiv (dil γ)) f' g' h'‖ ≤
        (Cκ * A * δ^2) * (triLpMass f' g' h' 3 3 3).toReal := by
    intro f' g' h'
    let b := enlargedCapMultiplier metric δ η outer enlarged γ
    have finite (i : Fin 3) (a : ι) :
        EndpointFiniteAnnulus (pullbackTrilinearFactor (dil γ) (U γ i a)) :=
      normalized_finite_radial_annulus (dil γ) (J i) (U γ i a)
        ((hSupport γ i a).trans (inter_subset_right.trans
          (tsupport_radianFourier_finiteIntegerRadialTruncation (J i) (ε i) (f i a))))
    have cap (i : Fin 3) (a : ι) (p : E)
        (hp : radianFourier (pullbackTrilinearFactor (dil γ) (U γ i a) : E → ℂ) p ≠ 0) :
        dil γ p ∈ tsupport b :=
      tsupport_radianFourier_pullbackTrilinearFactor_subset (dil γ) (U γ i a) b
        ((hSupport γ i a).trans inter_subset_left) (subset_tsupport _ hp)
    have bound := hLocal γ k f' g' h' (finite 0 (left k)) (finite 1 (middle k)) (finite 2 (right k))
      (cap 0 (left k)) (cap 1 (middle k)) (cap 2 (right k))
    let core := ((δ^2)⁻¹ • mCap γ k) ∘ pairedFrequencyEquiv (dil γ)
    have scale : mCap γ k ∘ pairedFrequencyEquiv (dil γ) =
        fun p => ((δ^2 : ℝ) : ℂ) * core p := by
      funext p
      change _ = ((δ^2 : ℝ) : ℂ) * ((δ^2)⁻¹ • mCap γ k (pairedFrequencyEquiv (dil γ) p))
      rw [← Complex.real_smul,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hδ.1.ne'),one_smul]
      rfl
    rw [scale,radianTrilinearForm_const_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg δ)]
    exact (mul_le_mul_of_nonneg_left bound (sq_nonneg δ)).trans_eq (by ring)
  rw [exactSum]
  exact radian_near_field_bound_of_normalized_bounds S Pplus hq hδ hD hCκ hA hC hAngular
    (V 0) (V 1) (V 2) (fun γ => U γ 0) (fun γ => U γ 1) (fun γ => U γ 2)
    (fun γ i => projected γ 0 i) (fun γ i => projected γ 1 i) (fun γ i => projected γ 2 i)
    left middle right mCap chart normalized

end Burnett.A05
