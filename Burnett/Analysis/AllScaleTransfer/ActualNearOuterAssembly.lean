import Burnett.Analysis.AllScaleTransfer.ActualNearCapDecomposition
import Burnett.Analysis.AllScaleTransfer.RadianNearProjectedSum
import Burnett.Analysis.AllScaleTransfer.RadianBoxRadialSum

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Set Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ENNReal BigOperators

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The actual finite array assembled with the Euclidean fiber norm. -/
def schwartzFieldLp3 {ι : Type*} [Fintype ι] (F : ι → SchwartzMap E ℂ) :
    FieldLp ι (ENNReal.ofReal 3) :=
  (fieldArray_memLp (fun i x => F i x) (fun i => (F i).memLp _ volume)).toLp
    (fun x => WithLp.toLp 2 (fun i => F i x))

private theorem near_projected_coordinate {ι : Type*} [Fintype ι] {b : E → ℝ} {C : ℝ}
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

/-- The exact near decomposition and the cap Hölder estimate use the
same actual projected factors. The local estimate is for the rescaled
coefficient of that same designated-slot cap symbol. -/
theorem radian_near_finite_field_bound
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
      (∀ p, radianWeight (fun _ => 1) f' g' h' p ≠ 0 →
        dil γ p.1 ∈ P ∧ dil γ p.2 ∈ P ∧ dil γ (-(p.1+p.2)) ∈ P) →
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
    near_projected_coordinate (Pplus γ) (F i) (U γ i) (hAction γ i) a
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
    let tri : Fin 3 → SchwartzMap E ℂ := ![U γ 0 (left k),U γ 1 (middle k),U γ 2 (right k)]
    let b := enlargedCapMultiplier metric δ η outer enlarged γ
    have supported (i : Fin 3) : tsupport (radianFourier (tri i : E → ℂ)) ⊆ tsupport b := by
      fin_cases i
      · exact (hSupport γ 0 (left k)).trans inter_subset_left
      · exact (hSupport γ 1 (middle k)).trans inter_subset_left
      · exact (hSupport γ 2 (right k)).trans inter_subset_left
    have bound := hLocal γ k f' g' h'
      (radianWeight_pullback_nonzero_cap_support (dil γ) b tri supported)
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
