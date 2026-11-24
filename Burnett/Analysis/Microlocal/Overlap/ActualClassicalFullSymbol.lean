import Burnett.Analysis.Microlocal.Overlap.AngularClassicalSymbolModel
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets

/-! A compact-base classical full symbol and its fixed infrared remainder. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2100000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Metric Set Burnett.Fourier
open Burnett.Analysis.CarlesonEmbedding (contDiff_firstPartialJet)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel
  (E radialCore radialCore_contDiff radialCore_eq_one radialCore_eq_zero radialCore_nonneg radialCore_le_one)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

/-- The actual Schwartz pairing for the full left Fourier symbol. -/
def classicalLeftPairing (p : E → E → ℂ) (f v : SchwartzMap E ℂ) : ℂ :=
  ∫ x, conj (f x) * firstOrderAction p v x

theorem contDiff_uncurry_infraredAngularPrincipal {a : E → E → ℂ}
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E))) :
    ContDiff ℝ ∞ (uncurry (infraredAngularPrincipal a)) := by
  have hc : ContDiff ℝ ∞ (fun q : E × E => (1 : ℂ) - (radialCore q.2 : ℂ)) :=
    contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (radialCore_contDiff.comp contDiff_snd))
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q.2 = 0
  · have hSmall : ∀ᶠ z : E × E in 𝓝 q, ‖z.2‖ < (1 : ℝ) :=
      (continuous_snd.norm.tendsto q).eventually (Iio_mem_nhds (by simp [hq]))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hSmall] with z hz
    change (1 - (radialCore z.2 : ℂ)) * a z.1 z.2 = 0
    simp only [radialCore_eq_one _ hz.le, Complex.ofReal_one, sub_self, zero_mul]
  · have hOpen : IsOpen ((univ : Set E) ×ˢ ({0}ᶜ : Set E)) :=
      isOpen_univ.prod isOpen_compl_singleton
    exact hc.contDiffAt.mul (ha.contDiffAt (hOpen.mem_nhds ⟨mem_univ _, hq⟩))

/-- Above the fixed infrared scale the remainder is exactly `b - a`. -/
def classicalFullRemainder (b a : E → E → ℂ) (x ξ : E) : ℂ :=
  b x ξ - infraredAngularPrincipal a x ξ

theorem classicalFullRemainder_support {b a : E → E → ℂ} {S : Set E} (hS : IsCompact S)
    (hb : ∀ ξ, tsupport (fun x => b x ξ) ⊆ S)
    (ha : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S) (ξ : E) :
    tsupport (fun x => classicalFullRemainder b a x ξ) ⊆ S := by
  apply closure_minimal _ hS.isClosed
  intro x hx
  by_contra h
  apply hx
  have hB : b x ξ = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => b y ξ) (fun hx' => h (hb ξ hx'))
  have hA : a x ξ = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => a y ξ) (fun hx' => h (ha ξ hx'))
  simp [classicalFullRemainder, infraredAngularPrincipal, hB, hA]

/-- A classical high-frequency remainder estimate suffices for the full
fixed infrared remainder. The low-frequency part is controlled on compact phase sets. -/
theorem orderMinusOneBounds_classicalFullRemainder {b a : E → E → ℂ}
    {S : Set E} (hS : IsCompact S)
    (hb : ∀ ξ, tsupport (fun x => b x ξ) ⊆ S)
    (ha : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hbDiff : ContDiff ℝ ∞ (uncurry b))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (R : ℝ)
    (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C) :
    OrderMinusOneBounds (classicalFullRemainder b a) := by
  intro n
  obtain ⟨C, hC, hHigh⟩ := hLarge n
  let L := max (2 : ℝ) R
  let p := classicalFullRemainder b a
  let F (q : E × E) := (1 + ‖q.2‖) * ‖iteratedFDeriv ℝ n (fun y => p y q.2) q.1‖
  have hp : ContDiff ℝ ∞ (uncurry p) := hbDiff.sub (contDiff_uncurry_infraredAngularPrincipal haDiff)
  have hF : Continuous F :=
    (continuous_const.add continuous_snd.norm).mul (contDiff_firstPartialJet hp n).continuous.norm
  obtain ⟨D, hD⟩ := ((hS.prod (isCompact_closedBall (0 : E) L)).image hF).isBounded.exists_norm_le
  refine ⟨max C D, le_trans hC (le_max_left _ _), fun x ξ => ?_⟩
  by_cases hξ : L ≤ ‖ξ‖
  · have he : (fun y => p y ξ) = (fun y => b y ξ - a y ξ) := by
      funext y
      simp [p, classicalFullRemainder, infraredAngularPrincipal, radialCore_eq_zero _ ((le_max_left _ _).trans hξ)]
    rw [he]
    exact (hHigh x ξ ((le_max_right _ _).trans hξ)).trans (le_max_left _ _)
  · by_cases hx : x ∈ S
    · have ht : ξ ∈ closedBall (0 : E) L := by
        simpa only [mem_closedBall, dist_zero_right] using (le_of_not_ge hξ)
      have hBound := hD _ (mem_image_of_mem F (show (x, ξ) ∈ S ×ˢ closedBall 0 L from ⟨hx, ht⟩))
      change F (x, ξ) ≤ max C D
      exact (le_abs_self _).trans (hBound.trans (le_max_right _ _))
    · have hZero : iteratedFDeriv ℝ n (fun y => p y ξ) x = 0 := by
        by_contra h
        exact hx (classicalFullRemainder_support hS hb ha ξ (support_iteratedFDeriv_subset n h))
      rw [hZero, norm_zero, mul_zero]
      exact hC.trans (le_max_left _ _)

private def classicalFrequency (p : E → E → ℂ) (v : SchwartzMap E ℂ) (x ξ : E) : ℂ :=
  baseFourierPhase ξ x * (p x ξ * (𝓕 (v : E → ℂ)) ξ)

private theorem firstOrderAction_classicalFrequency (p : E → E → ℂ) (v : SchwartzMap E ℂ) (x : E) :
    firstOrderAction p v x = ∫ ξ, classicalFrequency p v x ξ := by
  rw [firstOrderAction, Real.fourierIntegralInv_eq']
  rfl

private theorem classicalFrequency_measurable {p : E → E → ℂ} (hp : Measurable (uncurry p))
    (v : SchwartzMap E ℂ) : Measurable (uncurry (classicalFrequency p v)) := by
  have hPhase : Continuous (fun z : E × E => baseFourierPhase z.2 z.1) :=
    baseFourierPhase_continuous_apply continuous_snd continuous_fst
  have hFourier : Measurable (fun z : E × E => (𝓕 (v : E → ℂ)) z.2) :=
    (SchwartzMap.fourierTransformCLE ℂ v).continuous.measurable.comp measurable_snd
  exact hPhase.measurable.mul (hp.mul hFourier)

private theorem classicalFrequency_norm_le {p : E → E → ℂ} {C : ℝ}
    (hBounds : ∀ x ξ, ‖p x ξ‖ ≤ C) (v : SchwartzMap E ℂ) (x ξ : E) :
    ‖classicalFrequency p v x ξ‖ ≤ C * ‖(𝓕 (v : E → ℂ)) ξ‖ := by
  unfold classicalFrequency
  rw [norm_mul, baseFourierPhase_norm, one_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hBounds x ξ) (norm_nonneg _)

private theorem classicalFrequency_integrable {p : E → E → ℂ} (hp : Measurable (uncurry p))
    {C : ℝ} (hBounds : ∀ x ξ, ‖p x ξ‖ ≤ C) (v : SchwartzMap E ℂ) (x : E) :
    Integrable (classicalFrequency p v x) (volume : Measure E) := by
  have hArg : Measurable (fun ξ : E => (x, ξ)) := measurable_const.prodMk measurable_id
  have hMeas : Measurable (classicalFrequency p v x) := by
    change Measurable (uncurry (classicalFrequency p v) ∘ fun ξ : E => (x, ξ))
    exact (classicalFrequency_measurable (p := p) hp v).comp hArg
  have hI : Integrable (fun ξ => ‖(𝓕 (v : E → ℂ)) ξ‖) (volume : Measure E) :=
    (SchwartzMap.fourierTransformCLE ℂ v).integrable.norm
  exact (hI.const_mul C).mono' hMeas.aestronglyMeasurable
    (Eventually.of_forall (classicalFrequency_norm_le hBounds v x))

private theorem classicalLeftPairing_integrable {p : E → E → ℂ}
    (hp : Measurable (uncurry p)) {C : ℝ} (hBounds : ∀ x ξ, ‖p x ξ‖ ≤ C)
    (f v : SchwartzMap E ℂ) : Integrable (fun x : E => conj (f x) * firstOrderAction p v x) volume := by
  have hEq : firstOrderAction p v = fun x => ∫ ξ, classicalFrequency p v x ξ :=
    funext (firstOrderAction_classicalFrequency p v)
  have hI : Measurable (firstOrderAction p v) := by
    rw [hEq]
    exact ((classicalFrequency_measurable hp v).stronglyMeasurable.integral_prod_right').measurable
  have hMeas : Measurable (fun x : E => conj (f x) * firstOrderAction p v x) :=
    (Complex.continuous_conj.measurable.comp f.continuous.measurable).mul hI
  let D : ℝ := C * ∫ ξ, ‖(𝓕 (v : E → ℂ)) ξ‖
  have hf : Integrable (f : E → ℂ) (volume : Measure E) := f.integrable
  have hDom : Integrable (fun x : E => ‖f x‖ * D) (volume : Measure E) := hf.norm.mul_const D
  refine hDom.mono' hMeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_conj]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [firstOrderAction_classicalFrequency]
  have hFrequency : Integrable (fun ξ => C * ‖(𝓕 (v : E → ℂ)) ξ‖) (volume : Measure E) :=
    ((SchwartzMap.fourierTransformCLE ℂ v).integrable.norm).const_mul C
  have hNorm := norm_integral_le_of_norm_le hFrequency
    (Eventually.of_forall (classicalFrequency_norm_le hBounds v x))
  simpa only [integral_const_mul, D] using hNorm

private theorem classicalLeftPairing_add {p q : E → E → ℂ}
    (hp : Measurable (uncurry p)) (hq : Measurable (uncurry q))
    (C D : ℝ)
    (hP : ∀ x ξ, ‖p x ξ‖ ≤ C) (hQ : ∀ x ξ, ‖q x ξ‖ ≤ D)
    (f v : SchwartzMap E ℂ) :
    classicalLeftPairing (fun x ξ => p x ξ + q x ξ) f v =
      classicalLeftPairing p f v + classicalLeftPairing q f v := by
  have hAct (x : E) : firstOrderAction (fun x ξ => p x ξ + q x ξ) v x =
      firstOrderAction p v x + firstOrderAction q v x := by
    simp only [firstOrderAction_classicalFrequency]
    rw [← integral_add (classicalFrequency_integrable hp hP v x) (classicalFrequency_integrable hq hQ v x)]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by simp only [classicalFrequency, add_mul, mul_add]
  unfold classicalLeftPairing
  simp only [hAct, mul_add]
  exact integral_add (classicalLeftPairing_integrable hp hP f v)
    (classicalLeftPairing_integrable hq hQ f v)

/-- The exact full symbol pairing implies the represented classical hypothesis.
The remainder is obtained directly from estimates above an arbitrary fixed radius. -/
theorem hasLocalClassicalRepresentation_of_fullSymbolPairing
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (b a : E → E → ℂ)
    (S L : Set E) (hS : IsCompact S) (hL : IsCompact L)
    (hb : ∀ ξ, tsupport (fun x => b x ξ) ⊆ S)
    (ha : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hbDiff : ContDiff ℝ ∞ (uncurry b))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (haZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (R : ℝ) (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (hAct : ∀ f v : SchwartzMap E ℂ, tsupport (v : E → ℂ) ⊆ L →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) = classicalLeftPairing b f v) :
    HasLocalClassicalRepresentation T a L := by
  let p := infraredAngularPrincipal a
  let q := classicalFullRemainder b a
  have hp : ContDiff ℝ ∞ (uncurry p) := contDiff_uncurry_infraredAngularPrincipal haDiff
  have hq : ContDiff ℝ ∞ (uncurry q) := hbDiff.sub hp
  have hDecay := orderMinusOneBounds_classicalFullRemainder hS hb ha hbDiff haDiff R hLarge
  obtain ⟨C, _, hA⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS ha haDiff haZero hDegree 0
  have hP (x ξ : E) : ‖p x ξ‖ ≤ C := by
    have hc : ‖(1 : ℂ) - (radialCore ξ : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ξ))]
      exact sub_le_self _ (radialCore_nonneg ξ)
    rw [show p x ξ = ((1 : ℂ) - (radialCore ξ : ℂ)) * a x ξ from rfl, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (by
      simpa only [norm_iteratedFDeriv_zero] using hA x ξ)
  obtain ⟨D, _, hBound⟩ := hDecay 0
  have hQ (x ξ : E) : ‖q x ξ‖ ≤ D := by
    have hd := hBound x ξ
    rw [norm_iteratedFDeriv_zero] at hd
    exact (le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg ξ))).trans hd
  refine hasLocalClassicalRepresentation_of_actualFullSymbol T a q S L hS hL
    (classicalFullRemainder_support hS hb ha) hq hDecay ?_
  intro f v hv
  rw [hAct f v hv]
  have hSplit : b = fun x ξ => p x ξ + q x ξ := by
    funext x ξ
    change b x ξ = p x ξ + (b x ξ - p x ξ)
    ring
  calc
    _ = classicalLeftPairing (fun x ξ => p x ξ + q x ξ) f v := congrArg (fun d => classicalLeftPairing d f v) hSplit
    _ = _ := classicalLeftPairing_add hp.continuous.measurable hq.continuous.measurable C D hP hQ f v

end Burnett.Microlocal.Overlap
