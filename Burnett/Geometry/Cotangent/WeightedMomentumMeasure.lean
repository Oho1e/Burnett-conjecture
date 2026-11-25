import Burnett.Geometry.Cotangent.RadialTestCalculus

set_option autoImplicit false
noncomputable section

namespace Burnett.FullMomentumLift

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual radial-coordinate Hamilton vector field `ρ X + ρ² k ∂ρ`. -/
def radialHamilton (X : E → E) (k : E → ℝ) (b : E × ℝ → ℝ) (p : E) (ρ : ℝ) : ℝ :=
  fderiv ℝ b (p, ρ) (ρ • X p, ρ ^ 2 * k p)

def scaleSection (s : E → ℝ) (p : E) : E × ℝ := (p, s p)

def sectionTrace (s : E → ℝ) (b : E × ℝ → ℝ) (p : E) : ℝ := b (scaleSection s p)

def homogeneousExtension (f : E → ℝ) (z : E × ℝ) : ℝ := z.2 * f z.1

def unitTransport (X : E → E) (k : E → ℝ) (f : E → ℝ) (p : E) : ℝ :=
  fderiv ℝ f p (X p) + k p * f p

def graphResidual (s : E → ℝ) (z : E × ℝ) : ℝ := z.2 - s z.1

theorem radialHamilton_graphResidual (X : E → E) (k s : E → ℝ) (p : E) (ρ : ℝ)
    (hs : DifferentiableAt ℝ s p) :
    radialHamilton X k (graphResidual s) p ρ = ρ ^ 2 * k p - ρ * fderiv ℝ s p (X p) := by
  have hρ : HasFDerivAt (fun z : E × ℝ => z.2) (ContinuousLinearMap.snd ℝ E ℝ) (p, ρ) :=
    hasFDerivAt_snd
  have hsp : HasFDerivAt (fun z : E × ℝ => s z.1)
      ((fderiv ℝ s p).comp (ContinuousLinearMap.fst ℝ E ℝ)) (p, ρ) :=
    hs.hasFDerivAt.comp (p, ρ) hasFDerivAt_fst
  have hg : HasFDerivAt (graphResidual s)
      ((ContinuousLinearMap.snd ℝ E ℝ) -
        (fderiv ℝ s p).comp (ContinuousLinearMap.fst ℝ E ℝ)) (p, ρ) := hρ.sub hsp
  unfold radialHamilton
  rw [hg.fderiv]
  change ρ ^ 2 * k p - fderiv ℝ s p (ρ • X p) = _
  rw [map_smul]
  rfl

/-- Genuine tangency of the invariant graph is equivalent to the radial drift law. -/
theorem graph_tangent_iff_scale_drift (X : E → E) (k s : E → ℝ) (p : E)
    (hs : DifferentiableAt ℝ s p) (hne : s p ≠ 0) :
    radialHamilton X k (graphResidual s) p (s p) = 0 ↔
      fderiv ℝ s p (X p) = k p * s p := by
  rw [radialHamilton_graphResidual X k s p (s p) hs]
  constructor
  · intro h
    have he : s p * (s p * k p - fderiv ℝ s p (X p)) = 0 := by
      calc
        _ = s p ^ 2 * k p - s p * fderiv ℝ s p (X p) := by ring
        _ = 0 := h
    have hz := (mul_eq_zero.mp he).resolve_left hne
    simpa only [mul_comm] using (sub_eq_zero.mp hz).symm
  · intro h
    rw [h]
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem homogeneousExtension_positive_one (f : E → ℝ) (p : E) (ρ t : ℝ) :
    homogeneousExtension f (p, t * ρ) = t * homogeneousExtension f (p, ρ) := by
  unfold homogeneousExtension
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem homogeneousExtension_section (s B : E → ℝ) (p : E) (hs : s p ≠ 0) :
    homogeneousExtension (fun x => B x / s x) (scaleSection s p) = B p := by
  simp only [homogeneousExtension, scaleSection]
  field_simp

theorem sectionTrace_hasFDerivAt (s : E → ℝ) (b : E × ℝ → ℝ) (p : E)
    (hs : DifferentiableAt ℝ s p) (hb : DifferentiableAt ℝ b (scaleSection s p)) :
    HasFDerivAt (sectionTrace s b)
      ((fderiv ℝ b (scaleSection s p)).comp
        ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ s p))) p := by
  have hL := (hasFDerivAt_id p).prodMk hs.hasFDerivAt
  exact hb.hasFDerivAt.comp p hL

theorem homogeneousExtension_hasFDerivAt (f : E → ℝ) (p : E) (ρ : ℝ)
    (hf : DifferentiableAt ℝ f p) :
    HasFDerivAt (homogeneousExtension f)
      (ρ • ((fderiv ℝ f p).comp (ContinuousLinearMap.fst ℝ E ℝ)) +
        f p • (ContinuousLinearMap.snd ℝ E ℝ)) (p, ρ) := by
  have hρ : HasFDerivAt (fun z : E × ℝ => z.2) (ContinuousLinearMap.snd ℝ E ℝ) (p, ρ) :=
    hasFDerivAt_snd
  have hfp : HasFDerivAt (fun z : E × ℝ => f z.1)
      ((fderiv ℝ f p).comp (ContinuousLinearMap.fst ℝ E ℝ)) (p, ρ) :=
    hf.hasFDerivAt.comp (p, ρ) hasFDerivAt_fst
  exact hρ.fun_mul hfp

theorem radialHamilton_homogeneousExtension (X : E → E) (k f : E → ℝ) (p : E) (ρ : ℝ)
    (hf : DifferentiableAt ℝ f p) :
    radialHamilton X k (homogeneousExtension f) p ρ = ρ ^ 2 * unitTransport X k f p := by
  unfold radialHamilton
  rw [(homogeneousExtension_hasFDerivAt f p ρ hf).fderiv]
  change ρ * fderiv ℝ f p (ρ • X p) + f p * (ρ ^ 2 * k p) =
    ρ ^ 2 * (fderiv ℝ f p (X p) + k p * f p)
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

theorem radialHamilton_homogeneousExtension_unit (X : E → E) (k f : E → ℝ) (p : E)
    (hf : DifferentiableAt ℝ f p) :
    radialHamilton X k (homogeneousExtension f) p 1 = unitTransport X k f p := by
  simpa only [one_pow, one_mul] using radialHamilton_homogeneousExtension X k f p 1 hf

theorem radialHamilton_section (X : E → E) (k s : E → ℝ) (b : E × ℝ → ℝ) (p : E)
    (hs : DifferentiableAt ℝ s p) (hb : DifferentiableAt ℝ b (scaleSection s p))
    (htangent : fderiv ℝ s p (X p) = k p * s p) :
    radialHamilton X k b p (s p) = s p * fderiv ℝ (sectionTrace s b) p (X p) := by
  have hB := sectionTrace_hasFDerivAt s b p hs hb
  have hv : (s p • X p, s p ^ 2 * k p) =
      s p • (((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ s p)) (X p)) := by
    change (s p • X p, s p ^ 2 * k p) = (s p • X p, s p * fderiv ℝ s p (X p))
    rw [htangent]
    congr 1
    ring
  unfold radialHamilton
  change fderiv ℝ b (scaleSection s p) (s p • X p, s p ^ 2 * k p) = _
  rw [hv, map_smul, hB.fderiv, ContinuousLinearMap.comp_apply]
  rfl

theorem quotient_hasFDerivAt (B s : E → ℝ) (p : E)
    (hB : DifferentiableAt ℝ B p) (hs : DifferentiableAt ℝ s p) (hne : s p ≠ 0) :
    HasFDerivAt (fun x => B x / s x)
      (B p • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(s p ^ 2)⁻¹)).comp (fderiv ℝ s p)) +
        (s p)⁻¹ • fderiv ℝ B p) p := by
  have hi := (hasFDerivAt_inv hne).comp p hs.hasFDerivAt
  simpa only [div_eq_mul_inv, Function.comp_def] using hB.hasFDerivAt.fun_mul hi

theorem directional_quotient (B s : E → ℝ) (p v : E)
    (hB : DifferentiableAt ℝ B p) (hs : DifferentiableAt ℝ s p) (hne : s p ≠ 0) :
    fderiv ℝ (fun x => B x / s x) p v =
      (fderiv ℝ B p v * s p - B p * fderiv ℝ s p v) / s p ^ 2 := by
  rw [(quotient_hasFDerivAt B s p hB hs hne).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  field_simp
  ring

/-- The radial drift is essential: `Xs = k s` gives the exact quotient transport law. -/
theorem unitTransport_quotient (X : E → E) (k B s : E → ℝ) (p : E)
    (hB : DifferentiableAt ℝ B p) (hs : DifferentiableAt ℝ s p) (hne : s p ≠ 0)
    (htangent : fderiv ℝ s p (X p) = k p * s p) :
    unitTransport X k (fun x => B x / s x) p = (s p)⁻¹ * fderiv ℝ B p (X p) := by
  unfold unitTransport
  rw [directional_quotient B s p (X p) hB hs hne, htangent]
  field_simp
  ring

theorem weighted_radial_transport (X : E → E) (k s : E → ℝ) (b : E × ℝ → ℝ) (p : E)
    (hs : DifferentiableAt ℝ s p) (hb : DifferentiableAt ℝ b (scaleSection s p))
    (hne : s p ≠ 0) (htangent : fderiv ℝ s p (X p) = k p * s p) :
    (s p ^ 2)⁻¹ * radialHamilton X k b p (s p) =
      unitTransport X k (fun x => sectionTrace s b x / s x) p := by
  rw [radialHamilton_section X k s b p hs hb htangent,
    unitTransport_quotient X k (sectionTrace s b) s p
      (sectionTrace_hasFDerivAt s b p hs hb).differentiableAt hs hne htangent]
  field_simp

/-- The exact source identity for the explicitly constructed homogeneous cone test. -/
theorem weighted_full_vs_homogeneous (X : E → E) (k s : E → ℝ) (b : E × ℝ → ℝ) (p : E)
    (hs : DifferentiableAt ℝ s p) (hb : DifferentiableAt ℝ b (scaleSection s p))
    (hne : s p ≠ 0) (htangent : fderiv ℝ s p (X p) = k p * s p) :
    (s p ^ 2)⁻¹ * radialHamilton X k b p (s p) =
      radialHamilton X k (homogeneousExtension (fun x => sectionTrace s b x / s x)) p 1 := by
  rw [weighted_radial_transport X k s b p hs hb hne htangent,
    radialHamilton_homogeneousExtension_unit X k _ p
      (quotient_hasFDerivAt (sectionTrace s b) s p
        (sectionTrace_hasFDerivAt s b p hs hb).differentiableAt hs hne).differentiableAt]

end Burnett.FullMomentumLift

namespace Burnett.FullMomentumLift

open Set MeasureTheory Filter
open scoped ENNReal NNReal

variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]

/-- The genuine nonnegative density representing `s⁻²`. -/
def inverseSquareWeight (s : Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  ⟨(s ω ^ 2)⁻¹, inv_nonneg.mpr (sq_nonneg _)⟩

omit [MeasurableSpace Ω] in
@[simp] theorem inverseSquareWeight_coe (s : Ω → ℝ) (ω : Ω) :
    (inverseSquareWeight s ω : ℝ) = (s ω ^ 2)⁻¹ := rfl

theorem inverseSquareWeight_measurable (s : Ω → ℝ) (hs : Measurable s) :
    Measurable (inverseSquareWeight s) :=
  ((hs.pow_const 2).inv).subtype_mk

/-- The actual weighted pushforward, not a supplied full-momentum measure. -/
def weightedLift (μ : Measure Ω) (L : Ω → P) (s : Ω → ℝ) : Measure P :=
  (μ.withDensity (fun ω => (inverseSquareWeight s ω : ℝ≥0∞))).map L

theorem weightedLift_concentrated (μ : Measure Ω) (L : Ω → P) (s : Ω → ℝ)
    (hL : Measurable L) (A : Set P) (hA : MeasurableSet A) (hrange : ∀ ω, L ω ∈ A) :
    weightedLift μ L s Aᶜ = 0 := by
  rw [weightedLift, Measure.map_apply hL hA.compl]
  have he : L ⁻¹' Aᶜ = ∅ := by
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact hrange ω
  rw [he, measure_empty]

theorem weightedLift_map {Q : Type*} [MeasurableSpace Q] (μ : Measure Ω) (L : Ω → P) (s : Ω → ℝ)
    (F : P → Q) (hL : Measurable L) (hF : Measurable F) :
    (weightedLift μ L s).map F = weightedLift μ (F ∘ L) s := by
  rw [weightedLift, Measure.map_map hF hL]
  rfl

omit [MeasurableSpace Ω] in
theorem inverseSquareWeight_cancel (s : Ω → ℝ) (ω : Ω) (hs : s ω ≠ 0) (z : ℝ) :
    (inverseSquareWeight s ω : ℝ) * (s ω ^ 2 * z) = z := by
  rw [inverseSquareWeight_coe]
  field_simp

theorem weightedLift_pairing (μ : Measure Ω) (L : Ω → P) (s : Ω → ℝ)
    (hL : Measurable L) (hs : Measurable s) (F : P → ℝ) (hF : Measurable F) :
    (Integrable F (weightedLift μ L s) ↔
      Integrable (fun ω => (s ω ^ 2)⁻¹ * F (L ω)) μ) ∧
    (∫ p, F p ∂weightedLift μ L s) = ∫ ω, (s ω ^ 2)⁻¹ * F (L ω) ∂μ := by
  have hw := inverseSquareWeight_measurable s hs
  constructor
  · rw [weightedLift, integrable_map_measure hF.aestronglyMeasurable hL.aemeasurable,
      integrable_withDensity_iff_integrable_smul hw]
    rfl
  · rw [weightedLift, integral_map hL.aemeasurable hF.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hw]
    rfl

theorem weightedLift_pairing_cancel (μ : Measure Ω) (L : Ω → P) (s : Ω → ℝ)
    (hL : Measurable L) (hs : Measurable s) (hsne : ∀ ω, s ω ≠ 0)
    (F : P → ℝ) (hF : Measurable F) (J : Ω → ℝ)
    (hscale : ∀ ω, F (L ω) = s ω ^ 2 * J ω) :
    (Integrable F (weightedLift μ L s) ↔ Integrable J μ) ∧
      (∫ p, F p ∂weightedLift μ L s) = ∫ ω, J ω ∂μ := by
  have he : (fun ω => (s ω ^ 2)⁻¹ * F (L ω)) = J := by
    funext ω
    rw [hscale ω]
    exact inverseSquareWeight_cancel s ω (hsne ω) (J ω)
  simpa only [he] using weightedLift_pairing μ L s hL hs F hF

theorem weightedLift_lintegral_cancel (μ : Measure Ω) (L : Ω → P) (s : Ω → ℝ)
    (hL : Measurable L) (hs : Measurable s) (hsne : ∀ ω, s ω ≠ 0)
    (F : P → ℝ) (hF : Measurable F) (J : Ω → ℝ)
    (hscale : ∀ ω, F (L ω) = s ω ^ 2 * J ω) :
    (∫⁻ p, ENNReal.ofReal (F p) ∂weightedLift μ L s) = ∫⁻ ω, ENNReal.ofReal (J ω) ∂μ := by
  have hw := inverseSquareWeight_measurable s hs
  rw [weightedLift, lintegral_map hF.ennreal_ofReal hL]
  have hFL : Measurable (fun ω => ENNReal.ofReal (F (L ω))) := (hF.comp hL).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul μ (f := fun ω => (inverseSquareWeight s ω : ℝ≥0∞))
    (g := fun ω => ENNReal.ofReal (F (L ω))) hw.coe_nnreal_ennreal hFL]
  apply lintegral_congr
  intro ω
  have hwcoe : (inverseSquareWeight s ω : ℝ≥0∞) = ENNReal.ofReal ((s ω ^ 2)⁻¹) := by
    change (inverseSquareWeight s ω : ℝ≥0∞) = ENNReal.ofReal (inverseSquareWeight s ω : ℝ)
    exact ENNReal.ofReal_coe_nnreal.symm
  change (inverseSquareWeight s ω : ℝ≥0∞) * ENNReal.ofReal (F (L ω)) = ENNReal.ofReal (J ω)
  rw [hwcoe, ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg (s ω)))]
  congr 1
  rw [hscale ω]
  exact inverseSquareWeight_cancel s ω (hsne ω) (J ω)

end Burnett.FullMomentumLift

namespace Burnett.FullMomentumLift

open Set MeasureTheory Filter
open scoped ENNReal NNReal

variable {Ω B V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The actual fibre scaling map `(x,ω) ↦ (x,sω)`. -/
def covectorLift (u : Ω → B × V) (s : Ω → ℝ) (ω : Ω) : B × V :=
  ((u ω).1, s ω • (u ω).2)

def radialRealization (u : Ω → B × V) (z : Ω × ℝ) : B × V :=
  ((u z.1).1, z.2 • (u z.1).2)

theorem radialRealization_section (u : Ω → B × V) (s : Ω → ℝ) :
    radialRealization u ∘ scaleSection s = covectorLift u s := rfl

/-- The true quadratic value of the supplied fibre bilinear form. -/
def quadraticValue (Q : B → LinearMap.BilinForm ℝ V) (p : B × V) : ℝ := Q p.1 p.2 p.2

theorem quadraticValue_covectorLift (Q : B → LinearMap.BilinForm ℝ V)
    (u : Ω → B × V) (s : Ω → ℝ) (ω : Ω) :
    quadraticValue Q (covectorLift u s ω) = s ω ^ 2 * quadraticValue Q (u ω) := by
  change Q (u ω).1 (s ω • (u ω).2) (s ω • (u ω).2) =
    s ω ^ 2 * Q (u ω).1 (u ω).2 (u ω).2
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem covectorLift_null (G : B → LinearMap.BilinForm ℝ V)
    (u : Ω → B × V) (s : Ω → ℝ) (hnull : ∀ ω, quadraticValue G (u ω) = 0) (ω : Ω) :
    quadraticValue G (covectorLift u s ω) = 0 := by
  rw [quadraticValue_covectorLift, hnull ω, mul_zero]

theorem covectorLift_nonzero (Q : B → LinearMap.BilinForm ℝ V)
    (u : Ω → B × V) (s : Ω → ℝ) (hunit : ∀ ω, quadraticValue Q (u ω) = 1)
    (hs : ∀ ω, s ω ≠ 0) (ω : Ω) : (covectorLift u s ω).2 ≠ 0 := by
  intro he
  have hξ : (u ω).2 = 0 := by
    have hi := congrArg (fun v : V => (s ω)⁻¹ • v) he
    simpa only [covectorLift, smul_smul, inv_mul_cancel₀ (hs ω), one_smul, smul_zero] using hi
  have hu := hunit ω
  simp only [quadraticValue, hξ, map_zero] at hu
  norm_num at hu

section Measurable

variable [MeasurableSpace Ω] [MeasurableSpace B] [MeasurableSpace V] [MeasurableSMul₂ ℝ V]

theorem covectorLift_measurable (u : Ω → B × V) (s : Ω → ℝ)
    (hu : Measurable u) (hs : Measurable s) : Measurable (covectorLift u s) :=
  hu.fst.prodMk (hs.smul hu.snd)

theorem radialRealization_measurable (u : Ω → B × V) (hu : Measurable u) :
    Measurable (radialRealization u) :=
  (hu.fst.comp measurable_fst).prodMk (measurable_snd.smul (hu.snd.comp measurable_fst))

/-- The radial chart graph and full covector lift are provably the same weighted witness. -/
theorem covectorLift_measure_eq_map_section (μ : Measure Ω) (u : Ω → B × V) (s : Ω → ℝ)
    (hu : Measurable u) (hs : Measurable s) :
    (weightedLift μ (scaleSection s) s).map (radialRealization u) =
      weightedLift μ (covectorLift u s) s := by
  rw [weightedLift_map μ (scaleSection s) s (radialRealization u)
    (measurable_id.prodMk hs) (radialRealization_measurable u hu), radialRealization_section]

/-- Every genuine quadratic moment is preserved by the weighted fibre scaling. -/
theorem covectorLift_quadratic_moment (μ : Measure Ω) (u : Ω → B × V) (s : Ω → ℝ)
    (hu : Measurable u) (hs : Measurable s) (hsne : ∀ ω, s ω ≠ 0)
    (Q : B → LinearMap.BilinForm ℝ V) (hQ : Measurable (quadraticValue Q)) :
    (Integrable (quadraticValue Q) (weightedLift μ (covectorLift u s) s) ↔
      Integrable (fun ω => quadraticValue Q (u ω)) μ) ∧
    (∫ p, quadraticValue Q p ∂weightedLift μ (covectorLift u s) s) =
      ∫ ω, quadraticValue Q (u ω) ∂μ :=
  weightedLift_pairing_cancel μ (covectorLift u s) s (covectorLift_measurable u s hu hs) hs hsne
    (quadraticValue Q) hQ (fun ω => quadraticValue Q (u ω)) (quadraticValue_covectorLift Q u s)

/-- Exact local second moment: the inverse-square density cancels the actual quadratic scaling. -/
theorem covectorLift_local_second_moment (μ : Measure Ω) (u : Ω → B × V) (s : Ω → ℝ)
    (hu : Measurable u) (hs : Measurable s) (hsne : ∀ ω, s ω ≠ 0)
    (Q : B → LinearMap.BilinForm ℝ V) (hQ : Measurable (quadraticValue Q))
    (hunit : ∀ ω, quadraticValue Q (u ω) = 1) (K : Set B) (hK : MeasurableSet K) :
    (∫⁻ p in {p : B × V | p.1 ∈ K}, ENNReal.ofReal (quadraticValue Q p)
      ∂weightedLift μ (covectorLift u s) s) = μ {ω | (u ω).1 ∈ K} := by
  classical
  let Z : Set (B × V) := {p | p.1 ∈ K}
  let Y : Set Ω := {ω | (u ω).1 ∈ K}
  let F := Z.indicator (quadraticValue Q)
  let J := Y.indicator (fun _ => (1 : ℝ))
  have hZ : MeasurableSet Z := hK.preimage measurable_fst
  have hY : MeasurableSet Y := hK.preimage hu.fst
  have hF : Measurable F := hQ.indicator hZ
  have he (ω : Ω) : F (covectorLift u s ω) = s ω ^ 2 * J ω := by
    by_cases hω : (u ω).1 ∈ K
    · simp only [F, J, Z, Y, mem_setOf_eq, covectorLift, hω, indicator_of_mem]
      exact (quadraticValue_covectorLift Q u s ω).trans (by rw [hunit ω, mul_one])
    · simp [F, J, Z, Y, covectorLift, hω]
  have hm := weightedLift_lintegral_cancel μ (covectorLift u s) s
    (covectorLift_measurable u s hu hs) hs hsne F hF J he
  have hFI : (fun p => ENNReal.ofReal (F p)) = Z.indicator (fun p => ENNReal.ofReal (quadraticValue Q p)) := by
    funext p
    by_cases hp : p ∈ Z <;> simp [F, hp]
  have hJI : (fun ω => ENNReal.ofReal (J ω)) = Y.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases hω : ω ∈ Y <;> simp [J, hω]
  rw [hFI, hJI, lintegral_indicator hZ, lintegral_indicator hY, lintegral_one,
    Measure.restrict_apply_univ] at hm
  exact hm

theorem covectorLift_local_second_moment_finite (μ : Measure Ω) (u : Ω → B × V) (s : Ω → ℝ)
    (hu : Measurable u) (hs : Measurable s) (hsne : ∀ ω, s ω ≠ 0)
    (Q : B → LinearMap.BilinForm ℝ V) (hQ : Measurable (quadraticValue Q))
    (hunit : ∀ ω, quadraticValue Q (u ω) = 1) (K : Set B) (hK : MeasurableSet K)
    (hfinite : μ {ω | (u ω).1 ∈ K} < ∞) :
    (∫⁻ p in {p : B × V | p.1 ∈ K}, ENNReal.ofReal (quadraticValue Q p)
      ∂weightedLift μ (covectorLift u s) s) < ∞ := by
  rw [covectorLift_local_second_moment μ u s hu hs hsne Q hQ hunit K hK]
  exact hfinite

theorem covectorLift_local_second_moment_integrable (μ : Measure Ω) (u : Ω → B × V) (s : Ω → ℝ)
    (hu : Measurable u) (hs : Measurable s) (hsne : ∀ ω, s ω ≠ 0)
    (Q : B → LinearMap.BilinForm ℝ V) (hQ : Measurable (quadraticValue Q))
    (hunit : ∀ ω, quadraticValue Q (u ω) = 1) (K : Set B) (hK : MeasurableSet K)
    (hfinite : μ {ω | (u ω).1 ∈ K} < ∞) :
    IntegrableOn (quadraticValue Q) {p : B × V | p.1 ∈ K}
      (weightedLift μ (covectorLift u s) s) := by
  classical
  let Z : Set (B × V) := {p | p.1 ∈ K}
  let Y : Set Ω := {ω | (u ω).1 ∈ K}
  let F := Z.indicator (quadraticValue Q)
  let J := Y.indicator (fun _ => (1 : ℝ))
  have hZ : MeasurableSet Z := hK.preimage measurable_fst
  have hY : MeasurableSet Y := hK.preimage hu.fst
  have hF : Measurable F := hQ.indicator hZ
  have he (ω : Ω) : F (covectorLift u s ω) = s ω ^ 2 * J ω := by
    by_cases hω : (u ω).1 ∈ K
    · simp only [F, J, Z, Y, mem_setOf_eq, covectorLift, hω, indicator_of_mem]
      exact (quadraticValue_covectorLift Q u s ω).trans (by rw [hunit ω, mul_one])
    · simp [F, J, Z, Y, covectorLift, hω]
  have hJ : Integrable J μ :=
    (integrableOn_const (μ := μ) (s := Y) (C := (1 : ℝ)) hfinite.ne).integrable_indicator hY
  have hi := (weightedLift_pairing_cancel μ (covectorLift u s) s
    (covectorLift_measurable u s hu hs) hs hsne F hF J he).1.mpr hJ
  exact (integrable_indicator_iff hZ).mp hi

end Measurable
end Burnett.FullMomentumLift

namespace Burnett.FullMomentumLift

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

/-- Transport of the full test is derived from transport of its explicitly constructed
one-homogeneous cone test, with the radial drift retained. -/
theorem full_transport_of_homogeneous_transport (μ : Measure E)
    (X : E → E) (k s : E → ℝ) (b : E × ℝ → ℝ) (hs : Measurable s)
    (hfull : Measurable (fun z : E × ℝ => radialHamilton X k b z.1 z.2))
    (hgood : ∀ᵐ p ∂μ, DifferentiableAt ℝ s p ∧ DifferentiableAt ℝ b (scaleSection s p) ∧
      s p ≠ 0 ∧ fderiv ℝ s p (X p) = k p * s p)
    (hunit : Integrable (fun p => radialHamilton X k
      (homogeneousExtension (fun x => sectionTrace s b x / s x)) p 1) μ)
    (hzero : (∫ p, radialHamilton X k
      (homogeneousExtension (fun x => sectionTrace s b x / s x)) p 1 ∂μ) = 0) :
    Integrable (fun z : E × ℝ => radialHamilton X k b z.1 z.2)
      (weightedLift μ (scaleSection s) s) ∧
    (∫ z, radialHamilton X k b z.1 z.2 ∂weightedLift μ (scaleSection s) s) = 0 := by
  have hL : Measurable (scaleSection s) := measurable_id.prodMk hs
  have he : (fun p => (s p ^ 2)⁻¹ * radialHamilton X k b p (s p)) =ᵐ[μ]
      (fun p => radialHamilton X k (homogeneousExtension (fun x => sectionTrace s b x / s x)) p 1) := by
    filter_upwards [hgood] with p hp
    exact weighted_full_vs_homogeneous X k s b p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  have hm := weightedLift_pairing μ (scaleSection s) s hL hs
    (fun z : E × ℝ => radialHamilton X k b z.1 z.2) hfull
  have hi : Integrable (fun p => (s p ^ 2)⁻¹ * radialHamilton X k b p (s p)) μ :=
    hunit.congr he.symm
  exact ⟨hm.1.mpr hi, hm.2.trans ((integral_congr_ae he).trans hzero)⟩

end Burnett.FullMomentumLift

namespace Burnett.FullMomentumLift

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

section CompactBase

variable {Ω P B : Type*} [TopologicalSpace Ω] [TopologicalSpace P] [T2Space P] [TopologicalSpace B]

/-- Compactness of the unit-ray bundle over compact bases forces compact lift preimages. -/
theorem lift_compact_preimage_of_base_compact (πΩ : Ω → B) (πP : P → B) (L : Ω → P)
    (hπ : Continuous πP) (hL : Continuous L) (hbase : ∀ ω, πP (L ω) = πΩ ω)
    (hcompact : ∀ K : Set B, IsCompact K → IsCompact (πΩ ⁻¹' K))
    (K : Set P) (hK : IsCompact K) : IsCompact (L ⁻¹' K) := by
  apply (hcompact (πP '' K) (hK.image hπ)).of_isClosed_subset (hK.isClosed.preimage hL)
  intro ω hω
  exact ⟨L ω, hω, hbase ω⟩

end CompactBase

section Regular

variable {Ω P : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [T2Space P]

omit [MeasurableSpace Ω] [BorelSpace Ω] in
theorem inverseSquareWeight_continuous (s : Ω → ℝ) (hs : Continuous s) (hne : ∀ ω, s ω ≠ 0) :
    Continuous (inverseSquareWeight s) :=
  ((hs.pow 2).inv₀ (fun ω => pow_ne_zero 2 (hne ω))).subtype_mk
    (fun ω => inv_nonneg.mpr (sq_nonneg (s ω)))

/-- Finite-on-compacts of the lift is proved from continuity and compact lift preimages. -/
theorem weightedLift_finiteOnCompacts (μ : Measure Ω) [IsLocallyFiniteMeasure μ]
    (L : Ω → P) (s : Ω → ℝ) (hL : Continuous L) (hs : Continuous s) (hne : ∀ ω, s ω ≠ 0)
    (hcompact : ∀ K : Set P, IsCompact K → IsCompact (L ⁻¹' K)) :
    IsFiniteMeasureOnCompacts (weightedLift μ L s) := by
  haveI : IsLocallyFiniteMeasure (μ.withDensity (fun ω => (inverseSquareWeight s ω : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe (inverseSquareWeight_continuous s hs hne)
  refine ⟨fun K hK => ?_⟩
  rw [weightedLift, Measure.map_apply hL.measurable hK.measurableSet]
  exact (hcompact K hK).measure_lt_top

theorem weightedLift_locallyFinite [WeaklyLocallyCompactSpace P]
    (μ : Measure Ω) [IsLocallyFiniteMeasure μ] (L : Ω → P) (s : Ω → ℝ)
    (hL : Continuous L) (hs : Continuous s) (hne : ∀ ω, s ω ≠ 0)
    (hcompact : ∀ K : Set P, IsCompact K → IsCompact (L ⁻¹' K)) :
    IsLocallyFiniteMeasure (weightedLift μ L s) := by
  haveI := weightedLift_finiteOnCompacts μ L s hL hs hne hcompact
  infer_instance

theorem weightedLift_regular [WeaklyLocallyCompactSpace P] [PseudoMetrizableSpace P] [SigmaCompactSpace P]
    (μ : Measure Ω) [IsLocallyFiniteMeasure μ] (L : Ω → P) (s : Ω → ℝ)
    (hL : Continuous L) (hs : Continuous s) (hne : ∀ ω, s ω ≠ 0)
    (hcompact : ∀ K : Set P, IsCompact K → IsCompact (L ⁻¹' K)) :
    (weightedLift μ L s).Regular := by
  haveI := weightedLift_locallyFinite μ L s hL hs hne hcompact
  infer_instance

omit [BorelSpace Ω] in
theorem unitMeasure_finite_over_compact {B : Type*} [TopologicalSpace B]
    (μ : Measure Ω) [IsLocallyFiniteMeasure μ] (πΩ : Ω → B)
    (hcompact : ∀ K : Set B, IsCompact K → IsCompact (πΩ ⁻¹' K))
    (K : Set B) (hK : IsCompact K) : μ (πΩ ⁻¹' K) < ∞ :=
  (hcompact K hK).measure_lt_top

end Regular
end Burnett.FullMomentumLift

namespace Burnett.FullMomentumLift

open Set MeasureTheory
open scoped ENNReal NNReal

variable {Ω B V : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [TopologicalSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
  [AddCommGroup V] [Module ℝ V] [MeasurableSpace V] [MeasurableSMul₂ ℝ V]

/-- Genuine source local finiteness and compact unit bundles give every required local moment. -/
theorem covectorLift_local_moment_of_compact_unit_bundle (μ : Measure Ω) [IsLocallyFiniteMeasure μ]
    (u : Ω → B × V) (s : Ω → ℝ) (hu : Measurable u) (hs : Measurable s)
    (hsne : ∀ ω, s ω ≠ 0) (Q : B → LinearMap.BilinForm ℝ V)
    (hQ : Measurable (quadraticValue Q)) (hunit : ∀ ω, quadraticValue Q (u ω) = 1)
    (hcompact : ∀ K : Set B, IsCompact K → IsCompact {ω | (u ω).1 ∈ K})
    (K : Set B) (hK : IsCompact K) :
    ((∫⁻ p in {p : B × V | p.1 ∈ K}, ENNReal.ofReal (quadraticValue Q p)
      ∂weightedLift μ (covectorLift u s) s) = μ {ω | (u ω).1 ∈ K}) ∧
    ((∫⁻ p in {p : B × V | p.1 ∈ K}, ENNReal.ofReal (quadraticValue Q p)
      ∂weightedLift μ (covectorLift u s) s) < ∞) ∧
    IntegrableOn (quadraticValue Q) {p : B × V | p.1 ∈ K}
      (weightedLift μ (covectorLift u s) s) := by
  have hfinite : μ {ω | (u ω).1 ∈ K} < ∞ := (hcompact K hK).measure_lt_top
  exact ⟨covectorLift_local_second_moment μ u s hu hs hsne Q hQ hunit K hK.measurableSet,
    covectorLift_local_second_moment_finite μ u s hu hs hsne Q hQ hunit K hK.measurableSet hfinite,
    covectorLift_local_second_moment_integrable μ u s hu hs hsne Q hQ hunit K hK.measurableSet hfinite⟩

end Burnett.FullMomentumLift

namespace Burnett.FullMomentumLift

open Set

variable {Ω P B : Type*} [TopologicalSpace Ω] [TopologicalSpace P] [TopologicalSpace B]

theorem quotientTrace_tsupport_subset (L : Ω → P) (hL : Continuous L) (b : P → ℝ) (s : Ω → ℝ) :
    tsupport (fun ω => b (L ω) / s ω) ⊆ L ⁻¹' tsupport b := by
  change closure (Function.support (fun ω => b (L ω) / s ω)) ⊆ L ⁻¹' tsupport b
  apply closure_minimal _ ((isClosed_tsupport b).preimage hL)
  intro ω hω
  by_contra hn
  have hb : b (L ω) = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hω (by simp only [hb, zero_div])

theorem quotientTrace_hasCompactSupport (L : Ω → P) (hL : Continuous L)
    (hcompact : ∀ K : Set P, IsCompact K → IsCompact (L ⁻¹' K))
    (b : P → ℝ) (hb : HasCompactSupport b) (s : Ω → ℝ) :
    HasCompactSupport (fun ω => b (L ω) / s ω) :=
  (hcompact (tsupport b) hb).of_isClosed_subset (isClosed_tsupport _)
    (quotientTrace_tsupport_subset L hL b s)

theorem homogeneousExtension_tsupport_subset (f : Ω → ℝ) :
    tsupport (homogeneousExtension f) ⊆ Prod.fst ⁻¹' tsupport f := by
  change closure (Function.support (homogeneousExtension f)) ⊆ Prod.fst ⁻¹' tsupport f
  apply closure_minimal _ ((isClosed_tsupport f).preimage continuous_fst)
  intro z hz
  by_contra hn
  have hf : f z.1 = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hz (by simp only [homogeneousExtension, hf, mul_zero])

/-- The actual cone extension has compact base support, derived from compact full-test support. -/
theorem homogeneousTrace_hasCompactBaseSupport (π : Ω → B) (hπ : Continuous π)
    (L : Ω → P) (hL : Continuous L)
    (hcompact : ∀ K : Set P, IsCompact K → IsCompact (L ⁻¹' K))
    (b : P → ℝ) (hb : HasCompactSupport b) (s : Ω → ℝ) :
    ∃ K : Set B, IsCompact K ∧
      tsupport (homogeneousExtension (fun ω => b (L ω) / s ω)) ⊆ {z : Ω × ℝ | π z.1 ∈ K} := by
  let f := fun ω => b (L ω) / s ω
  have hc : HasCompactSupport f := quotientTrace_hasCompactSupport L hL hcompact b hb s
  refine ⟨π '' tsupport f, hc.image hπ, ?_⟩
  intro z hz
  exact ⟨z.1, homogeneousExtension_tsupport_subset f hz, rfl⟩

end Burnett.FullMomentumLift
