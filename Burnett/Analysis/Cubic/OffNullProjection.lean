import Burnett.Analysis.Fourier.SharpProjection
import Burnett.Analysis.Cubic.OffNullCompactGradient
import Burnett.Analysis.Cubic.OffNullGradientBridge

noncomputable section

namespace Burnett.CubicOffNull

open MeasureTheory Filter CubicExplicit
open X02.SobolevTestJet
open scoped Topology ContDiff

def realToComplexL2 : ScalarL2 →L[ℝ] Fourier.ComplexL2 Space :=
  Complex.ofRealCLM.compLpL 2 volume

def multiplierRealInput (m : Fourier.BoundedSymbol Space) :
    ScalarL2 →L[ℝ] Fourier.ComplexL2 Space :=
  ((Fourier.fourierMultiplier m).restrictScalars ℝ).comp realToComplexL2

def localizedGradientSchwartz (χ : Cutoff) (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) (i : Index) : SchwartzMap Space ℂ := by
  have hD : ContDiff ℝ ∞ (CubicExplicit.D i h) :=
    (hh.contDiff_fderiv_apply (by simp)).comp
      (contDiff_id.prodMk (contDiff_const (c := basis i)))
  have hc : HasCompactSupport (fun x => (χ : Space → ℝ) x * CubicExplicit.D i h x) :=
    (test_compactSupport χ).mul_right
  exact (hc.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp ((test_smooth χ).mul hD))

@[simp] theorem localizedGradientSchwartz_apply (χ : Cutoff) (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) (i : Index) (x : Space) :
    localizedGradientSchwartz χ h hh i x =
      (((χ : Space → ℝ) x * CubicExplicit.D i h x : ℝ) : ℂ) := rfl

theorem realToComplex_localizedGradientLp (χ : Cutoff) (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) (i : Index) :
    realToComplexL2 (localizedGradientLp χ h hh i) =
      (localizedGradientSchwartz χ h hh i).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := (volume : Measure Space))
      (localizedGradientLp χ h hh i),
    (localizedGradient_memLp χ hh i).coeFn_toLp,
    (localizedGradientSchwartz χ h hh i).coeFn_toLp 2 volume] with x ha hb hc
  change (realToComplexL2 (localizedGradientLp χ h hh i) : Space → ℂ) x = _ at ha
  change (localizedGradientLp χ h hh i : Space → ℝ) x = _ at hb
  rw [ha, hb, hc]
  rfl

/-- The actual fixed bounded Fourier multiplier kills χ∂fₙ in physical
whole-space L² whenever its symbol is supported in the fixed Eδ. -/
theorem f_fixedMultiplier_localizedGradient_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (m : Fourier.BoundedSymbol Space) (hm : ∀ ξ, ξ ∉ offNullRegion δ → m ξ = 0)
    (χ : Cutoff) (i : Index) :
    Tendsto (fun n => multiplierRealInput m
      (localizedGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) := by
  have ht := Fourier.fourierMultiplier_schwartz_tendsto_zero m (offNullRegion_measurableSet δ) hm
    (fun n => localizedGradientSchwartz χ (fSequence n) (fSequence_smooth n) i)
    (compact_fGradient_offNull_energy_tendsto_zero hδ χ i)
  simpa only [multiplierRealInput, ContinuousLinearMap.comp_apply,
    realToComplex_localizedGradientLp] using ht

theorem w_fixedMultiplier_localizedGradient_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (m : Fourier.BoundedSymbol Space) (hm : ∀ ξ, ξ ∉ offNullRegion δ → m ξ = 0)
    (χ : Cutoff) (i : Index) :
    Tendsto (fun n => multiplierRealInput m
      (localizedGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) := by
  have ht := Fourier.fourierMultiplier_schwartz_tendsto_zero m (offNullRegion_measurableSet δ) hm
    (fun n => localizedGradientSchwartz χ (wSequence n) (wSequence_smooth n) i)
    (compact_wGradient_offNull_energy_tendsto_zero hδ χ i)
  simpa only [multiplierRealInput, ContinuousLinearMap.comp_apply,
    realToComplex_localizedGradientLp] using ht

theorem f_fixedMultiplier_productGradient_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (m : Fourier.BoundedSymbol Space) (hm : ∀ ξ, ξ ∉ offNullRegion δ → m ξ = 0)
    (χ : Cutoff) (i : Index) :
    Tendsto (fun n => multiplierRealInput m
      (productGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) := by
  have he := f_productGradient_map_difference_tendsto_zero (multiplierRealInput m) χ i
  have hl := f_fixedMultiplier_localizedGradient_tendsto_zero hδ m hm χ i
  have ht := he.add hl
  simpa only [sub_add_cancel, add_zero] using ht

theorem w_fixedMultiplier_productGradient_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (m : Fourier.BoundedSymbol Space) (hm : ∀ ξ, ξ ∉ offNullRegion δ → m ξ = 0)
    (χ : Cutoff) (i : Index) :
    Tendsto (fun n => multiplierRealInput m
      (productGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) := by
  have he := w_productGradient_map_difference_tendsto_zero (multiplierRealInput m) χ i
  have hl := w_fixedMultiplier_localizedGradient_tendsto_zero hδ m hm χ i
  have ht := he.add hl
  simpa only [sub_add_cancel, add_zero] using ht

def offNullSharpSymbol (δ : ℝ) : Fourier.BoundedSymbol Space :=
  Fourier.sharpSymbol (offNullRegion δ) (offNullRegion_measurableSet δ)

theorem offNullSharpSymbol_zero {δ : ℝ} {ξ : Space} (hξ : ξ ∉ offNullRegion δ) :
    offNullSharpSymbol δ ξ = 0 := Fourier.sharpSymbol_apply_notMem _ hξ

/-- The fixed sharp conic orthogonal Fourier projection is a concrete
instance of the proved bounded-symbol conclusion, for the same f and w. -/
theorem fixed_offNull_sharp_localization {δ : ℝ} (hδ : 0 < δ) (χ : Cutoff) (i : Index) :
    Tendsto (fun n => multiplierRealInput (offNullSharpSymbol δ)
      (localizedGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) ∧
    Tendsto (fun n => multiplierRealInput (offNullSharpSymbol δ)
      (localizedGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) ∧
    Tendsto (fun n => multiplierRealInput (offNullSharpSymbol δ)
      (productGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) ∧
    Tendsto (fun n => multiplierRealInput (offNullSharpSymbol δ)
      (productGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) :=
  ⟨f_fixedMultiplier_localizedGradient_tendsto_zero hδ _ (fun _ hx => offNullSharpSymbol_zero hx) χ i,
    w_fixedMultiplier_localizedGradient_tendsto_zero hδ _ (fun _ hx => offNullSharpSymbol_zero hx) χ i,
    f_fixedMultiplier_productGradient_tendsto_zero hδ _ (fun _ hx => offNullSharpSymbol_zero hx) χ i,
    w_fixedMultiplier_productGradient_tendsto_zero hδ _ (fun _ hx => offNullSharpSymbol_zero hx) χ i⟩

theorem multipliers_eq_of_eq_away_zero (m n : Fourier.BoundedSymbol Space)
    (h : ∀ ξ, ξ ≠ 0 → m ξ = n ξ) : Fourier.fourierMultiplier m = Fourier.fourierMultiplier n := by
  apply Fourier.fourierMultiplier_congr_ae m n
  have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by simp [ae_iff]
  exact hne.mono h

/-- Smooth angular symbols may have an arbitrary assigned value at zero;
smoothness is only required away from the zero frequency. -/
def smoothAngularSymbol (a : Space → ℂ) (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Space))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖a ξ‖ ≤ B) : Fourier.BoundedSymbol Space where
  toFun := a
  measurable := by
    have hne : ∀ᵐ ξ : Space ∂volume, ξ ∈ ({0}ᶜ : Set Space) := by simp [ae_iff]
    have hr := Measure.restrict_eq_self_of_ae_mem hne
    have hm := ha.continuousOn.aestronglyMeasurable (measurableSet_singleton (0 : Space)).compl
      (μ := (volume : Measure Space))
    rwa [hr] at hm
  bound := B
  bound_nonneg := hB
  norm_le := hb

theorem fixed_offNull_smooth_localization {δ : ℝ} (hδ : 0 < δ)
    (a : Space → ℂ) (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Space))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ ξ, ‖a ξ‖ ≤ B)
    (hs : ∀ ξ, ξ ∉ offNullRegion δ → a ξ = 0) (χ : Cutoff) (i : Index) :
    Tendsto (fun n => multiplierRealInput (smoothAngularSymbol a ha B hB hb)
      (localizedGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) ∧
    Tendsto (fun n => multiplierRealInput (smoothAngularSymbol a ha B hB hb)
      (localizedGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) ∧
    Tendsto (fun n => multiplierRealInput (smoothAngularSymbol a ha B hB hb)
      (productGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) ∧
    Tendsto (fun n => multiplierRealInput (smoothAngularSymbol a ha B hB hb)
      (productGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) :=
  ⟨f_fixedMultiplier_localizedGradient_tendsto_zero hδ _ hs χ i,
    w_fixedMultiplier_localizedGradient_tendsto_zero hδ _ hs χ i,
    f_fixedMultiplier_productGradient_tendsto_zero hδ _ hs χ i,
    w_fixedMultiplier_productGradient_tendsto_zero hδ _ hs χ i⟩

abbrev GradientL2 := PiLp 2 (fun _ : Index => Fourier.ComplexL2 Space)

def localizedGradientProjection (m : Fourier.BoundedSymbol Space) (χ : Cutoff)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) : GradientL2 :=
  WithLp.toLp 2 (fun i => multiplierRealInput m (localizedGradientLp χ h hh i))

def productGradientProjection (m : Fourier.BoundedSymbol Space) (χ : Cutoff)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) : GradientL2 :=
  WithLp.toLp 2 (fun i => multiplierRealInput m (productGradientLp χ h hh i))

theorem localizedGradientProjection_norm_sq (m : Fourier.BoundedSymbol Space) (χ : Cutoff)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) :
    ‖localizedGradientProjection m χ h hh‖^2 =
      ∑ i : Index, ‖multiplierRealInput m (localizedGradientLp χ h hh i)‖^2 :=
  PiLp.norm_sq_eq_of_L2 _ _

theorem productGradientProjection_norm_sq (m : Fourier.BoundedSymbol Space) (χ : Cutoff)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) :
    ‖productGradientProjection m χ h hh‖^2 =
      ∑ i : Index, ‖multiplierRealInput m (productGradientLp χ h hh i)‖^2 :=
  PiLp.norm_sq_eq_of_L2 _ _

theorem gradientL2_tendsto_zero {u : ℕ → Index → Fourier.ComplexL2 Space}
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0)) :
    Tendsto (fun n => WithLp.toLp 2 (u n)) atTop (𝓝 (0 : GradientL2)) := by
  have hp : Tendsto u atTop (𝓝 (fun _ : Index => (0 : Fourier.ComplexL2 Space))) :=
    tendsto_pi_nhds.mpr hu
  exact ((PiLp.continuous_toLp 2 (fun _ : Index => Fourier.ComplexL2 Space)).tendsto _).comp hp

/-- The complete fixed-Fourier off-null localization assertion of paper
line 3193, in the positive Euclidean L² norm of all four components, for
the original two sequences and both positions of the compact cutoff. -/
theorem fixed_offNull_gradient_localization {δ : ℝ} (hδ : 0 < δ)
    (m : Fourier.BoundedSymbol Space) (hm : ∀ ξ, ξ ∉ offNullRegion δ → m ξ = 0)
    (χ : Cutoff) :
    Tendsto (fun n => localizedGradientProjection m χ (fSequence n) (fSequence_smooth n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => localizedGradientProjection m χ (wSequence n) (wSequence_smooth n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => productGradientProjection m χ (fSequence n) (fSequence_smooth n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => productGradientProjection m χ (wSequence n) (wSequence_smooth n))
      atTop (𝓝 0) :=
  ⟨gradientL2_tendsto_zero (fun i => f_fixedMultiplier_localizedGradient_tendsto_zero hδ m hm χ i),
    gradientL2_tendsto_zero (fun i => w_fixedMultiplier_localizedGradient_tendsto_zero hδ m hm χ i),
    gradientL2_tendsto_zero (fun i => f_fixedMultiplier_productGradient_tendsto_zero hδ m hm χ i),
    gradientL2_tendsto_zero (fun i => w_fixedMultiplier_productGradient_tendsto_zero hδ m hm χ i)⟩

def symbolZeroAtOrigin (m : Fourier.BoundedSymbol Space) : Fourier.BoundedSymbol Space where
  toFun ξ := if ξ = 0 then 0 else m ξ
  measurable := by
    have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by simp [ae_iff]
    exact m.measurable.congr (hne.mono (fun ξ hx => by simp [hx]))
  bound := m.bound
  bound_nonneg := m.bound_nonneg
  norm_le ξ := by
    by_cases hx : ξ = 0
    · simpa [hx] using m.bound_nonneg
    · simpa only [if_neg hx] using m.norm_le ξ

/-- Zero-frequency conventions are immaterial: only nonzero frequencies
outside Eδ are required to have zero symbol. This is the consumer-facing
form of the full fixed-Fourier localization statement. -/
theorem fixed_offNull_gradient_localization_away_zero {δ : ℝ} (hδ : 0 < δ)
    (m : Fourier.BoundedSymbol Space)
    (hm : ∀ ξ, ξ ≠ 0 → ξ ∉ offNullRegion δ → m ξ = 0) (χ : Cutoff) :
    Tendsto (fun n => localizedGradientProjection m χ (fSequence n) (fSequence_smooth n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => localizedGradientProjection m χ (wSequence n) (wSequence_smooth n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => productGradientProjection m χ (fSequence n) (fSequence_smooth n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => productGradientProjection m χ (wSequence n) (wSequence_smooth n))
      atTop (𝓝 0) := by
  have heq : Fourier.fourierMultiplier m = Fourier.fourierMultiplier (symbolZeroAtOrigin m) :=
    multipliers_eq_of_eq_away_zero m _ (fun ξ hx => by simp [symbolZeroAtOrigin, hx])
  have hs : ∀ ξ, ξ ∉ offNullRegion δ → symbolZeroAtOrigin m ξ = 0 := by
    intro ξ hx
    by_cases hz : ξ = 0
    · simp [symbolZeroAtOrigin, hz]
    · simpa [symbolZeroAtOrigin, hz] using hm ξ hz hx
  have ht := fixed_offNull_gradient_localization hδ (symbolZeroAtOrigin m) hs χ
  simpa only [localizedGradientProjection, productGradientProjection, multiplierRealInput, ← heq] using ht

end Burnett.CubicOffNull
