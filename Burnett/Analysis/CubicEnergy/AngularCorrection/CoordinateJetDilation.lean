import Burnett.Analysis.CubicEnergy.AngularCorrection.CoordinateQuotientCMCore

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A07

open MeasureTheory Filter Set Metric
open Burnett.A02.FrequencySplit (E Joint Freq8 splitFreq splitFreq_inner)
open Burnett.A06
open scoped ContDiff Topology RealInnerProductSpace ComplexConjugate

/-- Fixed joint dilation sending both high frequencies of the supported
unit-sphere symbols above the same infrared cutoff. -/
def coordinateJetDilation (ρ R : ℝ) : ℝ :=
  2 * (1 + 2*ρ) * R / (1-ρ)

theorem coordinateJetDilation_pos {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hsmall : ρ < 1) (hR : 0 < R) : 0 < coordinateJetDilation ρ R := by
  unfold coordinateJetDilation
  exact div_pos (by positivity) (sub_pos.mpr hsmall)

/-- Fixed linear map to the physical joint frequencies. -/
def scaledJointFrequency (s : ℝ) : Freq8 →L[ℝ] Joint :=
  s • splitFreq.toContinuousLinearMap

/-- The linear map underlying the already verified high-slot frequency change. -/
def highAdjointFrequencyCLM : Joint →L[ℝ] Joint :=
  (-(ContinuousLinearMap.fst ℝ E E)).prod
    (ContinuousLinearMap.snd ℝ E E + ContinuousLinearMap.fst ℝ E E)

/-- The same dilation, after exchanging the high input and output. -/
def scaledHighAdjointFrequency (s : ℝ) : Freq8 →L[ℝ] Joint :=
  s • (highAdjointFrequencyCLM.comp splitFreq.toContinuousLinearMap)

/-- This fixed multiplier is smooth even at the new high axis because it
reuses the original infrared cutoff near that axis. -/
def scaledCoordinateFactor (η : ℝ → ℝ) (s : ℝ) (j : Fin 4) (u : Freq8) : ℝ :=
  η (s * ‖(splitFreq u).2‖) * ((splitFreq u).2 j / ‖(splitFreq u).2‖ ^ 2) * s⁻¹

theorem scaledCoordinateFactor_contDiff
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (s : ℝ) (j : Fin 4)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ x ≤ r, η x = 0) :
    ContDiff ℝ ∞ (scaledCoordinateFactor η s j) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hi : ContDiff ℝ ∞ (fun v : Freq8 => (splitFreq v).2) :=
    contDiff_snd.comp splitFreq.contDiff
  by_cases hz : (splitFreq u).2 = 0
  · have hsmall : s * ‖(splitFreq u).2‖ < r := by simpa [hz] using hr
    have near := (isOpen_lt (continuous_const.mul hi.continuous.norm)
      continuous_const).mem_nhds hsmall
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [near] with v hv
    simp [scaledCoordinateFactor, hzero _ hv.le]
  · have hnum : ContDiffAt ℝ ∞ (fun v : Freq8 => (splitFreq v).2 j) u :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hi).contDiffAt
    have hden : ContDiffAt ℝ ∞ (fun v : Freq8 => ‖(splitFreq v).2‖ ^ 2) u :=
      ((contDiff_norm_sq ℝ).comp hi).contDiffAt
    have hd := hnum.div hden (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
    have hcut : ContDiffAt ℝ ∞ (fun v : Freq8 => η (s * ‖(splitFreq v).2‖)) u :=
      hη.contDiffAt.comp u ((contDiffAt_const (c := s)).mul (hi.contDiffAt.norm ℝ hz))
    exact (hcut.mul hd).mul contDiffAt_const

private theorem norm_le_sum_of_split (u : Freq8) :
    ‖u‖ ≤ ‖(splitFreq u).1‖ + ‖(splitFreq u).2‖ := by
  have e := splitFreq_inner u u
  simp only [real_inner_self_eq_norm_sq] at e
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp <|
    by nlinarith [mul_nonneg (norm_nonneg (splitFreq u).1) (norm_nonneg (splitFreq u).2)]

private theorem lowCartesianSymbol_support_lt
    (χ : ℝ → ℝ) (c : Joint → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcut : ∀ r ≥ ρ ^ 2, χ r = 0) (x : Joint)
    (h : lowCartesianSymbol χ c x ≠ 0) :
    ‖x.1‖ < ρ * ‖x.2‖ := by
  by_contra! hx
  exact h (lowCartesianSymbol_eq_zero_outside χ c hρ hcut hx)

private theorem jetDilation_enough {ρ R h k : ℝ}
    (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 0 < R) (hh : 0 ≤ h)
    (hout : (1/2 : ℝ) ≤ (1+2*ρ)*h) (hin : (1-ρ)*h ≤ k) :
    R ≤ coordinateJetDilation ρ R * h ∧ R ≤ coordinateJetDilation ρ R * k := by
  let s := coordinateJetDilation ρ R
  have hs : 0 < s := coordinateJetDilation_pos hρ hsmall hR
  have hm : R ≤ s * ((1-ρ)*h) := by
    have he : s * ((1-ρ)*h) = 2*R*((1+2*ρ)*h) := by
      dsimp only [s, coordinateJetDilation]
      field_simp [(sub_pos.mpr hsmall).ne']
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hout (show 0 ≤ 2*R by positivity)]
  have hh0 : (1-ρ)*h ≤ h := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith : 1-ρ ≤ 1) hh
  exact ⟨hm.trans (mul_le_mul_of_nonneg_left hh0 hs.le),
    hm.trans (mul_le_mul_of_nonneg_left hin hs.le)⟩

private theorem regularizedLowCartesianSymbol_smul_exact
    (η χ : ℝ → ℝ) (c : Joint → ℂ) (s : ℝ) (hs : 0 < s) (x : Joint) :
    regularizedLowCartesianSymbol η χ c (s • x) =
      η (s * ‖x.2‖) • (s • lowCartesianSymbol χ c x) := by
  rw [regularizedLowCartesianSymbol, lowCartesianSymbol_smul χ c s hs, Prod.smul_snd,
    norm_smul, Real.norm_of_nonneg hs.le]

/-- On a fixed open neighborhood of the joint unit sphere, both homogeneous
cores equal products of one fixed smooth coordinate factor and the original
regularized symbol evaluated along fixed linear maps. -/
theorem coordinateQuotients_eq_scaledRegularized
    (η χ : ℝ → ℝ) (c : Joint → ℂ) {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 0 < R) (hone : ∀ s ≥ R, η s = 1)
    (hcut : ∀ x ≥ ρ ^ 2, χ x = 0)
    (j : Fin 4) (u : Freq8) (hu : (1/2 : ℝ) < ‖u‖) :
    coordinateQuotient (lowCartesianSymbol χ c) j (splitFreq u) =
      scaledCoordinateFactor η (coordinateJetDilation ρ R) j u •
        regularizedLowCartesianSymbol η χ c (scaledJointFrequency (coordinateJetDilation ρ R) u) ∧
    coordinateQuotient (highAdjointSymbol (lowCartesianSymbol χ c)) j (splitFreq u) =
      scaledCoordinateFactor η (coordinateJetDilation ρ R) j u •
        conj (regularizedLowCartesianSymbol η χ c (scaledHighAdjointFrequency (coordinateJetDilation ρ R) u)) := by
  let x := splitFreq u
  let s := coordinateJetDilation ρ R
  have hs : 0 < s := coordinateJetDilation_pos hρ hsmall hR
  have normSum : ‖u‖ ≤ ‖x.1‖ + ‖x.2‖ := norm_le_sum_of_split u
  have sf : scaledJointFrequency s u = s • x := rfl
  have sa : scaledHighAdjointFrequency s u = s • highAdjointFrequencies x := rfl
  constructor
  · by_cases hz : lowCartesianSymbol χ c x = 0
    · rw [sf, regularizedLowCartesianSymbol_smul_exact η χ c s hs x, hz]
      rw [coordinateQuotient, show lowCartesianSymbol χ c (splitFreq u) = 0 from hz]
      simp
    · have hlow := lowCartesianSymbol_support_lt χ c hρ hcut x hz
      have hrad : (1/2 : ℝ) ≤ (1+2*ρ)*‖x.2‖ := by
        linarith [mul_nonneg hρ (norm_nonneg x.2)]
      have hbase : (1-ρ)*‖x.2‖ ≤ ‖x.2‖ := by nlinarith [mul_nonneg hρ (norm_nonneg x.2)]
      have hhigh : R ≤ s * ‖x.2‖ := (jetDilation_enough hρ hsmall hR (norm_nonneg _) hrad hbase).1
      rw [sf, regularizedLowCartesianSymbol_smul_exact η χ c s hs x, hone _ hhigh,
        one_smul, coordinateQuotient]
      change _ = (η (s*‖x.2‖) * (x.2 j / ‖x.2‖^2) * s⁻¹) • (s • lowCartesianSymbol χ c x)
      rw [hone _ hhigh, one_mul, smul_smul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
      rfl
  · let y := highAdjointFrequencies x
    by_cases hz : lowCartesianSymbol χ c y = 0
    · rw [sa, regularizedLowCartesianSymbol_smul_exact η χ c s hs y, hz]
      rw [coordinateQuotient, highAdjointSymbol,
        show lowCartesianSymbol χ c (highAdjointFrequencies (splitFreq u)) = 0 from hz]
      simp
    · have hlow0 := lowCartesianSymbol_support_lt χ c hρ hcut y hz
      have hlow : ‖x.1‖ < ρ * ‖x.2+x.1‖ := by simpa [y, highAdjointFrequencies] using hlow0
      have hupper : ‖x.2+x.1‖ ≤ ‖x.2‖+‖x.1‖ := norm_add_le _ _
      have hlower : ‖x.2‖ ≤ ‖x.2+x.1‖+‖x.1‖ := by
        simpa using norm_add_le (x.2+x.1) (-x.1)
      have hrad : (1/2 : ℝ) ≤ (1+2*ρ)*‖x.2+x.1‖ := by linarith
      have hbase : (1-ρ)*‖x.2+x.1‖ ≤ ‖x.2‖ := by linarith
      have hlarge := jetDilation_enough hρ hsmall hR (norm_nonneg _) hrad hbase
      have hout : R ≤ s * ‖y.2‖ := hlarge.1
      have hin : R ≤ s * ‖x.2‖ := hlarge.2
      rw [sa, regularizedLowCartesianSymbol_smul_exact η χ c s hs y, hone _ hout,
        one_smul, coordinateQuotient, highAdjointSymbol]
      change _ = (η (s*‖x.2‖) * (x.2 j / ‖x.2‖^2) * s⁻¹) • conj (s • lowCartesianSymbol χ c y)
      rw [hone _ hin, one_mul]
      have conj_s : conj (s • lowCartesianSymbol χ c y) = s • conj (lowCartesianSymbol χ c y) := by
        simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
      rw [conj_s, smul_smul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
      rfl

end Burnett.A07
