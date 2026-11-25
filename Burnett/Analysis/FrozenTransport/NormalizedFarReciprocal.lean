import Burnett.Analysis.AngularCaps.FarAngularPhase
import Burnett.Analysis.AngularCaps.SmoothCapProfiles

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 5700000

noncomputable section

namespace Burnett.V10

open Set Filter Burnett.Analysis.ProjectiveNullCaps
open Burnett.RicciSymbol (Index)
open scoped ContDiff RealInnerProductSpace Topology

open private coord_contDiff from Burnett.Analysis.AngularCaps.SmoothCapProfiles

/-- The low direction, independent ratio vector, and high direction. -/
abbrev FarProfilePoint := Vec × Vec × Vec

/-- The denominator after removing the two physical frequency magnitudes. -/
def normalizedFarPhase (m : Form) (x : FarProfilePoint) : ℝ :=
  2 * pairing m x.1 x.2.2 + inner ℝ x.1 x.2.1 * quadratic m x.1

def physicalFarProfilePoint (p q : Vec) : FarProfilePoint :=
  (unitRep p, ‖q‖⁻¹ • p, unitRep q)

theorem normalizedFarPhase_contDiff (m : Form) : ContDiff ℝ ∞ (normalizedFarPhase m) := by
  have hω : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.1) := contDiff_fst
  have hz : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.1) := contDiff_fst.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.2) := contDiff_snd.comp contDiff_snd
  have hPair : ContDiff ℝ ∞ (fun x : FarProfilePoint => pairing m x.1 x.2.2) := by
    unfold pairing rowValue
    exact ContDiff.sum fun j _ =>
      (ContDiff.sum fun i _ => contDiff_const.mul ((coord_contDiff i).comp hω)).mul
        ((coord_contDiff j).comp hθ)
  exact (contDiff_const.mul hPair).add ((hω.inner ℝ hz).mul ((quadratic_contDiff m).comp hω))

/-- On physical variables the normalization uses the actual output-minus-input phase. -/
theorem normalizedFarPhase_eq_signedQuadraticPhase {m : Form} (hm : Symmetric m)
    {p q : Vec} (hp : p ≠ 0) (hq : q ≠ 0) :
    normalizedFarPhase m (physicalFarProfilePoint p q) =
      signedQuadraticPhase m p q / (‖p‖ * ‖q‖) := by
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hm' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp only [normalizedFarPhase, physicalFarProfilePoint, unitRep, pairing_smul_left,
    pairing_smul_right, quadratic_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, signedQuadraticPhase_eq hm]
  field_simp [hn, hm']

/-- The smooth reciprocal cut away from a fixed neighborhood of zero. -/
def guardedFarReciprocal (s t : ℝ) : ℝ :=
  (1 - descendingProfile (1 / 4) 1 (t ^ 2 / s ^ 2)) / t

private theorem guardedFarReciprocal_near_zero (s : ℝ) :
    guardedFarReciprocal s =ᶠ[𝓝 0] (fun _ => 0 : ℝ → ℝ) := by
  have hOpen : IsOpen {t : ℝ | t ^ 2 / s ^ 2 < 1 / 4} :=
    isOpen_lt ((continuous_id.pow 2).div_const _) continuous_const
  have hZero : (0 : ℝ) ∈ {t : ℝ | t ^ 2 / s ^ 2 < 1 / 4} := by norm_num
  filter_upwards [hOpen.mem_nhds hZero] with t ht
  change t ^ 2 / s ^ 2 < 1 / 4 at ht
  rw [guardedFarReciprocal, descendingProfile_eq_one (by norm_num : (1 : ℝ) / 4 < 1) ht.le, sub_self, zero_div]

theorem guardedFarReciprocal_contDiff (s : ℝ) :
    ContDiff ℝ ∞ (guardedFarReciprocal s) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases h : t = 0
  · subst t
    exact contDiffAt_const.congr_of_eventuallyEq (guardedFarReciprocal_near_zero s)
  · have hNum : ContDiff ℝ ∞ (fun x : ℝ => 1 - descendingProfile (1 / 4) 1 (x ^ 2 / s ^ 2)) :=
      contDiff_const.sub ((descendingProfile_contDiff _ _).comp ((contDiff_id.pow 2).div_const _))
    exact hNum.contDiffAt.div contDiffAt_id h

theorem guardedFarReciprocal_eq_inv {s t : ℝ} (hs : 0 < s) (ht : s ≤ |t|) :
    guardedFarReciprocal s t = t⁻¹ := by
  have hSq : s ^ 2 ≤ t ^ 2 := calc
    _ ≤ |t| ^ 2 := by gcongr
    _ = _ := sq_abs _
  have hFar : 1 ≤ t ^ 2 / s ^ 2 := (le_div_iff₀ (pow_pos hs 2)).mpr (by simpa using hSq)
  rw [guardedFarReciprocal, descendingProfile_eq_zero (by norm_num : (1 : ℝ) / 4 < 1) hFar,
    sub_zero, one_div]

/-- Read the quotient symbol as the high frequency magnitude times this profile.
The input N is the normalized full numerator on the same three variables. -/
def guardedFarCorrectionProfile (m : Form) (s : ℝ) (N : FarProfilePoint → ℂ)
    (x : FarProfilePoint) : ℂ :=
  -Complex.I * N x * (guardedFarReciprocal s (normalizedFarPhase m x) : ℝ)

theorem guardedFarCorrectionProfile_contDiffOn (m : Form) (s : ℝ)
    {N : FarProfilePoint → ℂ} {U : Set FarProfilePoint} (hN : ContDiffOn ℝ ∞ N U) :
    ContDiffOn ℝ ∞ (guardedFarCorrectionProfile m s N) U :=
  (contDiffOn_const.mul hN).mul
    (Complex.ofRealCLM.contDiff.comp
      ((guardedFarReciprocal_contDiff s).comp (normalizedFarPhase_contDiff m))).contDiffOn

private theorem guardedFarCorrectionProfile_exact {m : Form} (hm : Symmetric m)
    {s : ℝ} (hs : 0 < s) {p q : Vec} (hp : p ≠ 0) (hq : q ≠ 0)
    (hgap : s ≤ |normalizedFarPhase m (physicalFarProfilePoint p q)|) (N : FarProfilePoint → ℂ) :
    Complex.I * (signedQuadraticPhase m p q : ℂ) *
        ((‖q‖ : ℂ) * guardedFarCorrectionProfile m s N (physicalFarProfilePoint p q)) =
      ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) * N (physicalFarProfilePoint p q) := by
  let x := physicalFarProfilePoint p q
  let d := normalizedFarPhase m x
  have hd : d ≠ 0 := abs_pos.mp (hs.trans_le hgap)
  have hq₀ : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hp₀ : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hphase : signedQuadraticPhase m p q = d * (‖p‖ * ‖q‖) :=
    ((eq_div_iff (mul_ne_zero hp₀ hq₀)).mp (normalizedFarPhase_eq_signedQuadraticPhase hm hp hq)).symm
  have hReal : signedQuadraticPhase m p q * ‖q‖ * guardedFarReciprocal s d = ‖p‖ * ‖q‖ ^ 2 := by
    have hgap' : s ≤ |d| := hgap
    rw [guardedFarReciprocal_eq_inv hs hgap', hphase]
    calc
      _ = (d * d⁻¹) * (‖p‖ * ‖q‖ ^ 2) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hd, one_mul]
  calc
    _ = ((signedQuadraticPhase m p q * ‖q‖ * guardedFarReciprocal s d : ℝ) : ℂ) * N x := by
      simp only [guardedFarCorrectionProfile, x, d, Complex.ofReal_mul]
      calc
        _ = -(Complex.I * Complex.I) *
          (((signedQuadraticPhase m p q : ℂ) * (‖q‖ : ℂ) *
            (guardedFarReciprocal s (normalizedFarPhase m (physicalFarProfilePoint p q)) : ℂ)) *
            N (physicalFarProfilePoint p q)) := by ring
        _ = _ := by rw [Complex.I_mul_I, neg_neg, one_mul]
    _ = _ := by rw [hReal]

/-- Over the actual low/far support the guarded quotient recovers the exact
signed multiplier uniformly over the compact Lorentzian background family. -/
theorem exists_guardedFarCorrectionProfile_on_actual_support
    {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ m ∈ K, ∀ κ : ℝ, 0 < κ → κ < 1 / 16 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ ϑ : ℝ → ℝ, (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) →
      ∀ p q r : Vec, p ≠ 0 → q ≠ 0 → r ≠ 0 →
        InRelativeCone m (C * (c * κ * δ ^ 2)) p →
        InRelativeCone m (C * (c * κ * δ ^ 2)) q →
        InRelativeCone m (C * (c * κ * δ ^ 2)) r →
        InLowFarTriadSupport ϑ κ δ p q r →
        let x := physicalFarProfilePoint p q
        b * δ ^ 2 ≤ |normalizedFarPhase m x| ∧
        ∀ N : FarProfilePoint → ℂ,
          Complex.I * (signedQuadraticPhase m p q : ℂ) *
            ((‖q‖ : ℂ) * guardedFarCorrectionProfile m (b * δ ^ 2) N x) =
          ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) * N x := by
  obtain ⟨c₀, b, hc₀, hb, gap⟩ := exists_uniform_lowFar_signedQuadraticPhase_gap hK hFrame C hC
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro m hm κ hκ hκ' δ hδ hδ' c hc hc' ϑ hCut hFlat p q r hp hq hr hP hQ hR hSupport x
  have symm : Symmetric m := (hFrame m hm).elim lorentzFrame_symm
  have h := (gap m hm κ hκ hκ' δ hδ hδ' c hc hc' ϑ hCut hFlat
    p q r hp hq hr hP hQ hR hSupport).2
  have hn : 0 < ‖p‖ * ‖q‖ := mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq)
  have hNormalized : b * δ ^ 2 ≤ |normalizedFarPhase m x| := by
    rw [show x = physicalFarProfilePoint p q from rfl, normalizedFarPhase_eq_signedQuadraticPhase symm hp hq,
      abs_div, abs_of_pos hn]
    exact (le_div_iff₀ hn).mpr h
  exact ⟨hNormalized, guardedFarCorrectionProfile_exact symm (mul_pos hb (pow_pos hδ 2)) hp hq hNormalized⟩

end Burnett.V10
