import Burnett.Analysis.FrozenTransport.FrozenDensityCubicVertex
import Burnett.Analysis.FrozenTransport.CyclicIntegralExtension
import Burnett.Analysis.FrozenTransport.CompactFarCorrectionProfile

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3900

noncomputable section

namespace Burnett.V10

open Set Burnett.V04 Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff ComplexConjugate Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι]

private theorem physicalFarProfilePoint_highOutput (p q : Vec) :
    farHighOutput (physicalFarProfilePoint p q) = ‖q‖⁻¹ • (p + q) := by
  simp only [farHighOutput, physicalFarProfilePoint, unitRep, smul_add, add_comm]

theorem frozenDensityCubicVertex_eq_farProfile (S : ι → Mat) (G : Mat)
    {p q r : Vec} (hq : q ≠ 0) (hSum : p + q + r = 0) (H J L : ι → ℂ) :
    let x := physicalFarProfilePoint p q
    frozenDensityCubicVertex S G p H q J r L =
      ((‖q‖ ^ 2 : ℝ) : ℂ) *
        frozenDensityCubicVertex S G x.2.1 H x.2.2 J (-farHighOutput x) L := by
  intro x
  have hq₀ : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have cancel (v : Vec) : ‖q‖ • (‖q‖⁻¹ • v) = v := by
    rw [smul_smul, mul_inv_cancel₀ hq₀, one_smul]
  have hp' : ‖q‖ • x.2.1 = p := cancel p
  have hq' : ‖q‖ • x.2.2 = q := cancel q
  have hr' : ‖q‖ • -farHighOutput x = r := by
    rw [smul_neg, show x = physicalFarProfilePoint p q from rfl,
      physicalFarProfilePoint_highOutput, cancel (p + q), triad_third_eq_neg_add hSum]
  simpa only [hp', hq', hr'] using
    frozenDensityCubicVertex_smul S G ‖q‖ x.2.1 H x.2.2 J (-farHighOutput x) L

/-- The cyclic physical cubic integrand coefficient. Radian Fourier measure is
handled by the integral, while the average over the three test placements is here. -/
def physicalCubicNumerator (S : ι → Mat) (G : Mat) (a : Vec → ℝ)
    (p : Vec) (H : ι → ℂ) (q : Vec) (J : ι → ℂ) (r : Vec) (L : ι → ℂ) : ℂ :=
  (-Complex.I / 3) * (cyclicWeight a p q r : ℂ) * frozenDensityCubicVertex S G p H q J r L

def normalizedPhysicalCubicNumerator (S : ι → Mat) (G : Mat) (a : Vec → ℝ)
    (H J L : FarProfilePoint → ι → ℂ) (x : FarProfilePoint) : ℂ :=
  (-Complex.I / 3) * (cyclicExtension a x.1 x.2.1 x.2.2 : ℂ) *
    frozenDensityCubicVertex S G x.2.1 (H x) x.2.2 (J x) (-farHighOutput x) (L x)

theorem physicalCubicNumerator_eq_normalized_on_lowSlot (S : ι → Mat) (G : Mat)
    (a : Vec → ℝ) (hodd : ∀ x : Vec, x ≠ 0 → a (-x) = -a x)
    (hscale : ∀ c : ℝ, 0 < c → ∀ x : Vec, x ≠ 0 → a (c • x) = c * a x)
    (ha : ContDiffOn ℝ 1 a ({0}ᶜ : Set Vec))
    {κ : ℝ} (hκ' : κ < 1 / 16) {p q r : Vec} (hSum : p + q + r = 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hlow : ‖p‖ ≤ 2 * κ * ‖q‖)
    (H J L : FarProfilePoint → ι → ℂ) :
    let x := physicalFarProfilePoint p q
    physicalCubicNumerator S G a p (H x) q (J x) r (L x) =
      ((‖p‖ * ‖q‖ ^ 2 : ℝ) : ℂ) * normalizedPhysicalCubicNumerator S G a H J L x := by
  intro x
  have hC := (cyclicWeight_div_norm_eq_extension_of_low a hodd hscale ha p q r hSum hp κ hκ' hlow).1
  have hc : cyclicWeight a p q r = cyclicExtension a x.1 x.2.1 x.2.2 * ‖p‖ :=
    (div_eq_iff (norm_ne_zero_iff.mpr hp)).mp hC
  have hv := frozenDensityCubicVertex_eq_farProfile S G hq hSum (H x) (J x) (L x)
  unfold physicalCubicNumerator normalizedPhysicalCubicNumerator
  rw [hc, hv]
  push_cast
  ring

private theorem cubicTerm_contDiffOn {U : Set FarProfilePoint} (S : ι → Mat) (G : Mat)
    (H J L : FarProfilePoint → ι → ℂ) (q r : FarProfilePoint → Vec)
    (hH : ∀ i, ContDiffOn ℝ ∞ (fun x => H x i) U)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (fun x => J x i) U)
    (hL : ∀ i, ContDiffOn ℝ ∞ (fun x => L x i) U)
    (hq : ∀ a, ContDiffOn ℝ ∞ (fun x => ((q x a : ℝ) : ℂ)) U)
    (hr : ∀ a, ContDiffOn ℝ ∞ (fun x => ((r x a : ℝ) : ℂ)) U) :
    ContDiffOn ℝ ∞ (fun x => frozenDensityCubicTerm S G (H x) (q x) (J x) (r x) (L x)) U := by
  unfold frozenDensityCubicTerm densityCoefficientDirection
  exact ContDiffOn.sum fun s _ => ContDiffOn.sum fun t _ =>
    ((ContDiffOn.sum fun k _ => contDiffOn_const.mul (hH k)).mul ((hq s.1).mul (hJ s.2))).mul
      ((hr t.1).mul (hL t.2))

open private coord_contDiff from Burnett.Analysis.AngularCaps.SmoothCapProfiles

theorem normalizedPhysicalCubicNumerator_contDiffOn (S : ι → Mat) (G : Mat)
    {a : Vec → ℝ} (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec))
    (H J L : FarProfilePoint → ι → ℂ)
    (hH : ∀ i, ContDiffOn ℝ ∞ (fun x => H x i) cyclicExtensionDomain)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (fun x => J x i) cyclicExtensionDomain)
    (hL : ∀ i, ContDiffOn ℝ ∞ (fun x => L x i) cyclicExtensionDomain) :
    ContDiffOn ℝ ∞ (normalizedPhysicalCubicNumerator S G a H J L) cyclicExtensionDomain := by
  have hz : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.1) := contDiff_fst.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun x : FarProfilePoint => x.2.2) := contDiff_snd.comp contDiff_snd
  have hρ : ContDiff ℝ ∞ (fun x : FarProfilePoint => -farHighOutput x) := (hθ.add hz).neg
  have coords (f : FarProfilePoint → Vec) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
      ContDiffOn ℝ ∞ (fun x => ((f x i : ℝ) : ℂ)) cyclicExtensionDomain :=
    (Complex.ofRealCLM.contDiff.comp ((coord_contDiff i).comp hf)).contDiffOn
  have h1 := cubicTerm_contDiffOn S G H J L _ _ hH hJ hL (coords _ hθ) (coords _ hρ)
  have h2 := cubicTerm_contDiffOn S G J L H _ _ hJ hL hH (coords _ hρ) (coords _ hz)
  have h3 := cubicTerm_contDiffOn S G L H J _ _ hL hH hJ (coords _ hz) (coords _ hθ)
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_cyclicExtension a ha))).mul ((h1.add h2).add h3).neg

theorem physicalCubicNumerator_highAdjoint (S : ι → Mat) (G : Mat)
    (a : Vec → ℝ) (hodd : ∀ x : Vec, x ≠ 0 → a (-x) = -a x)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (H J L : ι → ℂ) :
    conj (physicalCubicNumerator S G a (-p) (fun i => conj (H i))
        (-r) (fun i => conj (L i)) (-q) (fun i => conj (J i))) =
      physicalCubicNumerator S G a p H q J r L := by
  have hα : cyclicWeight a (-p) (-r) (-q) = -cyclicWeight a p q r := by
    unfold cyclicWeight
    rw [hodd p hp, hodd r hr, hodd q hq]
    ring
  have hΓ : frozenDensityCubicVertex S G (-p) (fun i => conj (H i))
      (-r) (fun i => conj (L i)) (-q) (fun i => conj (J i)) =
      conj (frozenDensityCubicVertex S G p H q J r L) := by
    rw [frozenDensityCubicVertex_conj, frozenDensityCubicVertex_highSwap S G p
      (fun i => conj (H i)) q (fun i => conj (J i)) r (fun i => conj (L i))]
    simpa only [neg_one_smul, neg_sq, one_pow, Complex.ofReal_one, one_mul] using
      frozenDensityCubicVertex_smul S G (-1 : ℝ) p (fun i => conj (H i))
        r (fun i => conj (L i)) q (fun i => conj (J i))
  simp only [physicalCubicNumerator, hα, hΓ, map_mul, map_div₀, map_neg, Complex.conj_I,
    neg_neg, map_ofNat, Complex.conj_ofReal, Complex.ofReal_neg, starRingEnd_self_apply]
  ring

end Burnett.V10
