import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicCoefficientDecay

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A06

open Metric MeasureTheory
open scoped BigOperators ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- One uniform bound for all ordered derivatives of order at most n along the
six fixed rotation fields, evaluated on the unit sphere. -/
def roundRotationJetBound : ℕ → (RotationSpace → ℝ) → ℝ → Prop
  | 0, f, C => ∀ x : RoundSphere3, ‖f x‖ ≤ C
  | n + 1, f, C =>
    (∀ x : RoundSphere3, ‖f x‖ ≤ C) ∧
      ∀ p ∈ rotationPairs, roundRotationJetBound n (planeRotationDerivative p.1 p.2 f) C

private theorem roundRotationJetBound_value {n : ℕ} {f : RotationSpace → ℝ} {C : ℝ}
    (h : roundRotationJetBound n f C) (x : RoundSphere3) : ‖f x‖ ≤ C := by
  cases n with
  | zero => exact h x
  | succ n => exact h.1 x

private theorem roundRotationJetBound_pred (n : ℕ) {f : RotationSpace → ℝ} {C : ℝ}
    (h : roundRotationJetBound (n + 1) f C) : roundRotationJetBound n f C := by
  induction n generalizing f with
  | zero => exact h.1
  | succ n ih => exact ⟨h.1, fun p hp => ih (h.2 p hp)⟩

private theorem contDiff_planeRotationDerivative_succ {n : ℕ} {f : RotationSpace → ℝ}
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (p : Fin 4 × Fin 4) :
    ContDiff ℝ n (planeRotationDerivative p.1 p.2 f) :=
  contDiff_planeRotationDerivative (by simpa only [Nat.cast_add, Nat.cast_one] using hf) p.1 p.2

private theorem differentiable_of_contDiff_succ {n : ℕ} {f : RotationSpace → ℝ}
    (hf : ContDiff ℝ (n + 1 : ℕ) f) : Differentiable ℝ f :=
  hf.differentiable (by exact_mod_cast (show 1 ≤ n + 1 by omega))

private theorem roundRotationJetBound_sum {ι : Type*} (s : Finset ι) (n : ℕ)
    {F : ι → RotationSpace → ℝ} {C : ι → ℝ}
    (hF : ∀ i ∈ s, ContDiff ℝ n (F i))
    (hC : ∀ i ∈ s, roundRotationJetBound n (F i) (C i)) :
    roundRotationJetBound n (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, C i) := by
  have value (x : RoundSphere3) : ‖∑ i ∈ s, F i x‖ ≤ ∑ i ∈ s, C i :=
    (norm_sum_le s fun i => F i x).trans (Finset.sum_le_sum fun i hi =>
      roundRotationJetBound_value (hC i hi) x)
  induction n generalizing F with
  | zero => exact value
  | succ n ih =>
    refine ⟨value, fun p hp => ?_⟩
    have hlin : planeRotationDerivative p.1 p.2 (fun x => ∑ i ∈ s, F i x) =
        fun x => ∑ i ∈ s, planeRotationDerivative p.1 p.2 (F i) x := by
      funext x
      simp only [planeRotationDerivative, fderiv_fun_sum (fun i hi =>
        differentiable_of_contDiff_succ (hF i hi) x), ContinuousLinearMap.sum_apply]
    rw [hlin]
    exact ih (fun i hi => contDiff_planeRotationDerivative_succ (hF i hi) p)
      (fun i hi => (hC i hi).2 p hp) (fun x =>
        (norm_sum_le s fun i => planeRotationDerivative p.1 p.2 (F i) x).trans
          (Finset.sum_le_sum fun i hi => roundRotationJetBound_value ((hC i hi).2 p hp) x))

private theorem roundRotationJetBound_sub {n : ℕ} {f g : RotationSpace → ℝ} {A B : ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hA : roundRotationJetBound n f A) (hB : roundRotationJetBound n g B) :
    roundRotationJetBound n (f - g) (A + B) := by
  have value (x : RoundSphere3) : ‖(f - g) x‖ ≤ A + B :=
    (norm_sub_le (f x) (g x)).trans
      (add_le_add (roundRotationJetBound_value hA x) (roundRotationJetBound_value hB x))
  induction n generalizing f g with
  | zero => exact value
  | succ n ih =>
    refine ⟨value, fun p hp => ?_⟩
    have hlin : planeRotationDerivative p.1 p.2 (f - g) =
        planeRotationDerivative p.1 p.2 f - planeRotationDerivative p.1 p.2 g := by
      funext x
      simp only [planeRotationDerivative, fderiv_sub (differentiable_of_contDiff_succ hf x)
        (differentiable_of_contDiff_succ hg x), ContinuousLinearMap.sub_apply, Pi.sub_apply]
    rw [hlin]
    exact ih (contDiff_planeRotationDerivative_succ hf p)
      (contDiff_planeRotationDerivative_succ hg p) (hA.2 p hp) (hB.2 p hp) (fun x =>
        (norm_sub_le (planeRotationDerivative p.1 p.2 f x) (planeRotationDerivative p.1 p.2 g x)).trans
          (add_le_add (roundRotationJetBound_value (hA.2 p hp) x) (roundRotationJetBound_value (hB.2 p hp) x)))

private theorem rotationPairs_card : rotationPairs.card = 6 := by decide

/-- One I−Δ step uses two rotation derivatives and costs a fixed factor seven. -/
theorem roundShiftCasimir_rotationJetBound (n : ℕ) {f : RotationSpace → ℝ} {C : ℝ}
    (hf : ContDiff ℝ (n + 2 : ℕ) f) (h : roundRotationJetBound (n + 2) f C) :
    roundRotationJetBound n (roundShiftCasimir f) (7 * C) := by
  let D (p : Fin 4 × Fin 4) := planeRotationDerivative p.1 p.2 (planeRotationDerivative p.1 p.2 f)
  have hn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast (show n ≤ n + 2 by omega))
  have hD (p : Fin 4 × Fin 4) : ContDiff ℝ n (D p) :=
    contDiff_planeRotationDerivative_succ (contDiff_planeRotationDerivative_succ hf p) p
  have hDQ (p : Fin 4 × Fin 4) (hp : p ∈ rotationPairs) : roundRotationJetBound n (D p) C :=
    (h.2 p hp).2 p hp
  have hsum : roundRotationJetBound n (planeRotationCasimir f) (6 * C) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, rotationPairs_card, Nat.cast_ofNat]
      using (roundRotationJetBound_sum rotationPairs n (F := D) (C := fun _ => C)
        (fun p _ => hD p) hDQ)
  have hC : roundRotationJetBound n f C :=
    roundRotationJetBound_pred n (roundRotationJetBound_pred (n + 1) h)
  have hsumDiff : ContDiff ℝ n (planeRotationCasimir f) :=
    ContDiff.sum (fun p _ => hD p)
  change roundRotationJetBound n (f - planeRotationCasimir f) (7 * C)
  have hc : C + 6 * C = 7 * C := by ring
  rw [← hc]
  exact roundRotationJetBound_sub hn hsumDiff hC hsum

theorem roundShiftCasimirPower_rotationJetBound (n k : ℕ) {f : RotationSpace → ℝ} {C : ℝ}
    (hf : ContDiff ℝ (k + 2 * n : ℕ) f) (h : roundRotationJetBound (k + 2 * n) f C) :
    roundRotationJetBound k (roundShiftCasimirPower n f) ((7 : ℝ)^n * C) := by
  induction n generalizing k with
  | zero => simpa only [pow_zero, one_mul, Nat.mul_zero, Nat.add_zero, roundShiftCasimirPower] using h
  | succ n ih =>
    have eq : k + 2 + 2 * n = k + 2 * (n + 1) := by omega
    have hd : ContDiff ℝ (k + 2 + 2 * n : ℕ) f := by rwa [eq]
    have hh : roundRotationJetBound (k + 2 + 2 * n) f C := by rwa [eq]
    have hz := roundShiftCasimir_rotationJetBound k (roundShiftCasimirPower_contDiff n (k + 2) hd)
      (ih (k + 2) hd hh)
    simpa only [roundShiftCasimirPower, pow_succ', mul_assoc] using hz

/-- For fixed real angular data, a uniform bound on derivatives through
order twelve in the six rotation directions gives (d+1)⁻¹² decay. -/
theorem exists_roundSphereHarmonicCoefficient_rotationJetBound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {f : RotationSpace → ℝ}, ContDiff ℝ 12 f → ∀ C : ℝ,
      0 ≤ C → roundRotationJetBound 12 f C → ∀ i : SphereHarmonicIndex,
      ‖∫ x : RoundSphere3, f x * sphereHarmonicFamily i x ∂roundSphere3Measure‖ ≤
        K * (((i.1 : ℝ) + 1)^12)⁻¹ * C := by
  let L : C(RoundSphere3, ℝ) →L[ℝ] RoundSphereL2 := ContinuousMap.toLp 2 roundSphere3Measure ℝ
  refine ⟨‖L‖ * (7 : ℝ)^6, by positivity, ?_⟩
  intro f hf C hC hj i
  have hpoint := roundShiftCasimirPower_rotationJetBound 6 0 hf hj
  have hbound : ‖roundShiftCasimirSixOnSphere hf‖ ≤ (7 : ℝ)^6 * C :=
    (ContinuousMap.norm_le (roundShiftCasimirSixOnSphere hf) (by positivity)).2 hpoint
  have hL : ‖L (roundShiftCasimirSixOnSphere hf)‖ ≤ ‖L‖ * ((7 : ℝ)^6 * C) :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg L))
  calc
    _ ≤ (((i.1 : ℝ) + 1)^12)⁻¹ * ‖L (roundShiftCasimirSixOnSphere hf)‖ :=
      norm_roundSphereHarmonicCoefficient_le hf i
    _ ≤ (((i.1 : ℝ) + 1)^12)⁻¹ * (‖L‖ * ((7 : ℝ)^6 * C)) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

end Burnett.A06
