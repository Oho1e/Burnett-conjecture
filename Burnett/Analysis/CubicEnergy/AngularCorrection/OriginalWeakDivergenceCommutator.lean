import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalHighAdjointFirstOrder
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularRoughCommutator

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A08

open Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate ContDiff ENNReal NNReal

open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private inner_realSchwartzCoefficient from Burnett.Analysis.CubicEnergy.AngularCorrection.SchwartzHighSlotCommutator

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Field := SchwartzMap E ℂ
private abbrev Index := Fin 4

/-- The paper's differential expression `-∂ₐ(dᵃᵇ∂ᵦ)` on the Schwartz core. -/
def schwartzDivergence (d : Index → Index → SchwartzMap E ℝ) (v : Field) : Field :=
  -(∑ a : Index, ∑ b : Index, coordinateDerivative a (realSchwartzMultiply (d a b) (coordinateDerivative b v)))

private def derivativeArray (u : Field) (x : E) : PiLp 2 (fun _ : Index => ℂ) :=
  WithLp.toLp 2 (fun a => coordinateDerivative a u x)

private theorem memLp_derivativeArray (p : ℝ≥0∞) (u : Field) :
    MemLp (derivativeArray u) p volume := by
  classical
  let A (a : Index) (x : E) : PiLp 2 (fun _ : Index => ℂ) :=
    WithLp.toLp 2 (Pi.single a (coordinateDerivative a u x))
  have hsum : derivativeArray u = ∑ a, A a := by
    funext x
    ext b
    rw [Finset.sum_apply]
    change _ = PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℂ) b (∑ a, A a x)
    rw [map_sum]
    simp [A, derivativeArray]
  rw [hsum]
  refine memLp_finset_sum' _ fun a _ => ?_
  have hsingle : Isometry
      (fun y : ℂ => (WithLp.toLp 2 (Pi.single a y) : PiLp 2 (fun _ : Index => ℂ))) :=
    fun y z => PiLp.edist_toLp_single_same 2 (fun _ : Index => ℂ) a y z
  exact hsingle.lipschitz.comp_memLp (by simp) ((coordinateDerivative a u).memLp p volume)

/-- The Lᵖ norm of the Euclidean gradient in the four original coordinates. -/
def schwartzGradientNorm (p : ℝ≥0∞) (u : Field) : ℝ :=
  (eLpNorm (derivativeArray u) p volume).toReal

private theorem schwartzGradientNorm_nonneg (p : ℝ≥0∞) (u : Field) :
    0 ≤ schwartzGradientNorm p u := ENNReal.toReal_nonneg

private theorem multiplier_norm_le (d : SchwartzMap E ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ x, |d x| ≤ D) (v : Field) :
    ‖(realSchwartzMultiply d v).toLp 2 volume‖ ≤ D * ‖v.toLp 2 volume‖ := by
  have heg : eLpNorm (realSchwartzMultiply d v : E → ℂ) 2 volume ≤
      ENNReal.ofReal D * eLpNorm (v : E → ℂ) 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ _
    filter_upwards with x
    rw [realSchwartzMultiply_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hd x) (norm_nonneg _)
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, ← ENNReal.toReal_ofReal hD, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (v.eLpNorm_lt_top 2 volume)).ne heg

/-- The weak pairing of the actual divergence commutator. For symmetric real
coefficients the first term tests the outer divergence on the Schwartz field
instead of differentiating the L² correction output. -/
def weakDivergenceCommutatorPair
    (d : Index → Index → SchwartzMap E ℝ) (T : Field → FirstOrderLp 2) (u w : Field) : ℂ :=
  inner ℂ ((schwartzDivergence d w).toLp 2 volume) (T u) -
    inner ℂ (w.toLp 2 volume) (T (schwartzDivergence d u))

/-- The actual real-coefficient commutator on an L² correction output. -/
def coefficientCommutatorOutput (d : SchwartzMap E ℝ) (T : Field → FirstOrderLp 2) (u : Field) :
    FirstOrderLp 2 :=
  symbolCLM (realSchwartzCoefficient d) (T u) - T (realSchwartzMultiply d u)

private theorem inner_coefficientCommutatorOutput (d : SchwartzMap E ℝ)
    (T : Field → FirstOrderLp 2) (v w : Field) :
    inner ℂ (w.toLp 2 volume) (coefficientCommutatorOutput d T v) =
      inner ℂ ((realSchwartzMultiply d w).toLp 2 volume) (T v) -
        inner ℂ (w.toLp 2 volume) (T (realSchwartzMultiply d v)) := by
  rw [coefficientCommutatorOutput, inner_sub_right, inner_realSchwartzCoefficient]

private theorem inner_right_schwartzDivergence (d : Index → Index → SchwartzMap E ℝ)
    (v : Field) (y : FirstOrderLp 2) :
    inner ℂ y ((schwartzDivergence d v).toLp 2 volume) =
      -(∑ a : Index, ∑ b : Index, inner ℂ y
        ((coordinateDerivative a (realSchwartzMultiply (d a b) (coordinateDerivative b v))).toLp 2 volume)) := by
  let evaluate := (innerSL ℂ y).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E))
  change evaluate (schwartzDivergence d v) =
    -(∑ a : Index, ∑ b : Index, evaluate
      (coordinateDerivative a (realSchwartzMultiply (d a b) (coordinateDerivative b v))))
  simp only [schwartzDivergence, map_neg, map_sum]

private theorem inner_left_schwartzDivergence (d : Index → Index → SchwartzMap E ℝ)
    (v : Field) (y : FirstOrderLp 2) :
    inner ℂ ((schwartzDivergence d v).toLp 2 volume) y =
      -(∑ a : Index, ∑ b : Index, inner ℂ
        ((coordinateDerivative a (realSchwartzMultiply (d a b) (coordinateDerivative b v))).toLp 2 volume) y) := by
  rw [← inner_conj_symm, inner_right_schwartzDivergence]
  simp only [map_neg, map_sum, inner_conj_symm]

private theorem weakDivergenceCommutatorPair_eq
    (d : Index → Index → SchwartzMap E ℝ) (symmetric : ∀ a b, d a b = d b a)
    (T S : Field → FirstOrderLp 2) (A B : Index → Field → FirstOrderLp 2)
    (dual : ∀ v w : Field, inner ℂ (w.toLp 2 volume) (T v) = inner ℂ (S w) (v.toLp 2 volume))
    (derivative : ∀ (a : Index) (v w : Field),
      -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (T v) -
          inner ℂ (w.toLp 2 volume) (T (coordinateDerivative a v)) =
        inner ℂ (w.toLp 2 volume) (A a v))
    (derivativeDual : ∀ (a : Index) (v w : Field),
      inner ℂ (w.toLp 2 volume) (A a v) = inner ℂ (B a w) (v.toLp 2 volume))
    (u w : Field) :
    weakDivergenceCommutatorPair d T u w =
      ∑ a : Index, ∑ b : Index,
        (inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume) (A b u) +
          inner ℂ ((coordinateDerivative a w).toLp 2 volume)
            (coefficientCommutatorOutput (d a b) T (coordinateDerivative b u)) -
          inner ℂ (B a w) ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume)) := by
  let M (a b : Index) := realSchwartzMultiply (d a b)
  let left (a b : Index) := inner ℂ
    ((coordinateDerivative b (M a b (coordinateDerivative a w))).toLp 2 volume) (T u)
  let right (a b : Index) := inner ℂ (S w)
    ((coordinateDerivative a (M a b (coordinateDerivative b u))).toLp 2 volume)
  have swap : (∑ a : Index, ∑ b : Index, inner ℂ
      ((coordinateDerivative a (M a b (coordinateDerivative b w))).toLp 2 volume) (T u)) =
      ∑ a : Index, ∑ b : Index, left a b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [M, left, symmetric b a]
  have term (a b : Index) :
      inner ℂ ((M a b (coordinateDerivative a w)).toLp 2 volume) (A b u) +
          inner ℂ ((coordinateDerivative a w).toLp 2 volume)
            (coefficientCommutatorOutput (d a b) T (coordinateDerivative b u)) -
          inner ℂ (B a w) ((M a b (coordinateDerivative b u)).toLp 2 volume) =
        -left a b + right a b := by
    rw [← derivative b u (M a b (coordinateDerivative a w)), inner_coefficientCommutatorOutput,
      ← derivativeDual a (M a b (coordinateDerivative b u)) w,
      ← derivative a (M a b (coordinateDerivative b u)) w,
      dual (coordinateDerivative a (M a b (coordinateDerivative b u))) w]
    dsimp only [M, left, right]
    abel
  calc
    weakDivergenceCommutatorPair d T u w = -(∑ a : Index, ∑ b : Index, left a b) +
        ∑ a : Index, ∑ b : Index, right a b := by
      rw [weakDivergenceCommutatorPair, dual (schwartzDivergence d u) w, inner_left_schwartzDivergence,
        inner_right_schwartzDivergence, sub_neg_eq_add]
      change -(∑ a : Index, ∑ b : Index, inner ℂ
        ((coordinateDerivative a (M a b (coordinateDerivative b w))).toLp 2 volume) (T u)) +
          (∑ a : Index, ∑ b : Index, right a b) = _
      rw [swap]
    _ = ∑ a : Index, ∑ b : Index, (-left a b + right a b) := by
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (term a b).symm

private theorem coordinateDerivative_norm_le_gradient (p : ℝ≥0∞) (v : Field) (a : Index) :
    ‖(coordinateDerivative a v).toLp p volume‖ ≤ schwartzGradientNorm p v := by
  rw [SchwartzMap.norm_toLp]
  exact ENNReal.toReal_mono (memLp_derivativeArray p v).2.ne
    (eLpNorm_mono_ae (ae_of_all volume fun x => PiLp.norm_apply_le (derivativeArray v x) a))

private theorem highDerivativeLp4Sum_le_gradient (v : Field) :
    highDerivativeLp4Sum v ≤ 4 * schwartzGradientNorm 4 v := by
  calc
    _ ≤ ∑ _a : Index, schwartzGradientNorm 4 v :=
      Finset.sum_le_sum fun a _ => coordinateDerivative_norm_le_gradient 4 v a
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

/-- The three terms and energy estimate for the same original scalar
correction on the fixed Schwartz fields, using the actual weak divergence. -/
theorem exists_originalAngular_weakDivergence_commutator_bound
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∀ (d : Index → Index → SchwartzMap E ℝ), (∀ a b, d a b = d b a) →
      ∀ (D : ℝ), 0 ≤ D → (∀ a b x, |d a b x| ≤ D) →
      ∀ (L : ℝ≥0), (∀ a b x, ‖fderiv ℝ (d a b : E → ℝ) x‖ ≤ (L : ℝ)) →
      ∀ H : Field, ∃ (T : Field → FirstOrderLp 2) (A B : Index → Field → FirstOrderLp 2),
        (∀ u w : Field, inner ℂ (w.toLp 2 volume) (T u) =
          radianHighPair (originalRegularizedAngularSymbol η χ F) H u w) ∧
        (∀ (a : Index) (u w : Field),
          inner ℂ (w.toLp 2 volume) (A a u) = radianHighPair (originalRegularizedAngularSymbol η χ F)
            (coordinateDerivative a H) u w ∧
          inner ℂ (w.toLp 2 volume) (B a u) = radianHighPair
            (highAdjointSymbol (originalRegularizedAngularSymbol η χ F))
            (fun x => conj (coordinateDerivative a H x)) u w) ∧
        (∀ u w : Field, weakDivergenceCommutatorPair d T u w =
          ∑ a : Index, ∑ b : Index,
            (inner ℂ ((realSchwartzMultiply (d a b) (coordinateDerivative a w)).toLp 2 volume) (A b u) +
              inner ℂ ((coordinateDerivative a w).toLp 2 volume)
                (coefficientCommutatorOutput (d a b) T (coordinateDerivative b u)) -
              inner ℂ (B a w) ((realSchwartzMultiply (d a b) (coordinateDerivative b u)).toLp 2 volume))) ∧
        ∀ u : Field, ‖Complex.I * weakDivergenceCommutatorPair d T u u‖ ≤ C * M *
          (D * schwartzGradientNorm 2 u * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u +
           (L : ℝ) * schwartzGradientNorm 2 u * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u) := by
  have hρ₁ : ρ < 1 := hsmall.trans (by norm_num)
  obtain ⟨Corder, hCorder, firstOrder⟩ := exists_originalAngular_highAdjoint_firstOrder_and_coordinate_commutator
    η χ hr hρ hρ₁ hR hη hzero hone hχ hcut
  obtain ⟨K, Crough, hCrough, rough⟩ := exists_originalAngular_realSchwartz_roughCommutator
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  let C := 4 * Corder + Crough
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (by norm_num) hCorder) hCrough
  refine ⟨max K 27, 32 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro F W hW hQ hF M hM hjet d symmetric D hD hd L hd₁ H
  have jet27 n (hn : n ≤ 27) := hjet n (hn.trans (Nat.le_max_right K 27))
  have jetK n (hn : n ≤ K) := hjet n (hn.trans (Nat.le_max_left K 27))
  have lip (a b : Index) : LipschitzWith L (d a b : E → ℝ) :=
    lipschitzWith_of_nnnorm_fderiv_le (d a b).differentiable (fun x => hd₁ a b x)
  obtain ⟨T, S, normT, normS, pair, _⟩ := firstOrder hW hQ hF M hM jet27
  let P (v : Field) := T v (H.toLp 4 volume)
  let A (a : Index) (v : Field) := T v ((coordinateDerivative a H).toLp 4 volume)
  let B (a : Index) (v : Field) := S (coordinateDerivative a H) v
  have dual (h v w : Field) : inner ℂ (w.toLp 2 volume) (T v (h.toLp 4 volume)) =
      inner ℂ (S h w) (v.toLp 2 volume) := by
    rw [← inner_conj_symm (S h w), (pair h w v).2.2, starRingEnd_self_apply]
  have derivative (a : Index) (v w : Field) :
      -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (P v) -
          inner ℂ (w.toLp 2 volume) (P (coordinateDerivative a v)) =
        inner ℂ (w.toLp 2 volume) (A a v) := by
    simpa only [P, A, (pair H v (coordinateDerivative a w)).1, (pair H (coordinateDerivative a v) w).1,
      (pair (coordinateDerivative a H) v w).1] using
        originalRegularizedAngularPair_coordinateDerivative_commutator
          η χ hr hρ hR hη hzero hone hχ hcut hW hQ hF hM jet27 a H v w
  have terms := weakDivergenceCommutatorPair_eq d symmetric P (S H) A B (dual H) derivative
    (fun a => dual (coordinateDerivative a H))
  refine ⟨P, A, B, fun u w => (pair H u w).1,
    fun a u w => ⟨(pair (coordinateDerivative a H) u w).1, (pair (coordinateDerivative a H) u w).2.1⟩, terms, ?_⟩
  intro u
  let G₂ := schwartzGradientNorm 2 u
  let G₄ := schwartzGradientNorm 4 u
  let H₄ := schwartzGradientNorm 4 H
  let U := C * M * H₄ * G₄
  let V := C * M * (L : ℝ) * ‖H.toLp 4 volume‖ * G₄
  have h₂ : 0 ≤ G₂ := schwartzGradientNorm_nonneg 2 u
  have h₄ : 0 ≤ G₄ := schwartzGradientNorm_nonneg 4 u
  have hH : 0 ≤ H₄ := schwartzGradientNorm_nonneg 4 H
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have oneDerivative (a : Index) {x : FirstOrderLp 2}
      (hx : ‖x‖ ≤ Corder * M * ‖(coordinateDerivative a H).toLp 4 volume‖ * highDerivativeLp4Sum u) :
      ‖x‖ ≤ U := by
    calc
      _ ≤ Corder * M * H₄ * (4 * G₄) := hx.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 4 H a) (mul_nonneg hCorder hM))
        (highDerivativeLp4Sum_le_gradient u) (highDerivativeLp4Sum_nonneg u) (by positivity))
      _ = (4 * Corder) * M * H₄ * G₄ := by ring
      _ ≤ U := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCrough) hM) hH) h₄
  have boundA (a : Index) : ‖A a u‖ ≤ U := oneDerivative a (normT u _)
  have boundB (a : Index) : ‖B a u‖ ≤ U := oneDerivative a (normS _ u)
  have roughBound (a b : Index) : ‖coefficientCommutatorOutput (d a b) P (coordinateDerivative b u)‖ ≤ V := by
    let v := coordinateDerivative b u
    obtain ⟨P₁, P₂, identities, normR, _⟩ :=
      rough hW hQ hF M hM jetK (d a b) L (lip a b) v
    have eq₁ : P₁ (H.toLp 4 volume) = P v := inner_eq_of_schwartz
      (fun w => (identities H w).1.trans (pair H v w).1.symm)
    have eq₂ : P₂ (H.toLp 4 volume) = P (realSchwartzMultiply (d a b) v) :=
      inner_eq_of_schwartz (fun w => (identities H w).2.trans (pair H _ w).1.symm)
    have one := normR (H.toLp 4 volume)
    rw [eq₁, eq₂] at one
    refine one.trans ((mul_le_mul_of_nonneg_left (coordinateDerivative_norm_le_gradient 4 u b)
      (by positivity : 0 ≤ Crough * M * (L : ℝ) * ‖H.toLp 4 volume‖)).trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg (by norm_num) hCorder)) hM)
        L.coe_nonneg) (norm_nonneg _)) h₄
  have boundPartial (a : Index) : ‖(coordinateDerivative a u).toLp 2 volume‖ ≤ G₂ :=
    coordinateDerivative_norm_le_gradient 2 u a
  have boundMultiplied (a b j : Index) :
      ‖(realSchwartzMultiply (d a b) (coordinateDerivative j u)).toLp 2 volume‖ ≤ D * G₂ :=
    (multiplier_norm_le (d a b) D hD (hd a b) _).trans (mul_le_mul_of_nonneg_left (boundPartial j) hD)
  let Aterm := D * G₂ * U
  let Rterm := G₂ * V
  rw [norm_mul, Complex.norm_I, one_mul, terms u u]
  calc
    _ ≤ ∑ _a : Index, ∑ _b : Index, (Aterm + Rterm + Aterm) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (boundMultiplied a b a) (boundA b) (norm_nonneg _) (mul_nonneg hD h₂))
      · exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (boundPartial a) (roughBound a b) (norm_nonneg _) h₂)
      · rw [show Aterm = U * (D * G₂) by dsimp only [Aterm]; ring]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (boundB a) (boundMultiplied a b b) (norm_nonneg _) hU)
    _ = 16 * (Aterm + Rterm + Aterm) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    _ ≤ 32 * (Aterm + Rterm) := by
      have hRterm : 0 ≤ Rterm := mul_nonneg h₂ hV
      linarith
    _ = _ := by dsimp only [Aterm, Rterm, U, V, G₂, G₄, H₄]; ring

end Burnett.A08
