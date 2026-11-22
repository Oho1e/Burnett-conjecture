import Burnett.Analysis.AngularCaps.ActualCapAngularL3
import Burnett.Analysis.AngularCaps.CapFieldLp

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Filter Set
open scoped ENNReal BigOperators
open Burnett.Analysis.ProjectiveNullCaps

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

private theorem fieldLp_norm_le_sum_coordinateNorm {ι : Type*} [Fintype ι]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : FieldLp ι p) :
    ‖f‖ ≤ ∑ i : ι, ‖fieldCoordinateLp i f‖ := by
  classical
  let g (i : ι) (x : Space) : ℝ := ‖fieldCoordinateLp i f x‖
  have hg (i : ι) : MemLp (g i) p volume := (Lp.memLp (fieldCoordinateLp i f)).norm
  have pointwise : ∀ᵐ x ∂(volume : Measure Space), ‖f x‖ ≤ (∑ i : ι, g i) x := by
    filter_upwards [ae_all_iff.2 (fun i : ι => fieldCoordinateLp_ae i f)] with x hx
    rw [Finset.sum_apply]
    simp only [g, hx]
    have repr : (∑ i : ι, f x i • EuclideanSpace.single i (1 : ℂ)) = f x := by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun ι ℂ).sum_repr (f x)
    calc
      _ = ‖∑ i : ι, f x i • EuclideanSpace.single i (1 : ℂ)‖ := congrArg norm repr.symm
      _ ≤ _ := by
        simpa only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one] using
          norm_sum_le (s := Finset.univ) (fun i : ι => f x i • EuclideanSpace.single i (1 : ℂ))
  have finite (i : ι) : eLpNorm (g i) p volume ≠ ∞ := (hg i).eLpNorm_lt_top.ne
  have hnorm : eLpNorm (f : Space → EuclideanSpace ℂ ι) p volume ≤
      ∑ i : ι, eLpNorm (g i) p volume :=
    (eLpNorm_mono_ae_real pointwise).trans
      (eLpNorm_sum_le (fun i _ => (hg i).aestronglyMeasurable) (Fact.out : 1 ≤ p))
  have finiteSum : (∑ i : ι, eLpNorm (g i) p volume) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun i _ => finite i)
  have h := ENNReal.toReal_mono finiteSum hnorm
  rw [ENNReal.toReal_sum (fun i _ => finite i)] at h
  simpa only [Lp.norm_def, g, eLpNorm_norm] using h

/-- A scalar angular `L³` bound lifts to a finite Euclidean array with
a factor equal to the number of field components. -/
theorem liftScalarLp_angular_L3 {ι γ : Type*} [Fintype ι] [Fintype γ]
    (T : γ → ComplexLp (ENNReal.ofReal 3) →L[ℂ] ComplexLp (ENNReal.ofReal 3))
    {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ u : ComplexLp (ENNReal.ofReal 3),
      (∑ w, ‖T w u‖^3)^(1/3 : ℝ) ≤ C * ‖u‖)
    (f : FieldLp ι (ENNReal.ofReal 3)) :
    (∑ w, ‖liftScalarLp (T w) f‖^3)^(1/3 : ℝ) ≤
      ((Fintype.card ι : ℝ) * C) * ‖f‖ := by
  classical
  let a (i : ι) : PiLp (3 : ℝ≥0∞) (fun _ : γ => ℝ) :=
    WithLp.toLp 3 (fun w => ‖T w (fieldCoordinateLp i f)‖)
  let b : PiLp (3 : ℝ≥0∞) (fun _ : γ => ℝ) :=
    WithLp.toLp 3 (fun w => ‖liftScalarLp (T w) f‖)
  have hsum (w : γ) : (∑ i : ι, a i) w = ∑ i : ι, a i w := by
    let ev : PiLp (3 : ℝ≥0∞) (fun _ : γ => ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj w).comp (WithLp.linearEquiv 3 ℝ (γ → ℝ)).toLinearMap
    exact map_sum ev (fun i : ι => a i) Finset.univ
  have norm3 (z : PiLp (3 : ℝ≥0∞) (fun _ : γ => ℝ)) :
      ‖z‖ = (∑ w, ‖z w‖^3)^(1/3 : ℝ) :=
    PiLp.norm_eq_of_nat 3 (by norm_cast) z
  have hb_nonneg (w : γ) : 0 ≤ b w := norm_nonneg _
  have ha_nonneg (i : ι) (w : γ) : 0 ≤ a i w := norm_nonneg _
  have hpoint (w : γ) : b w ≤ (∑ i : ι, a i) w := by
    rw [hsum]
    change ‖liftScalarLp (T w) f‖ ≤ ∑ i : ι, ‖T w (fieldCoordinateLp i f)‖
    simpa only [fieldCoordinateLp_liftScalarLp] using
      (fieldLp_norm_le_sum_coordinateNorm (liftScalarLp (T w) f))
  have hmono : ‖b‖ ≤ ‖∑ i : ι, a i‖ := by
    rw [norm3, norm3]
    refine Real.rpow_le_rpow (Finset.sum_nonneg (fun w _ => pow_nonneg (norm_nonneg _) _))
      (Finset.sum_le_sum (fun w _ => ?_)) (by norm_num)
    rw [Real.norm_of_nonneg (hb_nonneg w),
      Real.norm_of_nonneg ((hb_nonneg w).trans (hpoint w))]
    exact pow_le_pow_left₀ (hb_nonneg w) (hpoint w) 3
  have ha (i : ι) : ‖a i‖ ≤ C * ‖f‖ := by
    rw [norm3]
    simp_rw [Real.norm_of_nonneg (ha_nonneg i _)]
    exact (hT (fieldCoordinateLp i f)).trans
      (mul_le_mul_of_nonneg_left (fieldCoordinateLp_norm_le i f) hC)
  calc
    _ = ‖b‖ := by
      rw [norm3]
      simp_rw [Real.norm_of_nonneg (hb_nonneg _)]
      rfl
    _ ≤ ‖∑ i : ι, a i‖ := hmono
    _ ≤ ∑ i : ι, ‖a i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, C * ‖f‖ := Finset.sum_le_sum fun i _ => ha i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The same actual cap family gives both angular `L³` estimates for
finite arrays with the scalar counting exponent. -/
theorem exists_uniform_actual_capMultipliers_field_angular_L3 (ι : Type*) [Fintype ι]
    {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (hND : ∀ m ∈ K, Nondegenerate m)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ D c₀ δ₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∃ C : {q : ℝ // 3 < q} → ℝ, (∀ q, 0 ≤ C q) ∧
        ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∃ S : SmoothThinConeCaps m δ (c*κ*δ^2) inner outer enlarged D,
            ∃ (P : ∀ w : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
                  (capMultiplier S.centers m δ (c*κ*δ^2) inner outer w) C₃)
              (Pplus : ∀ w : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
                  (enlargedCapMultiplier m δ (c*κ*δ^2) outer enlarged w) C₃),
              ∀ (q : {q : ℝ // 3 < q}) (f : FieldLp ι (ENNReal.ofReal 3)),
                (∑ w : ↑S.centers, ‖(P w).fieldAction f‖^3)^(1/3 : ℝ) ≤
                  ((Fintype.card ι : ℝ) * C q) *
                    (S.centers.card : ℝ)^(1/(3*(q.val-2))) * ‖f‖ ∧
                (∑ w : ↑S.centers, ‖(Pplus w).fieldAction f‖^3)^(1/3 : ℝ) ≤
                  ((Fintype.card ι : ℝ) * C q) *
                    (S.centers.card : ℝ)^(1/(3*(q.val-2))) * ‖f‖ := by
  obtain ⟨D, c₀, δ₀, hD, hc₀, hδ₀, hδone, hFamily⟩ :=
    exists_uniform_actual_capMultipliers_angular_L3 hK hFrame hND hIn hIO hOE
  refine ⟨D, c₀, δ₀, hD, hc₀, hδ₀, hδone, ?_⟩
  intro κ hκ hκsmall c hc hcsmall
  obtain ⟨C₃, hC₃, C, hC, hCaps⟩ := hFamily κ hκ hκsmall c hc hcsmall
  refine ⟨C₃, hC₃, C, hC, ?_⟩
  intro m hm δ hδ hδsmall
  obtain ⟨S, P, Pplus, hS⟩ := hCaps m hm δ hδ hδsmall
  refine ⟨S, P, Pplus, ?_⟩
  intro q f
  have hcoeff : 0 ≤ C q * (S.centers.card : ℝ)^(1/(3*(q.val-2))) :=
    mul_nonneg (hC q) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have base := liftScalarLp_angular_L3 (fun w => (P w).action) hcoeff (fun u => (hS q u).1) f
  have wide := liftScalarLp_angular_L3 (fun w => (Pplus w).action) hcoeff (fun u => (hS q u).2) f
  exact ⟨by simpa only [CapLpRealization.fieldAction, mul_assoc] using base,
    by simpa only [CapLpRealization.fieldAction, mul_assoc] using wide⟩

end Burnett.Analysis.CapFourier
