import Burnett.Analysis.AngularCaps.ActualFieldCapAngularL3
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set
open scoped ENNReal BigOperators
open Burnett.Analysis.ProjectiveNullCaps

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private theorem sum_triple_mul_le_cubeNorm {γ : Type*} [Fintype γ]
    (a b c : γ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, a i * b i * c i) ≤
      (∑ i, a i^3)^(1/3 : ℝ) * (∑ i, b i^3)^(1/3 : ℝ) * (∑ i, c i^3)^(1/3 : ℝ) := by
  classical
  have hpq : Real.HolderConjugate (3/2 : ℝ) 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have main := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun i => a i * b i) (g := c) hpq
    (fun i _ => mul_nonneg (ha i) (hb i)) (fun i _ => hc i)
  have cs := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := fun i => a i^(3/2 : ℝ)) (g := fun i => b i^(3/2 : ℝ))
    Real.HolderConjugate.two_two
    (fun i _ => Real.rpow_nonneg (ha i) _) (fun i _ => Real.rpow_nonneg (hb i) _)
  have square (x : ℝ) (hx : 0 ≤ x) : (x^(3/2 : ℝ))^(2 : ℝ) = x^3 := by
    rw [← Real.rpow_mul hx, show (3/2 : ℝ) * 2 = 3 by norm_num, Real.rpow_ofNat]
  have hpair : (∑ i, (a i * b i)^(3/2 : ℝ)) ≤
      (∑ i, a i^3)^(1/2 : ℝ) * (∑ i, b i^3)^(1/2 : ℝ) := by
    simp_rw [Real.mul_rpow (ha _) (hb _)]
    simpa only [square _ (ha _), square _ (hb _)] using cs
  have A₀ : 0 ≤ (∑ i, a i^3) := Finset.sum_nonneg fun i _ => pow_nonneg (ha i) _
  have B₀ : 0 ≤ (∑ i, b i^3) := Finset.sum_nonneg fun i _ => pow_nonneg (hb i) _
  have C₀ : 0 ≤ (∑ i, c i^3) := Finset.sum_nonneg fun i _ => pow_nonneg (hc i) _
  have AB₀ : 0 ≤ (∑ i, (a i * b i)^(3/2 : ℝ)) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg (ha i) (hb i)) _
  calc
    _ ≤ (∑ i, (a i * b i)^(3/2 : ℝ))^(1/(3/2) : ℝ) * (∑ i, c i^3)^(1/3 : ℝ) := by
      simpa only [Real.rpow_ofNat] using main
    _ ≤ ((∑ i, a i^3)^(1/2 : ℝ) * (∑ i, b i^3)^(1/2 : ℝ))^(1/(3/2) : ℝ) *
        (∑ i, c i^3)^(1/3 : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow AB₀ hpair (by norm_num))
        (Real.rpow_nonneg C₀ _)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg A₀ _) (Real.rpow_nonneg B₀ _),
        ← Real.rpow_mul A₀, ← Real.rpow_mul B₀]
      norm_num

private theorem cap_count_scale_bound {N D δ q : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hδ : 0 < δ) (hq : 3 < q) (hcount : N ≤ D/δ^2) :
    δ^2 * N^(1/(q-2)) ≤ D^(1/(q-2)) * δ^(2*(q-3)/(q-2)) := by
  have hq₂ : 0 < q - 2 := by linarith
  have power : 0 ≤ 1/(q-2) := div_nonneg zero_le_one hq₂.le
  have hexp : (2 : ℝ) - 2*(1/(q-2)) = 2*(q-3)/(q-2) := by
    field_simp [hq₂.ne']
    ring
  calc
    _ ≤ δ^2 * (D/δ^2)^(1/(q-2)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN hcount power) (sq_nonneg _)
    _ = (δ^2 : ℝ) * (D^(1/(q-2))/δ^(2*(1/(q-2)))) := by
      rw [Real.div_rpow hD (sq_nonneg δ), ← Real.rpow_natCast_mul hδ.le]
      norm_num
    _ = D^(1/(q-2)) * (δ^(2 : ℝ)/δ^(2*(1/(q-2)))) := by rw [Real.rpow_two]; ring
    _ = _ := by rw [← Real.rpow_sub hδ, hexp]

/-- Sum the localized near terms using the actual enlarged caps from the same
field angular family. The local bound is evaluated on the original three fields. -/
theorem actual_near_angular_sum_bound {ι : Type*} [Fintype ι]
    {m : Form} {δ η inner outer enlarged D C₃ : ℝ}
    (S : SmoothThinConeCaps m δ η inner outer enlarged D)
    (Pplus : ∀ j : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
      (enlargedCapMultiplier m δ η outer enlarged j) C₃)
    {q Cκ A C : ℝ} (hq : 3 < q) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hD : 0 < D) (hCκ : 0 ≤ Cκ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hAngular : ∀ v : FieldLp ι (ENNReal.ofReal 3),
      (∑ j : ↑S.centers, ‖(Pplus j).fieldAction v‖^3)^(1/3 : ℝ) ≤
        ((Fintype.card ι : ℝ) * C) * (S.centers.card : ℝ)^(1/(3*(q-2))) * ‖v‖)
    (T : ↑S.centers → FieldLp ι (ENNReal.ofReal 3) → FieldLp ι (ENNReal.ofReal 3) →
      FieldLp ι (ENNReal.ofReal 3) → ℂ)
    (f g w : FieldLp ι (ENNReal.ofReal 3))
    (hcap : ∀ j : ↑S.centers, ‖T j f g w‖ ≤ Cκ * A * δ^2 *
      (‖(Pplus j).fieldAction f‖ * ‖(Pplus j).fieldAction g‖ * ‖(Pplus j).fieldAction w‖)) :
    ‖∑ j : ↑S.centers, T j f g w‖ ≤
      (Cκ * ((Fintype.card ι : ℝ) * C)^3 * D^(1/(q-2))) * A *
        δ^(2*(q-3)/(q-2)) * ‖f‖ * ‖g‖ * ‖w‖ := by
  classical
  let N : ℝ := S.centers.card
  let e : ℝ := 1/(3*(q-2))
  let Cfield : ℝ := (Fintype.card ι : ℝ) * C
  let L : ℝ := Cfield * N^e
  let K : ℝ := Cκ * A * δ^2
  let X (v : FieldLp ι (ENNReal.ofReal 3)) (j : ↑S.centers) := ‖(Pplus j).fieldAction v‖
  let angular (v : FieldLp ι (ENNReal.ofReal 3)) := (∑ j, (X v j)^3)^(1/3 : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hX (v) (j) : 0 ≤ X v j := norm_nonneg _
  have hangular₀ (v) : 0 ≤ angular v :=
    Real.rpow_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (hX v j) _) _
  have hCfield : 0 ≤ Cfield := mul_nonneg (Nat.cast_nonneg _) hC
  have hL : 0 ≤ L := mul_nonneg hCfield (Real.rpow_nonneg hN _)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCκ hA) (sq_nonneg _)
  have hAngular' (v) : angular v ≤ L * ‖v‖ := hAngular v
  have hprod : angular f * angular g * angular w ≤
      (L * ‖f‖) * (L * ‖g‖) * (L * ‖w‖) :=
    mul_le_mul
      (mul_le_mul (hAngular' f) (hAngular' g) (hangular₀ g) (mul_nonneg hL (norm_nonneg f)))
      (hAngular' w) (hangular₀ w)
      (mul_nonneg (mul_nonneg hL (norm_nonneg f)) (mul_nonneg hL (norm_nonneg g)))
  have hpow : (N^e)^3 = N^(1/(q-2)) := by
    rw [← Real.rpow_mul_natCast hN]
    congr 1
    dsimp only [e]
    have hq₂ : q - 2 ≠ 0 := by linarith
    field_simp [hq₂]
    ring
  have hscale : δ^2 * N^(1/(q-2)) ≤ D^(1/(q-2)) * δ^(2*(q-3)/(q-2)) :=
    cap_count_scale_bound hN hD.le hδ.1 hq S.count_bound
  calc
    _ ≤ ∑ j : ↑S.centers, ‖T j f g w‖ := norm_sum_le _ _
    _ ≤ ∑ j : ↑S.centers, K * (X f j * X g j * X w j) :=
      Finset.sum_le_sum fun j _ => hcap j
    _ = K * (∑ j : ↑S.centers, X f j * X g j * X w j) := (Finset.mul_sum ..).symm
    _ ≤ K * (angular f * angular g * angular w) :=
      mul_le_mul_of_nonneg_left (sum_triple_mul_le_cubeNorm (X f) (X g) (X w) (hX f) (hX g) (hX w)) hK
    _ ≤ K * ((L * ‖f‖) * (L * ‖g‖) * (L * ‖w‖)) := mul_le_mul_of_nonneg_left hprod hK
    _ = (Cκ * Cfield^3 * A * ‖f‖ * ‖g‖ * ‖w‖) * (δ^2 * N^(1/(q-2))) := by
      dsimp only [K, L]
      rw [← hpow]
      ring
    _ ≤ (Cκ * Cfield^3 * A * ‖f‖ * ‖g‖ * ‖w‖) * (D^(1/(q-2)) * δ^(2*(q-3)/(q-2))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by dsimp only [Cfield]; ring

end Burnett.Analysis.CapFourier
