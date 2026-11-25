import Burnett.Analysis.CubicEnergy.CompleteEnergy.InfraredCubicContinuity
import Burnett.Analysis.TransportPatches.OriginalThinC03Consumer

set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 5700000
noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Burnett.Fourier Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview
open Burnett.RicciSymbol (Index)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz projectionMatrixDerivative)
open Burnett.C03 (projectedGaugeComplement ProjectedPatchLpBounds)
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators ENNReal Topology

private theorem ofReal_three : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num

private theorem euclideanL3_le_sum {I : Type} [Fintype I] (F : I → SchwartzMap E ℂ) :
    (eLpNorm (fun x => WithLp.toLp 2 (fun i => F i x) : E → EuclideanSpace ℂ I) 3 volume).toReal ≤
      ∑ i, (eLpNorm (F i : E → ℂ) 3 volume).toReal := by
  let v (x : E) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => F i x)
  have hPoint (x : E) : ‖v x‖ ≤ ∑ i, ‖F i x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  have h : eLpNorm v 3 volume ≤ ∑ i, eLpNorm (F i : E → ℂ) 3 volume := calc
    _ ≤ eLpNorm (fun x => ∑ i, ‖F i x‖) 3 volume := eLpNorm_mono_real hPoint
    _ ≤ ∑ i, eLpNorm (fun x => ‖F i x‖) 3 volume := by
      rw [show (fun x => ∑ i, ‖F i x‖) = ∑ i, (fun x : E => ‖F i x‖) from
        funext (fun x => (Finset.sum_apply x Finset.univ (fun i : I => fun y : E => ‖F i y‖)).symm)]
      exact eLpNorm_sum_le (fun i _ => ((F i).memLp 3 volume).1.norm) (by norm_num)
    _ = _ := Finset.sum_congr rfl (fun i _ => eLpNorm_norm (F i : E → ℂ))
  have hFinite : (∑ i, eLpNorm (F i : E → ℂ) 3 volume) < ⊤ :=
    ENNReal.sum_lt_top.2 (fun i _ => ((F i).memLp 3 volume).eLpNorm_lt_top)
  exact (ENNReal.toReal_mono hFinite.ne h).trans_eq
    (ENNReal.toReal_sum (fun i _ => ((F i).memLp 3 volume).eLpNorm_lt_top.ne))

theorem euclideanFieldValueL3_le_entry_sum {J : Type} [Fintype J] (f : J → SchwartzMap E ℂ) :
    euclideanFieldValueL3 f ≤ ∑ j, (eLpNorm (f j : E → ℂ) 3 volume).toReal := by
  simpa only [euclideanFieldValueL3, fieldValueArray, ofReal_three] using euclideanL3_le_sum f

theorem euclideanFieldGradientL3_le_entry_sum {J : Type} [Fintype J] (f : J → SchwartzMap E ℂ) :
    euclideanFieldGradientL3 f ≤
      ∑ a : Index × J, (eLpNorm (coordinateDerivative a.1 (f a.2) : E → ℂ) 3 volume).toReal := by
  simpa only [euclideanFieldGradientL3, euclideanFieldGradientNorm, euclideanFieldGradient,
    energyPartial, coordinateDerivative, ofReal_three] using
    euclideanL3_le_sum (fun a : Index × J => coordinateDerivative a.1 (f a.2))

private theorem realL3_add_le {F : Type} [NormedAddCommGroup F] {f g : E → F}
    (hf : MemLp f 3 volume) (hg : MemLp g 3 volume) :
    (eLpNorm (f + g) 3 volume).toReal ≤ (eLpNorm f 3 volume).toReal + (eLpNorm g 3 volume).toReal := by
  have hSum := ENNReal.add_lt_top.mpr ⟨hf.eLpNorm_lt_top, hg.eLpNorm_lt_top⟩
  rw [← ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono hSum.ne (eLpNorm_add_le hf.1 hg.1 (by norm_num))

private theorem realL3_sub_le {F : Type} [NormedAddCommGroup F] {f g : E → F}
    (hf : MemLp f 3 volume) (hg : MemLp g 3 volume) :
    (eLpNorm (f - g) 3 volume).toReal ≤ (eLpNorm f 3 volume).toReal + (eLpNorm g 3 volume).toReal := by
  have hSum := ENNReal.add_lt_top.mpr ⟨hf.eLpNorm_lt_top, hg.eLpNorm_lt_top⟩
  rw [← ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono hSum.ne (eLpNorm_sub_le hf.1 hg.1 (by norm_num))

private theorem fieldValueL3_add_le {J : Type} [Fintype J] (u v : J → SchwartzMap E ℂ) :
    euclideanFieldValueL3 (u + v) ≤ euclideanFieldValueL3 u + euclideanFieldValueL3 v := by
  have eq : fieldValueArray (u + v) = fieldValueArray u + fieldValueArray v := rfl
  simpa only [euclideanFieldValueL3, ofReal_three, eq] using
    realL3_add_le (fieldValueArray_memLp u 3) (fieldValueArray_memLp v 3)

private theorem fieldValueL3_sub_le {J : Type} [Fintype J] (u v : J → SchwartzMap E ℂ) :
    euclideanFieldValueL3 (u - v) ≤ euclideanFieldValueL3 u + euclideanFieldValueL3 v := by
  have eq : fieldValueArray (u - v) = fieldValueArray u - fieldValueArray v := rfl
  simpa only [euclideanFieldValueL3, ofReal_three, eq] using
    realL3_sub_le (fieldValueArray_memLp u 3) (fieldValueArray_memLp v 3)

private theorem fieldGradientL3_add_le {J : Type} [Fintype J] (u v : J → SchwartzMap E ℂ) :
    euclideanFieldGradientL3 (u + v) ≤ euclideanFieldGradientL3 u + euclideanFieldGradientL3 v := by
  have eq : euclideanFieldGradient (u + v) = euclideanFieldGradient u + euclideanFieldGradient v := by
    funext x
    apply PiLp.ext
    intro i
    change coordinateDerivative i.1 (u i.2 + v i.2) x =
      coordinateDerivative i.1 (u i.2) x + coordinateDerivative i.1 (v i.2) x
    rw [map_add, SchwartzMap.add_apply]
  simpa only [euclideanFieldGradientL3, euclideanFieldGradientNorm, ofReal_three, eq] using
    realL3_add_le (euclideanFieldGradient_memLp u 3) (euclideanFieldGradient_memLp v 3)

private theorem fieldGradientL3_sub_le {J : Type} [Fintype J] (u v : J → SchwartzMap E ℂ) :
    euclideanFieldGradientL3 (u - v) ≤ euclideanFieldGradientL3 u + euclideanFieldGradientL3 v := by
  have eq : euclideanFieldGradient (u - v) = euclideanFieldGradient u - euclideanFieldGradient v := by
    funext x
    apply PiLp.ext
    intro i
    change coordinateDerivative i.1 (u i.2 - v i.2) x =
      coordinateDerivative i.1 (u i.2) x - coordinateDerivative i.1 (v i.2) x
    rw [map_sub, SchwartzMap.sub_apply]
  simpa only [euclideanFieldGradientL3, euclideanFieldGradientNorm, ofReal_three, eq] using
    realL3_sub_le (euclideanFieldGradient_memLp u 3) (euclideanFieldGradient_memLp v 3)

/-- The (L^3) array norm in the complete cubic energy agrees with the same
ordered array of actual whole-space derivatives used in the defect estimate. -/
theorem euclideanFieldGradientL3_of_orderedDerivative
    (f : OrderedPair → SchwartzMap E ℂ) (a : Index × OrderedPair → ComplexL2 E)
    (h : ∀ i, (coordinateDerivative i.1 (f i.2)).toLp 2 volume = a i) :
    euclideanFieldGradientL3 f = (eLpNorm (orderedGradientValue a) 3 volume).toReal := by
  have hRow (i : Index × OrderedPair) : (a i : E → ℂ) =ᵐ[volume] coordinateDerivative i.1 (f i.2) := by
    rw [← h i]
    exact (coordinateDerivative i.1 (f i.2)).coeFn_toLp 2 volume
  have hAll := ae_all_iff.mpr hRow
  have hEq : orderedGradientValue a =ᵐ[volume] euclideanFieldGradient f := by
    filter_upwards [hAll] with x hx
    exact congrArg (WithLp.toLp 2) (funext hx)
  rw [euclideanFieldGradientL3, euclideanFieldGradientNorm, ofReal_three, eLpNorm_congr_ae hEq]

/-- On the same C03 patch, the actual Schwartz projection and its original
gauge complement have both volume bounds and the small value factor. -/
theorem originalPatch_euclideanLp_of_C03
    (z : ProjectionSchwartzMatrix) (P : Set E) (cv cg : ℝ)
    (h : ProjectedPatchLpBounds 3 z P cv cg) :
    let u (k : OrderedPair) := projectionFullSchwartz z k.1 k.2
    let G (k : OrderedPair) := projectedGaugeComplement z k.1 k.2
    let V := ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
    euclideanFieldValueL3 u ≤ 16 * cv * V ∧ euclideanFieldValueL3 G ≤ 16 * cv * V ∧
      euclideanFieldGradientL3 u ≤ 64 * cg * V ∧ euclideanFieldGradientL3 G ≤ 64 * cg * V := by
  intro u G V
  have valBound (f : OrderedPair → SchwartzMap E ℂ)
      (hF : ∀ k, (eLpNorm (f k : E → ℂ) 3 volume).toReal ≤ cv * V) :
      euclideanFieldValueL3 f ≤ 16 * cv * V := calc
    _ ≤ ∑ k, (eLpNorm (f k : E → ℂ) 3 volume).toReal := euclideanFieldValueL3_le_entry_sum _
    _ ≤ ∑ _k : OrderedPair, cv * V := Finset.sum_le_sum fun k _ => hF k
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, show Fintype.card OrderedPair = 16 by decide,
      nsmul_eq_mul]; norm_num; ring
  have gradBound (f : OrderedPair → SchwartzMap E ℂ)
      (hF : ∀ a : Index × OrderedPair,
        (eLpNorm (coordinateDerivative a.1 (f a.2) : E → ℂ) 3 volume).toReal ≤ cg * V) :
      euclideanFieldGradientL3 f ≤ 64 * cg * V := calc
    _ ≤ ∑ a : Index × OrderedPair, (eLpNorm (coordinateDerivative a.1 (f a.2) : E → ℂ) 3 volume).toReal :=
      euclideanFieldGradientL3_le_entry_sum _
    _ ≤ ∑ _a : Index × OrderedPair, cg * V := Finset.sum_le_sum fun a _ => hF a
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, show Fintype.card (Index × OrderedPair) = 64 by decide,
      nsmul_eq_mul]; norm_num; ring
  refine ⟨valBound u ?_, valBound G ?_, gradBound u ?_, gradBound G ?_⟩
  · intro k
    simpa only [ofReal_three, V, ENNReal.toReal_rpow] using (h k.1 k.2).1.1
  · intro k
    simpa only [ofReal_three, V, ENNReal.toReal_rpow] using (h k.1 k.2).1.2
  · intro a
    simpa only [ofReal_three, V, ENNReal.toReal_rpow] using ((h a.2.1 a.2.2).2 a.1).1
  · intro a
    simpa only [ofReal_three, V, ENNReal.toReal_rpow] using ((h a.2.1 a.2.2).2 a.1).2

/-- For a fixed patch, vanishing value norms leave the same cubic volume gain
as the first derivatives. The second factor uses the original gauge field
alongside the thin-screen replacement. -/
theorem cubicPatch_W13_budgets {J : Type} [Fintype J]
    (u v G : ℕ → J → SchwartzMap E ℂ) (Cgrad Ce a m : ℝ)
    (hCe : 0 ≤ Ce) (ha : a ≤ 1) (hm : 0 ≤ m)
    (hU : Tendsto (fun n => euclideanFieldValueL3 (u n)) atTop (𝓝 0))
    (hV : Tendsto (fun n => euclideanFieldValueL3 (v n)) atTop (𝓝 0))
    (hG : Tendsto (fun n => euclideanFieldValueL3 (G n)) atTop (𝓝 0))
    (hGrad : ∀ᶠ n in atTop, euclideanFieldGradientL3 (u n) ≤ Cgrad * m ∧
      euclideanFieldGradientL3 (G n) ≤ Cgrad * m)
    (hDiff : ∀ ε > 0, ∀ᶠ n in atTop, euclideanFieldGradientL3 (u n - v n) ≤ Ce * a * m + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      euclideanFieldW13 (u n - v n) ≤ Ce * a * m + ε ∧
      euclideanFieldW13 (u n + G n) + euclideanFieldW13 (v n + G n) ≤ (4 * Cgrad + Ce) * m + ε := by
  intro ε hε
  have he : 0 < ε / 8 := by positivity
  have hBase : Ce * a * m ≤ Ce * m :=
    mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left ha hCe) hm
  filter_upwards [hU.eventually (Iio_mem_nhds he), hV.eventually (Iio_mem_nhds he),
    hG.eventually (Iio_mem_nhds he), hGrad, hDiff (ε / 8) he] with n hUn hVn hGn hD hCut
  have hgV : euclideanFieldGradientL3 (v n) ≤
      euclideanFieldGradientL3 (u n) + euclideanFieldGradientL3 (u n - v n) := by
    simpa only [sub_sub_cancel] using fieldGradientL3_sub_le (u n) (u n - v n)
  refine ⟨?_, ?_⟩
  · rw [euclideanFieldW13_eq]
    linarith only [hUn, hVn, hCut, hε, fieldValueL3_sub_le (u n) (v n)]
  · rw [euclideanFieldW13_eq, euclideanFieldW13_eq]
    linarith only [hUn, hVn, hGn, hD.1, hD.2, hCut, hgV, hBase, hε,
      fieldValueL3_add_le (u n) (G n), fieldValueL3_add_le (v n) (G n),
      fieldGradientL3_add_le (u n) (G n), fieldGradientL3_add_le (v n) (G n)]

end Burnett.C02
