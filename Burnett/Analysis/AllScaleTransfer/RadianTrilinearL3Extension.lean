import Burnett.Analysis.AllScaleTransfer.RadianSchwartzTrilinear
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Mathlib.Analysis.NormedSpace.Multilinear.Curry
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit (Joint)
open Burnett.Analysis.CapFourier (Space radianTrilinearForm)
open scoped BigOperators ENNReal NNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

abbrev RadianLp3 := Lp ℂ (ENNReal.ofReal (3 : ℝ)) (volume : Measure Space)

local instance : NormedAddCommGroup RadianLp3 := Lp.instNormedAddCommGroup
local instance : NormedSpace ℂ RadianLp3 := Lp.instNormedSpace

abbrev RadianTrilinearLp3 :=
  RadianLp3 →L[ℂ] RadianLp3 →L[ℂ] RadianLp3 →L[ℂ] ℂ

private def schwartzLp3 : SchwartzMap Space ℂ →L[ℂ] RadianLp3 :=
  SchwartzMap.toLpCLM ℂ ℂ (ENNReal.ofReal 3) volume

private def schwartzLp3Range : Submodule ℂ RadianLp3 :=
  LinearMap.range schwartzLp3.toLinearMap

local instance : NormedSpace ℂ schwartzLp3Range := Submodule.normedSpace schwartzLp3Range

private def schwartzLp3Equiv : SchwartzMap Space ℂ ≃ₗ[ℂ] schwartzLp3Range :=
  LinearEquiv.ofInjective schwartzLp3.toLinearMap (SchwartzMap.injective_toLp _ volume)

private theorem schwartzLp3Range_dense : Dense (schwartzLp3Range : Set RadianLp3) :=
  Burnett.A02.FrequencySplit.CMBilinearDual.schwartz_toLp_denseRange
    _ ENNReal.ofReal_ne_top

private def extendFromSchwartzLp3 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (T : schwartzLp3Range →L[ℂ] F) : RadianLp3 →L[ℂ] F :=
  T.extend schwartzLp3Range.subtypeL schwartzLp3Range_dense.denseRange_val
    schwartzLp3Range.subtypeₗᵢ.isometry.isUniformInducing

private theorem extendFromSchwartzLp3_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (T : schwartzLp3Range →L[ℂ] F) (x : schwartzLp3Range) :
    extendFromSchwartzLp3 T (x : RadianLp3) = T x :=
  T.extend_eq schwartzLp3Range.subtypeL schwartzLp3Range_dense.denseRange_val
    schwartzLp3Range.subtypeₗᵢ.isometry.isUniformInducing x

private theorem extendFromSchwartzLp3_norm_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : schwartzLp3Range →L[ℂ] F) : ‖extendFromSchwartzLp3 T‖ ≤ ‖T‖ := by
  have h (x : schwartzLp3Range) :
      ‖x‖ ≤ (1 : ℝ≥0) * ‖schwartzLp3Range.subtypeL x‖ := by simp
  simpa only [NNReal.coe_one, one_mul, extendFromSchwartzLp3] using
    T.opNorm_extend_le schwartzLp3Range.subtypeL schwartzLp3Range_dense.denseRange_val h

private def extendSchwartzLp3CLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] : (schwartzLp3Range →L[ℂ] F) →L[ℂ] (RadianLp3 →L[ℂ] F) := by
  let L : (schwartzLp3Range →L[ℂ] F) →ₗ[ℂ] (RadianLp3 →L[ℂ] F) := {
    toFun := extendFromSchwartzLp3
    map_add' u v := by
      apply ContinuousLinearMap.extend_unique
      ext x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        Submodule.subtypeL_apply, extendFromSchwartzLp3_apply]
    map_smul' c u := by
      apply ContinuousLinearMap.extend_unique
      ext x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        RingHom.id_apply, Submodule.subtypeL_apply, extendFromSchwartzLp3_apply] }
  exact L.mkContinuous 1 (fun T => by simpa only [one_mul] using extendFromSchwartzLp3_norm_le T)

private theorem extendSchwartzLp3CLM_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] : ‖(extendSchwartzLp3CLM (F := F))‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (fun T => by
    simpa only [one_mul] using extendFromSchwartzLp3_norm_le T)

private theorem extendSchwartzLp3CLM_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (T : schwartzLp3Range →L[ℂ] F) (x : schwartzLp3Range) :
    extendSchwartzLp3CLM T (x : RadianLp3) = T x :=
  extendFromSchwartzLp3_apply T x

private theorem extendSchwartzLastLp3_norm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {n : ℕ}
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin (n+1) => schwartzLp3Range) F) :
    ‖extendSchwartzLp3CLM.compContinuousMultilinearMap T.curryRight‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖(extendSchwartzLp3CLM (F := F))‖ * ‖T.curryRight‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖T.curryRight‖ :=
      mul_le_mul_of_nonneg_right extendSchwartzLp3CLM_norm_le (norm_nonneg T.curryRight)
    _ = ‖T‖ := by rw [one_mul, ContinuousMultilinearMap.curryRight_norm]

/-- The original Fourier form extends to a bounded complex trilinear map on
three Lebesgue L³ factors with the same bound as on Schwartz tests. -/
theorem exists_radianTrilinearForm_Lp3_extension (m : Joint → ℂ)
    (hm : AEStronglyMeasurable m volume) (H : ℝ) (hH : ∀ p, ‖m p‖ ≤ H)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ f g h : SchwartzMap Space ℂ,
      ‖radianTrilinearForm m f g h‖ ≤
        C * ‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
          ‖h.toLp (ENNReal.ofReal 3) volume‖) :
    ∃ T : RadianTrilinearLp3, ‖T‖ ≤ C ∧
      ∀ f g h : SchwartzMap Space ℂ,
        T (f.toLp (ENNReal.ofReal 3) volume) (g.toLp (ENNReal.ofReal 3) volume)
          (h.toLp (ENNReal.ofReal 3) volume) = radianTrilinearForm m f g h := by
  let rangeForm := (radianSchwartzTrilinear m hm H hH).compLinearMap
    (fun _ : Fin 3 => schwartzLp3Equiv.symm.toLinearMap)
  have eqRange (x : schwartzLp3Range) : schwartzLp3 (schwartzLp3Equiv.symm x) = (x : RadianLp3) := by
    change ((schwartzLp3Equiv (schwartzLp3Equiv.symm x)) : RadianLp3) = (x : RadianLp3)
    rw [LinearEquiv.apply_symm_apply]
  have rangeBound (x : Fin 3 → schwartzLp3Range) : ‖rangeForm x‖ ≤ C * ∏ i, ‖x i‖ := by
    have h := hBound (schwartzLp3Equiv.symm (x 0)) (schwartzLp3Equiv.symm (x 1))
      (schwartzLp3Equiv.symm (x 2))
    change ‖radianTrilinearForm m _ _ _‖ ≤
      C * ‖schwartzLp3 (schwartzLp3Equiv.symm (x 0))‖ *
        ‖schwartzLp3 (schwartzLp3Equiv.symm (x 1))‖ * ‖schwartzLp3 (schwartzLp3Equiv.symm (x 2))‖ at h
    simp only [eqRange] at h
    simpa only [rangeForm, MultilinearMap.compLinearMap_apply, LinearEquiv.coe_toLinearMap,
      radianSchwartzTrilinear_apply, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, mul_assoc] using h
  let T := rangeForm.mkContinuous C rangeBound
  let T₂ := extendSchwartzLp3CLM.compContinuousMultilinearMap T.curryRight
  let T₁ := extendSchwartzLp3CLM.compContinuousMultilinearMap T₂.curryRight
  let U := continuousMultilinearCurryFin1 ℂ schwartzLp3Range _ T₁
  refine ⟨extendSchwartzLp3CLM U, ?_, ?_⟩
  · calc
      _ ≤ ‖U‖ := extendFromSchwartzLp3_norm_le _
      _ = ‖T₁‖ := (continuousMultilinearCurryFin1 ℂ schwartzLp3Range _).norm_map T₁
      _ ≤ ‖T₂‖ := extendSchwartzLastLp3_norm_le T₂
      _ ≤ ‖T‖ := extendSchwartzLastLp3_norm_le T
      _ ≤ C := rangeForm.mkContinuous_norm_le hC rangeBound
  · intro f g h
    change extendSchwartzLp3CLM U (schwartzLp3Equiv f : RadianLp3)
      (schwartzLp3Equiv g : RadianLp3) (schwartzLp3Equiv h : RadianLp3) = _
    simp only [extendSchwartzLp3CLM_apply, U, continuousMultilinearCurryFin1_apply, T₁, T₂,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.curryRight_apply, T, MultilinearMap.coe_mkContinuous,
      rangeForm, MultilinearMap.compLinearMap_apply, LinearEquiv.coe_toLinearMap,
      radianSchwartzTrilinear_apply]
    simp [Fin.snoc]

end Burnett.A05
