import Burnett.Analysis.FrozenTransport.V03SegmentTaylor
import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.V03.Palatini

open Set Filter Function
open Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

/-- Taking two derivatives of a scalar coefficient in a fixed direction
keeps that direction in the last slot of the actual third derivative. -/
theorem directionalCoefficient_fderiv_and_secondFDeriv {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (C : V → ℝ) {U : Set V}
    (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) {G : V} (hG : G ∈ U) (K : V) :
    let F (A : V) := fderiv ℝ C A K
    (∀ H, fderiv ℝ F G H = secondFDeriv C G H K) ∧
    ∀ H J, secondFDeriv F G H J = secondFDeriv (fderiv ℝ C) G H J K := by
  intro F
  let D := fderiv ℝ C
  let L : (V →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ K
  let L₁ := ContinuousLinearMap.compL ℝ V (V →L[ℝ] ℝ) ℝ L
  have hD : ContDiffOn ℝ ∞ D U := hC.fderiv_of_isOpen hU (by simp)
  have hD₂ : ContDiffOn ℝ ∞ (fderiv ℝ D) U := hD.fderiv_of_isOpen hU (by simp)
  have hFirst (A : V) (hA : A ∈ U) : fderiv ℝ F A = L₁ (fderiv ℝ D A) :=
    (L.hasFDerivAt.comp A ((hD.contDiffAt (hU.mem_nhds hA)).differentiableAt (by simp)).hasFDerivAt).fderiv
  refine ⟨fun H => DFunLike.congr_fun (hFirst G hG) H, fun H J => ?_⟩
  have hNear : fderiv ℝ F =ᶠ[𝓝 G] L₁ ∘ fderiv ℝ D := by
    have hAround : ∀ᶠ A in 𝓝 G, A ∈ U := hU.mem_nhds hG
    filter_upwards [hAround] with A hA
    exact hFirst A hA
  have hSecond : fderiv ℝ (L₁ ∘ fderiv ℝ D) G = L₁.comp (secondFDeriv D G) :=
    (L₁.hasFDerivAt.comp G
      ((hD₂.contDiffAt (hU.mem_nhds hG)).differentiableAt (by simp)).hasFDerivAt).fderiv
  exact DFunLike.congr_fun (DFunLike.congr_fun (hNear.fderiv_eq.trans hSecond) H) J

theorem assembledMetricDirections_twoSlots {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : ι → Mat) (h k : ι → ℝ) (T : Mat →L[ℝ] Mat →L[ℝ] F) :
    T (assembleMetricComponents S h) (assembleMetricComponents S k) =
      ∑ i, ∑ j, (h i * k j) • T (S i) (S j) := by
  simp only [assembleMetricComponents_apply, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg (fun a : ℝ => a • T (S i) (S j)) (mul_comm (k j) (h i))

theorem assembledMetricDirections_threeSlots {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : ι → Mat) (h k v : ι → ℝ)
    (T : Mat →L[ℝ] Mat →L[ℝ] Mat →L[ℝ] F) :
    T (assembleMetricComponents S h) (assembleMetricComponents S k) (assembleMetricComponents S v) =
      ∑ i, ∑ j, ∑ l, (h i * k j * v l) • T (S i) (S j) (S l) := by
  rw [assembledMetricDirections_twoSlots]
  simp only [assembleMetricComponents_apply, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul, mul_assoc]
  let F₀ (i j l : ι) := (k j * (v l * h i)) • T (S i) (S j) (S l)
  change (∑ j, ∑ l, ∑ i, F₀ i j l) = _
  calc
    _ = ∑ j, ∑ i, ∑ l, F₀ i j l := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, ∑ l, F₀ i j l := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => ?_
      apply congrArg (fun a : ℝ => a • T (S i) (S j) (S l))
      ring

end Burnett.V03.Palatini
