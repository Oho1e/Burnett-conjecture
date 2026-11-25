import Burnett.Analysis.TransportPatches.ProjectedDivergenceScale
import Burnett.Analysis.TransportPatches.ExtendedPatchDivergenceCoefficient
import Burnett.Analysis.TransportPatches.OriginalPatchCoefficientBounds
import Burnett.Analysis.TransportPatches.PatchCorrectionSchwartz
import Burnett.Analysis.TransportPatches.PatchProjectedLpScale
import Burnett.Analysis.TransportPatches.CubicPartitionVolume
import Burnett.Analysis.TransportPatches.CubicPatchProductRule
import Burnett.Analysis.GaugeProjection.ProjectedChartSourceBound

/-! Application of the scale bound to the actual original vacuum fields
on the same cubic patches. No coefficient extension is supplied as data. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 7300000

noncomputable section

namespace Burnett.C03

open Filter Function Set Metric MeasureTheory Burnett.P01 Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference CurvatureDifference InverseField
open Burnett.C01 (patchCenter exists_scaled_cubic_cutoffs sum_scaled_patch_measure_le
  cubed_partition_first_derivative_zero)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ContDiff ENNReal NNReal BigOperators Topology

open private coordinateJet_continuous coordinateSecondMetricJet_continuous from
  Burnett.Analysis.GaugeProjection.ProjectedChartSourceBound
open private projectedChartInverse_symmetric from
  Burnett.Analysis.GaugeProjection.ProjectedChartRepresentatives

/-- A fixed original open-chart vacuum sequence satisfies the C03
whole-space source and finite-exponent bounds, with the original
compactly supported variable coefficient and the same selected patch
for the physical and gauge fields. -/
theorem exists_original_projectedPatchSource_family
    (U K Kplus : Set CoordinateSpace) (hU : IsOpen U) (hK : IsCompact K)
    (hKplus : IsCompact Kplus) (hNested : K ⊆ interior Kplus) (hKU : Kplus ⊆ U)
    (g₀ : CoordinateSpace → Tensor2) (g : ℕ → CoordinateSpace → Tensor2)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hND₀ : ∀ x ∈ U, Matrix.det (g₀ x) ≠ 0)
    (hND : ∀ n x, x ∈ U → Matrix.det (g n x) ≠ 0)
    (hSym₀ : ∀ x ∈ U, IsSymmetricTensor (g₀ x))
    (hSym : ∀ n x, x ∈ U → IsSymmetricTensor (g n x))
    (hVac : ∀ n x, x ∈ U → ∀ i j, coordinateRicci
      (fun y => christoffel (projectedChartInverse (g n) y) (coordinateJet (g n) y)) x i j = 0)
    (hConv : TendstoUniformlyOn g g₀ atTop Kplus)
    (D : ℝ) (hD : 0 ≤ D) (hJet : ∀ n x, x ∈ Kplus → ‖coordinateJet (g n) x‖ ≤ D)
    (e : ℕ → ℝ) (he₀ : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (hError : ∀ n x, x ∈ Kplus → ‖g n x - g₀ x‖ ≤ e n) :
    ∃ (ℓ₀ M Ccoeff : ℝ) (Ccut : ℕ → ℝ) (Cₚ : {p : ℝ // 1 < p} → ℝ),
      0 < ℓ₀ ∧ 0 ≤ M ∧ 0 ≤ Ccoeff ∧ (∀ k, 0 ≤ Ccut k) ∧ (∀ p, 0 ≤ Cₚ p) ∧
      ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ →
      ∃ (s : Finset LatticeIndex) (χ χplus : LatticeIndex → CoordinateSpace → ℝ),
        let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
        (∀ x ∈ thickening ℓ K, (∑ j ∈ s, χ j x ^ 3) = 1) ∧
        (∀ x ∈ thickening ℓ K, ∀ v : CoordinateSpace,
          (∑ j ∈ s, χ j x ^ 2 * fderiv ℝ (χ j) x v) = 0) ∧
        (∑ j ∈ s, (volume : Measure CoordinateSpace) (W j)) ≤ ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume Kplus ∧
        (∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ ContDiff ℝ ∞ (χplus j) ∧
          (∀ x, 0 ≤ χ j x ∧ χplus j x ∈ Icc (0 : ℝ) 1) ∧
          tsupport (χ j) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧
          tsupport (χplus j) ⊆ W j ∧ W j ⊆ interior Kplus ∧
          (∀ x ∈ thickening ℓ (tsupport (χ j)), χplus j x = 1) ∧
          (∀ k x, ‖iteratedFDeriv ℝ k (χ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
            ‖iteratedFDeriv ℝ k (χplus j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k)) ∧
        ∀ᶠ n in atTop, ∀ j ∈ s,
          let m := matrixInverse (g₀ (patchCenter ℓ j))
          ∃ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix)
              (d : Index → Index → SchwartzMap CoordinateSpace ℝ),
            (∀ i k x, A.entry i k x = ((m i k + d i k x : ℝ) : ℂ)) ∧
            (∀ i k x, d i k x = correctionCoefficientPart (χplus j) (matrixInverse ∘ g n) m x i k) ∧
            (∀ i k, d i k = d k i) ∧
            (∀ i k x, |d i k x| ≤ Ccoeff * (ℓ + e n)) ∧
            (∀ i k x, ‖fderiv ℝ (d i k : CoordinateSpace → ℝ) x‖ ≤ 4 * Ccoeff * (1 + e n / ℓ)) ∧
            (∀ i k x, z i k x = ((χ j x * (g n x i k - g₀ x i k)) : ℝ)) ∧
            (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
              M * (volume (W j) ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e n)) ∧
            (∀ p : {p : ℝ // 1 < p},
              ProjectedPatchLpBounds p.val z (W j) (Cₚ p * e n) (Cₚ p * (1 + e n / ℓ))) := by
  obtain ⟨r, hr, hMid⟩ := hK.exists_cthickening_subset_open isOpen_interior hNested
  let Kmid := cthickening r K
  have hKmid : IsCompact Kmid := hK.cthickening
  have hMidPlus : Kmid ⊆ Kplus := hMid.trans interior_subset
  have hKMid : K ⊆ interior Kmid :=
    (self_subset_thickening hr K).trans
      (interior_maximal (thickening_subset_cthickening r K) isOpen_thickening)
  obtain ⟨ℓ₀, C, hℓ₀, hC, hCut⟩ := exists_scaled_cubic_cutoffs hK hKMid
  obtain ⟨_, G₀, _, hG₀, _, hG₀Same⟩ :=
    exists_openChartMetricRepresentatives hKplus hU hKU g g₀ hg hg₀
  obtain ⟨D₀, hD₀, hD₀Bound⟩ :=
    (hKplus.image (coordinateJet_continuous hG₀)).isBounded.exists_pos_norm_le
  obtain ⟨D₂, hD₂, hD₂Bound⟩ :=
    (hKplus.image (coordinateSecondMetricJet_continuous hG₀)).isBounded.exists_pos_norm_le
  obtain ⟨B₀, hB₀, hBgInv, hInverse⟩ :=
    eventually_original_inverseJet_bounds U Kplus hU hKplus hKU g₀ g hg₀ hg hND₀ hND hConv D hJet
  obtain ⟨Ccoeff, hCcoeff, hCoeff⟩ := eventually_original_patchCoefficient_bounds
    U Kplus hU hKplus hKU g₀ g hg₀ hg hND₀ hND hConv
    D (C 1) hD (hC 1) hJet e he₀ hError
  let DI := 16 * (2 * B₀) ^ 2 * D
  let I := B₀ + 32 * B₀ ^ 2
  let Ddiff := D + D₀
  let B := I + D + DI + 1 + Ddiff + D₂
  have hDI : 0 ≤ DI := by dsimp [DI]; positivity
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hDdiff : 0 ≤ Ddiff := by dsimp [Ddiff]; positivity
  obtain ⟨M, hM, hSource⟩ := exists_projectedDivergence_scale_bound B Ddiff (4 * Ccoeff)
    hDdiff (by positivity) C hC
  choose Cp hCp hLp using fun p : {p : ℝ // 1 < p} => exists_projectedPatchLp_scale p.val p.property
  let BGrad := C 0 + C 0 * Ddiff + C 1
  have hBGrad : 0 ≤ BGrad :=
    add_nonneg (add_nonneg (hC 0) (mul_nonneg (hC 0) hDdiff)) (hC 1)
  let CP := fun p => Cp p * BGrad
  refine ⟨ℓ₀, M, Ccoeff, C, CP, hℓ₀, hM, hCcoeff, hC, fun p => mul_nonneg (hCp p) hBGrad, ?_⟩
  intro ℓ hℓ hSmall
  obtain ⟨s, χ, χplus, hCube, hPatches⟩ := hCut ℓ hℓ hSmall
  let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
  have hWmid (j : LatticeIndex) (hj : j ∈ s) : W j ⊆ Kmid := (hPatches j hj).2.2.2.2.2.1
  have hWK (j : LatticeIndex) (hj : j ∈ s) : W j ⊆ Kplus := (hWmid j hj).trans hMidPlus
  have hSumW := sum_scaled_patch_measure_le (volume : Measure CoordinateSpace) s ℓ hℓ Kplus
    hKplus.isClosed.measurableSet hWK
  refine ⟨s, χ, χplus, hCube, ?_, hSumW, ?_, ?_⟩
  · intro x hx v
    apply cubed_partition_first_derivative_zero s χ x v
    · exact fun j hj => (hPatches j hj).1.differentiable (by simp) x
    · filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
      exact hCube y hy
  · intro j hj
    obtain ⟨hχ, hχplus, hPos, hInner, hOuter, _, hOne, hDeriv⟩ := hPatches j hj
    exact ⟨hχ, hχplus, hPos, hInner, hOuter, (hWmid j hj).trans hMid, hOne, hDeriv⟩
  have heOne := (tendsto_order.1 he).2 (1 : ℝ) zero_lt_one
  filter_upwards [hInverse, hCoeff, heOne] with n hnInv hnCoeff hnSmall
  intro j hj
  obtain ⟨hχ, hχplus, hPos, hInner, hOuter, _, hOne, hDeriv⟩ := hPatches j hj
  let S := tsupport (χ j)
  have hSW : S ⊆ W j := hInner.trans (closedBall_subset_closedBall (by linarith))
  have hχc : HasCompactSupport (χ j) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hInner
  have hχplusc : HasCompactSupport (χplus j) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hOuter
  have hSU : S ⊆ U := hSW.trans ((hWK j hj).trans hKU)
  let m := matrixInverse (g₀ (patchCenter ℓ j))
  let d (k : ℕ) := correctionCoefficientPart (χplus j) (matrixInverse ∘ g k) m
  let a (k : ℕ) (x : CoordinateSpace) := m + d k x
  have hAgree (k : ℕ) : a k =ᶠ[𝓝ˢ S] projectedChartInverse (g k) := by
    have hNear : thickening ℓ S ∈ 𝓝ˢ S :=
      isOpen_thickening.mem_nhdsSet.mpr (self_subset_thickening hℓ S)
    filter_upwards [hNear] with x hx
    change m + χplus j x • (matrixInverse (g k x) - m) = matrixInverse (g k x)
    rw [hOne x hx, one_smul]
    abel
  obtain ⟨R⟩ := exists_projectedChartRepresentatives hχc hU hSU g a g₀ hg hg₀ hSym hND hAgree
    (fun k x hx => hVac k x (hSU hx))
  have hCutPlus (x : CoordinateSpace) (_ : x ∈ W j) :
      ‖χplus j x‖ ≤ 1 ∧ ‖fderiv ℝ (χplus j) x‖ ≤ C 1 * ℓ⁻¹ := by
    have h01 := (hPos x).2
    refine ⟨?_, ?_⟩
    · simpa only [Real.norm_of_nonneg h01.1] using h01.2
    · simpa only [pow_one, ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] using
        (hDeriv 1 x).2
  have hCoef := hnCoeff ℓ hℓ j (hWK j hj) (χplus j) (hχplus.differentiable (by simp)) hOuter hCutPlus
  let Dcoef := Ccoeff * (1 + e n / ℓ)
  have hDcoef : 0 ≤ Dcoef :=
    mul_nonneg hCcoeff (add_nonneg zero_le_one (div_nonneg (he₀ n) hℓ.le))
  let L := Real.toNNReal (4 * Dcoef)
  obtain ⟨hASmooth, hLip⟩ := patch_inverse_smooth_lipschitz U hU (χplus j) hχplus
    (hOuter.trans ((hWK j hj).trans hKU)) (g n) (hg n) (hND n) m Dcoef hDcoef (fun x => (hCoef x).2)
  have hSlope : (L : ℝ) ≤ (4 * Ccoeff) * (1 + e n / ℓ) := by
    change (Real.toNNReal (4 * Dcoef) : ℝ) ≤ _
    rw [Real.coe_toNNReal', max_eq_left (mul_nonneg (by norm_num) hDcoef)]
    change 4 * (Ccoeff * (1 + e n / ℓ)) ≤ _
    rw [← mul_assoc]
  have hCenter : patchCenter ℓ j ∈ U :=
    hKU (hWK j hj (mem_closedBall_self (by linarith)))
  have hM₀ : IsSymmetricTensor m :=
    projectedChartInverse_symmetric g₀ (patchCenter ℓ j) (hSym₀ _ hCenter)
  obtain ⟨dc, hdc, hdSym, hdcBound, hdcD⟩ := exists_patchCorrectionSchwartz U hU
    (χplus j) hχplus hχplusc (hOuter.trans ((hWK j hj).trans hKU))
    (g n) (hg n) (hND n) (hSym n) m hM₀ (Ccoeff * (ℓ + e n)) Dcoef hDcoef
    (fun x => (hCoef x).1) (fun x => (hCoef x).2)
  have hPoint (x : CoordinateSpace) (hx : x ∈ S) :
      ‖R.metric n x - G₀ x‖ ≤ e n ∧
      ‖coordinateJet (R.metric n) x - coordinateJet G₀ x‖ ≤ Ddiff := by
    have hxK := hWK j hj (hSW hx)
    have hmNear := (R.metric_agrees n).filter_mono (nhds_le_nhdsSet hx)
    have hgNear := hG₀Same.filter_mono (nhds_le_nhdsSet hxK)
    constructor
    · rw [hmNear.eq_of_nhds, hgNear.eq_of_nhds]
      exact hError n x hxK
    · rw [projectedChart_coordinateJet_eq_of_eventuallyEq hmNear]
      exact (norm_sub_le _ _).trans
        (add_le_add (hJet n x hxK) (hD₀Bound _ (mem_image_of_mem _ hxK)))
  have hJets (x : CoordinateSpace) (hx : x ∈ S) :
      ‖localizedSourceJets (a n) (R.metric n) G₀ x‖ ≤ B := by
    have hxK := hWK j hj (hSW hx)
    have hANear : a n =ᶠ[𝓝 x] matrixInverse ∘ g n :=
      (hAgree n).filter_mono (nhds_le_nhdsSet hx)
    have hA : ‖a n x‖ ≤ I := by
      rw [hANear.eq_of_nhds]
      change ‖matrixInverse (g n x)‖ ≤ I
      have H := (hnInv x hxK).1.trans (mul_le_mul_of_nonneg_left (hError n x hxK) (by positivity))
      have hb := hBgInv x hxK
      have hSum := norm_add_le (matrixInverse (g n x) - matrixInverse (g₀ x)) (matrixInverse (g₀ x))
      rw [sub_add_cancel] at hSum
      have hSmall := mul_le_mul_of_nonneg_left hnSmall.le (show 0 ≤ 32 * B₀ ^ 2 by positivity)
      exact hSum.trans (by dsimp [I]; linarith)
    have hAI : ‖coordinateJet (a n) x‖ ≤ DI := by
      rw [projectedChart_coordinateJet_eq_of_eventuallyEq hANear]
      exact (hnInv x hxK).2
    have hG : ‖coordinateJet (R.metric n) x‖ ≤ D := by
      rw [projectedChart_coordinateJet_eq_of_eventuallyEq
        ((R.metric_agrees n).filter_mono (nhds_le_nhdsSet hx))]
      exact hJet n x hxK
    have hBg : ‖coordinateSecondMetricJet G₀ x‖ ≤ D₂ := hD₂Bound _ (mem_image_of_mem _ hxK)
    simp only [localizedSourceJets, Prod.norm_def, max_le_iff]
    refine ⟨hA.trans ?_, hG.trans ?_, hAI.trans ?_, (hPoint x hx).1.trans (hnSmall.le.trans ?_),
      (hPoint x hx).2.trans ?_, hBg.trans ?_⟩ <;> dsimp [B] <;> linarith
  let A := ProjectedSourceCoefficients.ofReal (fun i k x => a n x i k) hASmooth L hLip
  let z := localizedMetricSchwartz (R.metric n) G₀ (χ j) hχ hχc (R.metric_smooth n) hG₀
  have hFinal := hSource ℓ hℓ (χ j) hχ hχc (W j) (isCompact_closedBall _ _) hSW
    (fun k x _ => (hDeriv k x).1) (a n) (R.metric n) G₀ hASmooth (R.metric_smooth n) hG₀
    L hLip (R.inverse_symmetric n) (R.metric_symmetric n) (R.vacuum n) hJets (e n)
  refine ⟨A, z, dc, ?_, hdc, hdSym, hdcBound, ?_, ?_, hFinal (he₀ n) hnSmall.le hSlope hPoint, ?_⟩
  · intro i k x
    change ((m i k + d n x i k : ℝ) : ℂ) = _
    rw [hdc]
  · intro i k x
    simpa only [Dcoef, ← mul_assoc] using hdcD i k x
  · intro i k x
    change ((χ j x * (R.metric n x i k - G₀ x i k) : ℝ) : ℂ) = _
    by_cases hx : x ∈ S
    · have hxK := hWK j hj (hSW hx)
      rw [((R.metric_agrees n).filter_mono (nhds_le_nhdsSet hx)).eq_of_nhds,
        (hG₀Same.filter_mono (nhds_le_nhdsSet hxK)).eq_of_nhds]
    · have hχZero : χ j x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [hχZero, zero_mul]
  · intro p
    have hχ₀ (x : CoordinateSpace) (_ : x ∈ S) : ‖χ j x‖ ≤ C 0 := by
      simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using (hDeriv 0 x).1
    have hχ₁ (x : CoordinateSpace) (_ : x ∈ S) :
        ‖iteratedFDeriv ℝ 1 (χ j) x‖ ≤ C 1 * ℓ⁻¹ := by
      simpa only [pow_one] using (hDeriv 1 x).1
    have hLpPatch := hLp p (R.metric n) G₀ (R.metric_smooth n) hG₀
      (χ j) hχ hχc (W j) (isCompact_closedBall _ _) hSW
      (C 0) (C 1 * ℓ⁻¹) Ddiff (e n) (hC 0) (mul_nonneg (hC 1) (inv_nonneg.mpr hℓ.le))
      hDdiff (he₀ n) hχ₀ hχ₁ hPoint
    refine ProjectedPatchLpBounds.mono hLpPatch ?_ ?_
    · have hLevel : C 0 ≤ BGrad := by
        dsimp [BGrad]
        linarith [mul_nonneg (hC 0) hDdiff, hC 1]
      simpa only [CP, mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLevel (he₀ n)) (hCp p)
    · have hExtra : 0 ≤ C 0 + C 1 + (C 0 + C 0 * Ddiff) * (e n / ℓ) :=
        add_nonneg (add_nonneg (hC 0) (hC 1))
          (mul_nonneg (add_nonneg (hC 0) (mul_nonneg (hC 0) hDdiff)) (div_nonneg (he₀ n) hℓ.le))
      have hLevel : C 0 * Ddiff + C 1 * ℓ⁻¹ * e n ≤ BGrad * (1 + e n / ℓ) := by
        calc
          _ ≤ (C 0 * Ddiff + C 1 * ℓ⁻¹ * e n) +
            (C 0 + C 1 + (C 0 + C 0 * Ddiff) * (e n / ℓ)) := le_add_of_nonneg_right hExtra
          _ = _ := by dsimp [BGrad]; ring
      simpa only [CP, mul_assoc] using mul_le_mul_of_nonneg_left hLevel (hCp p)

end Burnett.C03
