import Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms
import Burnett.Analysis.TransportPatches.PatchLpInput
import Burnett.Analysis.TransportPatches.CubicPartitionVolume

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.V03

open Filter Metric MeasureTheory Set Burnett.A02.FrequencySplit
open Burnett.P01 Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter sum_scaled_patch_measure_le)
open scoped BigOperators ENNReal Topology ContDiff

open private entry_eLpNorm_le_projectionMatrixLpNorm from Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

/-- Keep the unprojected C03 field itself while passing from the matrix norm
to the Euclidean norm used in the cubic energy. -/
theorem originalRawPatch_euclideanLp_of_C03 {U W : Set E}
    (hU : IsOpen U) (hW : IsCompact W) (hWU : W ⊆ U)
    (g g₀ : E → Tensor2)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχW : tsupport χ ⊆ W)
    (z : ProjectionSchwartzMatrix) (hz : ∀ i j x, z i j x = ((χ x * (g x i j - g₀ x i j) : ℝ) : ℂ))
    (A B D e : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hχ₀ : ∀ x ∈ tsupport χ, ‖χ x‖ ≤ A)
    (hχ₁ : ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 1 χ x‖ ≤ B)
    (hField : ∀ x ∈ tsupport χ, ‖g x - g₀ x‖ ≤ e ∧ ‖coordinateJet g x - coordinateJet g₀ x‖ ≤ D) :
    let u (k : OrderedPair) := z k.1 k.2
    let V := ((volume : Measure E) W).toReal ^ (1 / 3 : ℝ)
    euclideanFieldValueL3 u ≤ 16 * (A * e) * V ∧
      euclideanFieldGradientL3 u ≤ 64 * (A * D + B * e) * V := by
  intro u V
  obtain ⟨G, G₀, hG, hG₀, hNear, hNear₀⟩ :=
    exists_openChartMetricRepresentatives hχc.isCompact hU (hχW.trans hWU) (fun _ : ℕ => g) g₀
      (fun _ => hg) hg₀
  have near (x : E) (hx : x ∈ tsupport χ) := (hNear 0).filter_mono (nhds_le_nhdsSet hx)
  have near₀ (x : E) (hx : x ∈ tsupport χ) := hNear₀.filter_mono (nhds_le_nhdsSet hx)
  have hJetEq (f F : E → Tensor2) (x : E) (hf : F =ᶠ[𝓝 x] f) : coordinateJet F x = coordinateJet f x := by
    funext a i j
    change fderiv ℝ (fun y => F y i j) x (EuclideanSpace.single a 1) =
      fderiv ℝ (fun y => f y i j) x (EuclideanSpace.single a 1)
    have h : (fun y => F y i j) =ᶠ[𝓝 x] fun y => f y i j :=
      hf.mono fun _ hy => congrArg (fun t : Tensor2 => t i j) hy
    rw [h.fderiv_eq]
  have hF (x : E) (hx : x ∈ tsupport χ) :
      ‖G 0 x - G₀ x‖ ≤ e ∧ ‖coordinateJet (G 0) x - coordinateJet G₀ x‖ ≤ D := by
    rw [(near x hx).eq_of_nhds, (near₀ x hx).eq_of_nhds,
      hJetEq g (G 0) x (near x hx), hJetEq g₀ G₀ x (near₀ x hx)]
    exact hField x hx
  have hRaw : localizedMetricSchwartz (G 0) G₀ χ hχ hχc (hG 0) hG₀ = z := by
    funext i j
    ext x
    rw [hz]
    change Complex.ofReal (χ x * (G 0 x i j - G₀ x i j)) = _
    by_cases hx : x ∈ tsupport χ
    · rw [(near x hx).eq_of_nhds, (near₀ x hx).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hLp := Burnett.C03.localizedMetricSchwartz_patchLp (G 0) G₀ (hG 0) hG₀ χ hχ hχc
    W hW hχW A B D e hA hB hD he hχ₀ hχ₁ hF 3 (by norm_num)
  dsimp only at hLp
  rw [hRaw] at hLp
  let μ := (volume : Measure E) W ^ (1 / 3 : ℝ)
  have hμ : μ < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hW.measure_lt_top.ne
  have hConvert (w : ProjectionSchwartzMatrix) (T : ℝ) (hT : 0 ≤ T)
      (bound : projectionMatrixLpNorm 3 w ≤ ENNReal.ofReal T * μ) (i j : Index) :
      (eLpNorm (w i j : E → ℂ) 3 volume).toReal ≤ T * V := by
    have h := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ).ne
      ((entry_eLpNorm_le_projectionMatrixLpNorm 3 w i j).trans bound)
    have hThree : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
    simpa only [hThree, ENNReal.toReal_mul, ENNReal.toReal_ofReal hT, μ, V, ENNReal.toReal_rpow] using h
  constructor
  · calc
      _ ≤ ∑ j, (eLpNorm (u j : E → ℂ) 3 volume).toReal := Burnett.C02.euclideanFieldValueL3_le_entry_sum u
      _ ≤ ∑ _j : OrderedPair, (A * e) * V := Finset.sum_le_sum fun j _ =>
        hConvert z (A * e) (mul_nonneg hA he) hLp.1 j.1 j.2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, show Fintype.card OrderedPair = 16 by decide, nsmul_eq_mul]
        norm_num
        ring
  · calc
      _ ≤ ∑ j : Index × OrderedPair, (eLpNorm (Burnett.A07.coordinateDerivative j.1 (u j.2) : E → ℂ)
        3 volume).toReal := Burnett.C02.euclideanFieldGradientL3_le_entry_sum u
      _ ≤ ∑ _j : Index × OrderedPair, (A * D + B * e) * V := Finset.sum_le_sum fun j _ =>
        hConvert (projectionMatrixDerivative j.1 z) (A * D + B * e)
          (add_nonneg (mul_nonneg hA hD) (mul_nonneg hB he)) (hLp.2 j.1) j.2.1 j.2.2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, show Fintype.card (Index × OrderedPair) = 64 by decide,
          nsmul_eq_mul]
        norm_num
        ring

/-- After fixing the patch size, the factor with the undifferentiated
field tends to zero. The other term has exactly one patch volume. -/
theorem eventual_cubic_freezing_error_le_patch_volume {J : Type} [Fintype J]
    (z : ℕ → J → SchwartzMap E ℂ) (err : ℕ → ℝ) (P : Set E)
    (ℓ A B C : ℝ) (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hY : Tendsto (fun n => euclideanFieldValueL3 (z n)) atTop (𝓝 0))
    (hX : ∀ᶠ n in atTop, euclideanFieldGradientL3 (z n) ≤
      C * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ))
    (hError : ∀ᶠ n in atTop, |err n| ≤
      A * ℓ * euclideanFieldGradientL3 (z n) ^ 3 +
        B * euclideanFieldValueL3 (z n) * euclideanFieldGradientL3 (z n) ^ 2) :
    ∀ ε > 0, ∀ᶠ n in atTop, |err n| ≤ A * C ^ 3 * ℓ * ((volume : Measure E) P).toReal + ε := by
  let V := ((volume : Measure E) P).toReal
  let M := C * V ^ (1 / 3 : ℝ)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hMass : (V ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = V := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV]
    norm_num
  have hBudget : A * ℓ * M ^ 3 = A * C ^ 3 * ℓ * V := by
    dsimp only [M]
    rw [mul_pow, hMass]
    ring
  have hZero : Tendsto (fun n => B * euclideanFieldValueL3 (z n) * M ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hY.const_mul B).mul_const (M ^ 2)
  intro ε hε
  filter_upwards [hX, hError, (tendsto_order.1 hZero).2 ε hε] with n hnX hnErr hnY
  have hX₀ : 0 ≤ euclideanFieldGradientL3 (z n) := ENNReal.toReal_nonneg
  have hY₀ : 0 ≤ euclideanFieldValueL3 (z n) := ENNReal.toReal_nonneg
  calc
    |err n| ≤ A * ℓ * euclideanFieldGradientL3 (z n) ^ 3 +
        B * euclideanFieldValueL3 (z n) * euclideanFieldGradientL3 (z n) ^ 2 := hnErr
    _ ≤ A * ℓ * M ^ 3 + B * euclideanFieldValueL3 (z n) * M ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX₀ hnX _) (mul_nonneg hA hℓ.le))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX₀ hnX _) (mul_nonneg hB hY₀))
    _ ≤ _ := by rw [hBudget]; exact add_le_add_left hnY.le _

/-- The errors of the same lattice patches are charged their actual outer
volumes, with the fixed overlap multiplicity used by C03. -/
theorem eventually_sum_cubic_freezing_errors_le_patch_volumes
    (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (K : Set E) (hK : IsCompact K)
    (hPatch : ∀ j ∈ s, closedBall (patchCenter ℓ j) (6 * ℓ) ⊆ K)
    (err : ℕ → LatticeIndex → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hError : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop,
      |err n j| ≤ A * ℓ * ((volume : Measure E) (closedBall (patchCenter ℓ j) (6 * ℓ))).toReal + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∑ j ∈ s, |err n j|) ≤ (17 ^ 4 : ℝ) * A * ℓ * ((volume : Measure E) K).toReal + ε := by
  intro ε hε
  let P (j : LatticeIndex) : Set E := closedBall (patchCenter ℓ j) (6 * ℓ)
  let v (j : LatticeIndex) := ((volume : Measure E) (P j)).toReal
  let t : ℝ := ε / (s.card + 1)
  have hDen : 0 < (s.card : ℝ) + 1 := by positivity
  have ht : 0 < t := div_pos hε hDen
  have hCount : (s.card : ℝ) * t ≤ ε := by
    dsimp only [t]
    rw [← mul_div_assoc, div_le_iff₀ hDen]
    linarith
  have hFinite (j : LatticeIndex) : (volume : Measure E) (P j) ≠ ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  have hVolumes : (∑ j ∈ s, v j) ≤ (17 ^ 4 : ℝ) * ((volume : Measure E) K).toReal := by
    have hSum := sum_scaled_patch_measure_le volume s ℓ hℓ K hK.measurableSet hPatch
    have hRight : (((17 ^ 4 : ℕ) : ℝ≥0∞) * (volume : Measure E) K) ≠ ⊤ :=
      (ENNReal.mul_lt_top (by norm_num) hK.measure_lt_top).ne
    have h := ENNReal.toReal_mono hRight hSum
    rw [ENNReal.toReal_sum (fun j _ => hFinite j), ENNReal.toReal_mul] at h
    exact_mod_cast h
  have hAll : ∀ᶠ n in atTop, ∀ j ∈ s, |err n j| ≤ A * ℓ * v j + t :=
    (s.eventually_all).2 fun j hj => hError j hj t ht
  filter_upwards [hAll] with n hn
  calc
    _ ≤ ∑ j ∈ s, (A * ℓ * v j + t) := Finset.sum_le_sum hn
    _ = A * ℓ * ∑ j ∈ s, v j + (s.card : ℝ) * t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ A * ℓ * ((17 ^ 4 : ℝ) * ((volume : Measure E) K).toReal) + ε :=
      add_le_add (mul_le_mul_of_nonneg_left hVolumes (mul_nonneg hA hℓ.le)) hCount
    _ = _ := by ring

end Burnett.V03
