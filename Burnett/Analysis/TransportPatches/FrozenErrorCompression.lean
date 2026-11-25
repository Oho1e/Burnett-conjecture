import Burnett.Analysis.TransportPatches.ActualFrozenErrors
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingPhysicalCovariance

/-! The two genuine frozen errors compress the original ordered covariance quadratically. -/

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 6800000

noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.V06
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector densitySqrt densitySqrt_mul_self range_densitySqrt)
open Burnett.P01 (principalGaugeProjection principalGaugeProjectionMatrix tensorOfVector_principalGaugeProjectionMatrix)
open scoped BigOperators ComplexConjugate ContDiff Matrix ComplexOrder MatrixOrder Manifold

local notation "E" => CoordinateSpace
local notation "V" => OrderedPair → ℂ
local notation "Mat" => Matrix OrderedPair OrderedPair ℂ

private theorem norm_tensorOfVector (u : V) : ‖tensorOfVector u‖ = ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
    intro j
    exact norm_le_pi_norm u (i, j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (tensorOfVector u))).2
    intro ij
    exact (norm_le_pi_norm (tensorOfVector u ij.1) ij.2).trans (norm_le_pi_norm (tensorOfVector u) ij.1)

private theorem traceGram_re {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    (X * Xᴴ).trace.re = ∑ i, ∑ j, ‖X i j‖^2 := by
  simp only [trace, diag, mul_apply, Complex.re_sum, conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (X i j * conj (X i j)).re = _
  rw [Complex.mul_conj]
  simp only [Complex.ofReal_re, Complex.sq_norm]

private theorem sum_norm_sq_le (u v : V) (D : ℝ) (hD : 0 ≤ D)
    (h : ‖u‖ ≤ D * ‖v‖) :
    ∑ i, ‖u i‖^2 ≤ (16 * D^2) * ∑ i, ‖v i‖^2 := by
  let W := ∑ i, ‖v i‖^2
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : ‖v‖ ≤ Real.sqrt W := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg W)).2
    intro i
    exact (Real.le_sqrt (norm_nonneg _) hW).2
      (Finset.single_le_sum (f := fun k => ‖v k‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  calc
    ∑ i, ‖u i‖^2 ≤ ∑ _i : OrderedPair, D^2 * W := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (norm_le_pi_norm u i).trans (h.trans (mul_le_mul_of_nonneg_left hV hD))
      have hSq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (Real.sqrt_nonneg W))).2 hi
      rwa [mul_pow, Real.sq_sqrt hW] at hSq
    _ = (16 * D^2) * W := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hn : Fintype.card OrderedPair = 16 := by
        change Fintype.card (Fin 4 × Fin 4) = _
        simp
      rw [hn]
      push_cast
      ring

/-- The quadratic trace bound uses a Gram factor of the same PSD density.
The error estimate is only needed on the range of that density. -/
theorem traceCompression_le_of_range (N P T : Mat) (hN : N.PosSemidef)
    (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ v ∈ LinearMap.range N.mulVecLin, ‖T *ᵥ v‖ ≤ D * ‖P *ᵥ v‖) :
    (T * N * Tᴴ).trace.re ≤ (16 * D^2) * (P * N * Pᴴ).trace.re := by
  classical
  let U := densitySqrt N
  have hU : U * Uᴴ = N := densitySqrt_mul_self hN
  have hRewrite (A : Mat) : A * N * Aᴴ = (A * U) * (A * U)ᴴ := by
    rw [← hU, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hSwap (A : Mat) : (∑ i, ∑ j, ‖A i j‖^2) = ∑ j, ∑ i, ‖A i j‖^2 := Finset.sum_comm
  rw [hRewrite T, hRewrite P, traceGram_re, traceGram_re]
  rw [hSwap (T * U), hSwap (P * U), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj : U.col j ∈ LinearMap.range N.mulVecLin := by
    rw [← range_densitySqrt hN]
    exact ⟨Pi.single j 1, Matrix.mulVec_single_one U j⟩
  exact sum_norm_sq_le (T *ᵥ U.col j) (P *ᵥ U.col j) D hD (h _ hj)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- On the actual background null cone both ordered principal matrices
compress the original density by `16 * (C * ℓ)^2` relative to its original
physical projection. The pointwise matrix identities fix the actual symbol
actions when consuming this estimate in the norm formula. -/
theorem exists_actualFrozenScreen_traceCompression {r : Metric (M := M)}
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ inner outer C : ℝ, 0 < inner ∧ inner < outer ∧ 0 ≤ C ∧
      ∀ x₀ ∈ K, ∀ p : Cosphere r, projection p ∈ c.chart.source →
        c.chart (projection p) ∈ K → hamiltonian B hSig.isNondegenerate p = 0 →
        ∀ ℓ : ℝ, ‖c.chart (projection p) - x₀‖ ≤ ℓ → ℓ ≤ 1 →
        ∀ D : Burnett.F07.IntrinsicAmplitudeCoordinates.AmplitudeCovarianceDensity r,
        HasIntrinsicAmplitudeRicciKernel r B hSig.isNondegenerate D p →
        let N := atlasAmplitudeMatrix c D p
        N.PosSemidef →
        let m := chartInverseMetric B c x₀
        let q := atlasChartUnitCovector c p
        let ξ : E := WithLp.toLp 2 q
        let P := principalGaugeProjectionMatrix ξ
        let S := complexWideScreen inner outer m
        ∀ T₁ T₂ : Mat,
          (∀ v : V, let J := tensorOfVector (P *ᵥ v)
            tensorOfVector (T₁ *ᵥ v) = J - S J q) →
          (∀ v : V, let J := tensorOfVector (P *ᵥ v)
            tensorOfVector (T₂ *ᵥ v) = (normalizedFrozenPhase m ξ : ℂ) • S J q) →
          (T₁ * N * T₁ᴴ).trace.re ≤ 16 * (C * ℓ)^2 * (P * N * Pᴴ).trace.re ∧
          (T₂ * N * T₂ᴴ).trace.re ≤ 16 * (C * ℓ)^2 * (P * N * Pᴴ).trace.re := by
  obtain ⟨inner, outer, L, C, hIn, hIO, hL, hC, hErr⟩ :=
    exists_actualFrozenScreen_phase_errors (r := r) B hB hSig c K hK hConv hKU
  refine ⟨inner, outer, C, hIn, hIO, hC, ?_⟩
  intro x₀ hx₀ p hp px hNull ℓ hℓ hℓ₁ D hRic N hN m q ξ P S T₁ T₂ hT₁ hT₂
  have hScale : 0 ≤ C * ℓ := mul_nonneg hC ((norm_nonneg _).trans hℓ)
  have hRange (v : V) (hv : v ∈ LinearMap.range N.mulVecLin) :
      ‖T₁ *ᵥ v‖ ≤ (C * ℓ) * ‖P *ᵥ v‖ ∧ ‖T₂ *ᵥ v‖ ≤ (C * ℓ) * ‖P *ᵥ v‖ := by
    obtain ⟨w, rfl⟩ := hv
    let k := tensorOfVector (N *ᵥ w)
    obtain ⟨hSym, hR⟩ := P01.atlasAmplitudeMatrix_receiving_ricciKernel B c
      hSig.isSymmetric hSig.isNondegenerate D p hp hRic w
    have h := hErr x₀ hx₀ p hp px hNull ℓ hℓ hℓ₁ k hSym hR
    have hJ := tensorOfVector_principalGaugeProjectionMatrix ξ (N *ᵥ w)
    change tensorOfVector (P *ᵥ (N *ᵥ w)) = principalGaugeProjection ξ k at hJ
    refine ⟨?_, ?_⟩
    · change ‖T₁ *ᵥ (N *ᵥ w)‖ ≤ (C * ℓ) * ‖P *ᵥ (N *ᵥ w)‖
      rw [← norm_tensorOfVector (T₁ *ᵥ (N *ᵥ w)), ← norm_tensorOfVector (P *ᵥ (N *ᵥ w)),
        hT₁ (N *ᵥ w), hJ]
      exact h.1
    · change ‖T₂ *ᵥ (N *ᵥ w)‖ ≤ (C * ℓ) * ‖P *ᵥ (N *ᵥ w)‖
      rw [← norm_tensorOfVector (T₂ *ᵥ (N *ᵥ w)), ← norm_tensorOfVector (P *ᵥ (N *ᵥ w)),
        hT₂ (N *ᵥ w), hJ]
      exact h.2.1
  exact ⟨traceCompression_le_of_range N P T₁ hN (C * ℓ) hScale (fun v hv => (hRange v hv).1),
    traceCompression_le_of_range N P T₂ hN (C * ℓ) hScale (fun v hv => (hRange v hv).2)⟩

end Burnett.C02
