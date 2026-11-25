import Burnett.Analysis.TransportPatches.ActualWideInfraredMultipliers

/-! The two cutoff choices coincide on the actual null range on small patches. -/

set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.RicciSymbol Burnett.V06 Burnett.Geometry TensorFrame
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.A02.FrequencySplit (E)
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Microlocal.Overlap
open Burnett.P01 (principalGaugeProjection)
open scoped ContDiff Manifold

open private chartInverseMetric_isUnit chartInverseMetric_has_frame from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- There is one choice of wide cutoffs smooth for the entire compact
convex chart window. On each sufficiently small patch the two true errors
agree with those of the previous Ricci-range estimate. -/
theorem exists_compatibleWideWindow {r : Metric (M := M)}
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ (i o L C η : ℝ), 0 < i ∧ i < o ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 < η ∧
      (∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)) ∧
      ∀ x₀ ∈ K, ∀ p : Cosphere r, projection p ∈ c.chart.source →
        c.chart (projection p) ∈ K → hamiltonian B hSig.isNondegenerate p = 0 →
        ∀ d : ℝ, ‖c.chart (projection p) - x₀‖ ≤ d → d ≤ 1 → L * d ≤ η →
        ∀ k : ComplexTensor2, IsSymmetricComplexTensor k →
          (∀ a b, complexRicciSymbol (chartInverseMetric B c (c.chart (projection p)))
            (atlasChartUnitCovector c p) k a b = 0) →
        let m := chartInverseMetric B c x₀
        let q := atlasChartUnitCovector c p
        let ξ : E := WithLp.toLp 2 q
        let J : ComplexTensor2 := principalGaugeProjection ξ k
        let S := complexWideScreen i o m J q
        ‖J - S‖ ≤ C * d * ‖J‖ ∧ ‖(normalizedFrozenPhase m ξ : ℂ) • S‖ ≤ C * d * ‖J‖ := by
  let F := chartInverseMetric B c
  let Q := F '' K
  have hQ : IsCompact Q :=
    hK.image_of_continuousOn ((chartInverseMetric_smooth B hB hSig.isNondegenerate c).continuousOn.mono hKU)
  have hInv (R : ScreenMatrix) (hR : R ∈ Q) : IsUnit R.det := by
    obtain ⟨x, hx, rfl⟩ := hR
    exact chartInverseMetric_isUnit B hSig.isNondegenerate c (hKU hx)
  have hFrame (R : ScreenMatrix) (hR : R ∈ Q) : Nonempty (LorentzFrame R) := by
    obtain ⟨x, hx, rfl⟩ := hR
    exact chartInverseMetric_has_frame B hSig c (hKU hx)
  obtain ⟨i, o, hi, hio, hSmooth⟩ := @exists_globalAngularScreenSymbol_contDiffOn E _ _ Q hQ hInv hFrame
  have hFreq (x : E) (hx : x ∈ K) : WideScreenFrequencySmooth i o (F x) := by
    intro H a b
    exact hSmooth ({0}ᶜ : Set E) (fun _ => F x) (fun _ => H) (fun ξ j => ξ j)
      (fun _ _ => mem_image_of_mem _ hx) (fun _ _ => contDiffOn_const) (fun _ _ => contDiffOn_const)
      (fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffOn)
      (fun _ hξ hz => hξ (by ext j; exact congrFun hz j)) a b
  obtain ⟨i₀, o₀, _, C, hi₀, hio₀, _, hC, hOld⟩ :=
    exists_actualFrozenScreen_phase_errors (r := r) B hB hSig c K hK hConv hKU
  obtain ⟨L, hL, hPhase⟩ :=
    exists_actualNull_frozenPhaseAndThinCone (r := r) B hB hSig.isSymmetric hSig.isNondegenerate c K hK hConv hKU
  refine ⟨i, o, L, C, min i i₀, hi, hio, hL, hC, lt_min hi hi₀, hFreq, ?_⟩
  intro x₀ hx₀ p hp hx hNull d hd hd₁ hSmall k hSym hRic m q ξ J S
  have hPhi : |normalizedFrozenPhase m ξ| ≤ min i i₀ :=
    (hPhase x₀ hx₀ p hp hx hNull d hd).1.trans hSmall
  rw [normalizedFrozenPhase_eq_unitPhase] at hPhi
  have hΦ : |symbolNorm m (screenUnitCovector q)| ≤ min i i₀ := hPhi
  have hNew := hΦ.trans (min_le_left _ _)
  have hOldBound := hΦ.trans (min_le_right _ _)
  have hEq : S = complexWideScreen i₀ o₀ m J q := by
    change complexWideScreen i o m J q = _
    unfold complexWideScreen
    rw [globalAngularScreenSymbol_eq_on_inner i o hi.le hio m (tensorRe J) q hNew,
      globalAngularScreenSymbol_eq_on_inner i o hi.le hio m (tensorIm J) q hNew,
      globalAngularScreenSymbol_eq_on_inner i₀ o₀ hi₀.le hio₀ m (tensorRe J) q hOldBound,
      globalAngularScreenSymbol_eq_on_inner i₀ o₀ hi₀.le hio₀ m (tensorIm J) q hOldBound]
  rw [hEq]
  have h := hOld x₀ hx₀ p hp hx hNull d hd hd₁ k hSym hRic
  exact ⟨h.1, h.2.1⟩

end Burnett.C02
