import Burnett.Analysis.TransportWard.Weyl.CompactPrincipalJets
import Burnett.Analysis.TransportWard.Weyl.OriginalChartTransportSymbol
import Burnett.Analysis.TransportWard.Weyl.SharedInfraredTransportSymbol
import Burnett.Analysis.TransportWard.Weyl.LocalizedPrincipalCoefficient
import Burnett.Analysis.TransportWard.Weyl.NormalizedTestedVacuum
import Burnett.Analysis.TransportWard.Weyl.FrozenEulerQuadraticJet
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFixedTestWindow

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Filter Function MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition MaximalChart
open Burnett.A03 Burnett.A02.FrequencySplit Burnett.C02 Burnett.C04 Burnett.Analysis.TransportWardSymbol
open UnitNullCompactness CotangentAngularExtension
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ContDiff ENNReal Manifold Matrix.Norms.Elementwise Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The normalized ordered components reconstruct the metric used by C03. -/
theorem originalChartCubic_metric
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) :
    let b (x : E) (i : OrderedPair) := assembleMetricComponents orthonormalMetricDirection
      (normalizedChartMetric B c x) i.1 i.2
    let U := (chartAt E c).target
    ContDiffOn ℝ ∞ b U ∧
    (∀ x ∈ U, assembleMetricComponents frozenActionOrderedBasis (b x) =
      metricComponents (fixedForm B (AtlasChart.atPoint c)) x) ∧
    ∀ x ∈ U, assembleMetricComponents frozenActionOrderedBasis (b x) ∈ nonsingularMetricDomain := by
  intro b U
  have hChart : (fun x : E => fun i j : Index => b x (i,j)) =
      metricComponents (coordinateBilinear B c) :=
    assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric c
  have hb : ContDiffOn ℝ ∞ b U := by
    apply contDiffOn_pi.mpr
    intro i
    apply (ManifoldBilinear.contDiffOn_metricComponents B hB c i.1 i.2).congr
    intro x _
    exact congrArg (fun H : E → Tensor2 => H x i.1 i.2) hChart
  have hMetric (x : E) (hx : x ∈ U) :
      assembleMetricComponents frozenActionOrderedBasis (b x) =
        metricComponents (fixedForm B (AtlasChart.atPoint c)) x := by
    exact (assembleMetricComponents_orderedBasis (b x)).trans
      ((congrFun hChart x).trans (fixedForm_eq_preferred_components B c hx).symm)
  have hND (x : E) (hx : x ∈ U) :
      assembleMetricComponents frozenActionOrderedBasis (b x) ∈ nonsingularMetricDomain := by
    rw [hMetric x hx, fixedForm_eq_preferred_components B c hx]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c hx
  exact ⟨hb, hMetric, hND⟩

private theorem exists_uniform_schwartz_eLpNorm_top {J : Type*} [Finite J]
    (S : J → SchwartzMap E ℂ) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ j, eLpNorm (S j : E → ℂ) ⊤ volume ≤ A := by
  let seminorms (j : J) := SchwartzMap.seminorm ℝ 0 0 (S j)
  obtain ⟨M, hM⟩ := (Set.finite_range seminorms).bddAbove
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_lt_top, ?_⟩
  intro j
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x =>
    (SchwartzMap.norm_le_seminorm ℝ (S j) x).trans (hM (Set.mem_range_self j)))

/-- The global Schwartz realization retains the literal ordered Euler
coefficient on every C03 patch. -/
theorem originalChartCubic_metric_and_coefficient
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ (chartAt E c).target)
    (K : Set E) (hOne : ∀ x ∈ K, (χ : E → ℝ) x = 1) :
    let b (x : E) (i : OrderedPair) := assembleMetricComponents orthonormalMetricDirection
      (normalizedChartMetric B c x) i.1 i.2
    let U := (chartAt E c).target
    ContDiffOn ℝ ∞ b U ∧
    (∀ x ∈ U, assembleMetricComponents frozenActionOrderedBasis (b x) =
      metricComponents (fixedForm B (AtlasChart.atPoint c)) x) ∧
    (∀ x ∈ U, assembleMetricComponents frozenActionOrderedBasis (b x) ∈ nonsingularMetricDomain) ∧
    ∃ (C : Index → Index → OrderedPair → OrderedPair → OrderedPair → SchwartzMap E ℂ)
      (A : ℝ≥0∞), A < ⊤ ∧
      (∀ p q i j k, eLpNorm (C p q i j k : E → ℂ) ⊤ volume ≤ A) ∧
      ∀ p q i j k x, C p q i j k x = Complex.ofReal
        (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ) p q i j k x) := by
  classical
  intro b U
  obtain ⟨hb, hMetric, hND⟩ := originalChartCubic_metric B hB hSig c
  obtain ⟨hSmooth, hSupport, _, _, _⟩ := localizedEulerPrincipalVariationCoefficient_properties
    frozenActionOrderedBasis b χ (chartAt E c).open_target hb hND (test_smooth χ) hχ
    (test_compactSupport χ) hOne
  let R := localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ)
  have hCompact (p q : Index) (i j k : OrderedPair) : HasCompactSupport (R p q i j k) :=
    (test_compactSupport χ).of_isClosed_subset isClosed_closure (hSupport p q i j k)
  let C (p q : Index) (i j k : OrderedPair) : SchwartzMap E ℂ :=
    ((hCompact p q i j k).comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hSmooth p q i j k))
  let I := Index × Index × OrderedPair × OrderedPair × OrderedPair
  obtain ⟨A, hA, hSup⟩ := exists_uniform_schwartz_eLpNorm_top
    (fun v : I => C v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2)
  exact ⟨hb, hMetric, hND, C, A, hA, fun p q i j k => hSup (p,q,i,j,k),
    fun _ _ _ _ _ _ => rfl⟩

variable [T2Space M]

/-- The literal chart symbol has the center jet and parity budgets for
the fixed infrared multiplier used in the frozen cubic form. -/
theorem originalChartCubic_fixedInfrared_data
    (c : M) (f : CotangentBundle M → ℝ) (hf : IsDegreeOneTransportTest f) (ho : IsAntipodallyOdd f)
    {S : Set M} (hS : IsCompact S) (hSC : S ⊆ (chartAt E c).source)
    (hOff : ∀ p ∈ puncturedCotangent, p.proj ∉ S → f p = 0) :
    let a (x ξ : E) := originalChartTransportSymbol c f x (WithLp.ofLp ξ)
    let β (x ξ : E) := fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ
    IsCompact ((chartAt E c) '' S) ∧ (∀ x ∉ (chartAt E c) '' S, ∀ ξ, a x ξ = 0) ∧
    (∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ) ∧
    (∀ x ξ, a x (-ξ) = -a x ξ) ∧
    ContDiff ℝ ∞ (uncurry β) ∧ (∀ x ∉ (chartAt E c) '' S, ∀ ξ, β x ξ = 0) ∧
    (∀ x ξ, 1 < ‖ξ‖ → β x ξ = a x ξ) ∧
    (∀ x ξ, β x (-ξ) = -β x ξ) ∧
    (∀ x, ContDiffOn ℝ ∞ (a x) {ξ | ξ ≠ 0}) ∧
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x n, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (a x) ξ‖ ≤ D := by
  intro a β
  let K := (chartAt E c) '' S
  let q := originalChartTransportSymbol c f
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)
  obtain ⟨hK, _, hOffK, hSmooth, hHom, hOdd⟩ := originalChartTransportSymbol_properties c f hf ho hS hSC hOff
  have ha (x : E) (hx : x ∉ K) (ξ : E) : a x ξ = 0 := hOffK x hx (T ξ)
  have hOdd' (x ξ : E) : a x (-ξ) = -a x ξ := by
    change q x (T (-ξ)) = -q x (T ξ)
    rw [map_neg]
    exact hOdd x (T ξ)
  have hHom' (x : E) (t : ℝ) (ht : 0 < t) (ξ : E) : a x (t • ξ) = t * a x ξ := by
    by_cases hξ : ξ = 0
    · subst ξ
      have hzero := hOdd' x 0
      rw [neg_zero] at hzero
      have hzero' : a x 0 = 0 := by linarith
      simp only [smul_zero, hzero', mul_zero]
    · change q x (T (t • ξ)) = t * q x (T ξ)
      rw [map_smul]
      exact hHom x t ht (T ξ) (fun h => hξ (T.injective (h.trans (map_zero T).symm)))
  obtain ⟨hβc, _, _⟩ := sharedInfraredTransportSymbol_radian_properties wardFixedTestCutoff q K
    wardFixedTestCutoff_profile_one wardFixedTestCutoff_profile_zero hSmooth hOffK hHom
  have hβ : ContDiff ℝ ∞ (uncurry β) := by
    exact Complex.reCLM.contDiff.comp hβc
  have hβOff (x : E) (hx : x ∉ K) (ξ : E) : β x ξ = 0 := by
    simp only [β, fixedInfraredSymbol, ha x hx ξ, mul_zero, fixedRadianProfile,
      SchwartzMap.zero_apply, Complex.zero_re, add_zero]
  have hβHigh (x ξ : E) (hξ : 1 < ‖ξ‖) : β x ξ = a x ξ :=
    fixedInfraredSymbol_outside wardFixedTestCutoff 0 (a x) ξ (wardFixedTestCutoff_profile_zero ξ hξ)
      (by simp only [fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re])
  have hFreq (x : E) : ContDiffOn ℝ ∞ (a x) {ξ : E | ξ ≠ 0} := by
    let e (ξ : E) : E × Covector := (x, T ξ)
    have hE : ContDiff ℝ ∞ e := contDiff_const.prodMk T.contDiff
    apply hSmooth.comp hE.contDiffOn
    intro z hz
    exact ⟨mem_univ x, fun h => hz (T.injective (h.trans (map_zero T).symm))⟩
  obtain ⟨V, _, hSphere, _, _, _, hBudget⟩ :=
    compact_homogeneous_symbol_mixed_jet_budget a β K hK hβ hβOff hβHigh
      (fun x t ht ξ => by simpa only [smul_eq_mul] using hHom' x t ht ξ)
  obtain ⟨D, hD, hJ⟩ := hBudget 16 0
  refine ⟨hK, ha, hHom', hOdd', hβ, hβOff, hβHigh, fun x ξ => wardFixedTestCutoff_odd (a x) (hOdd' x) ξ,
    hFreq, D, hD, fun x n hn ξ hξ => ?_⟩
  simpa only [norm_iteratedFDeriv_zero] using
    hJ n hn 0 le_rfl x ξ (hSphere hξ)

end Burnett.V03.Palatini
