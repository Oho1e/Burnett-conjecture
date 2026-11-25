import Burnett.Analysis.TransportPatches.FrozenChartPhase
import Burnett.Analysis.TransportPatches.ScreenGlobalCutoffSupport
import Burnett.Geometry.ManifoldLorentzSignature
import Mathlib.Topology.MetricSpace.Thickening

/-! The same actual global wide screen varies Lipschitzly in the chart base. -/

set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.C02

open Set Module Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.V06 TensorFrame
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open scoped BigOperators ContDiff Manifold Topology

open private euclideanUnit compact_euclideanUnit from Burnett.Analysis.FrozenScreen.CompactFamily

local notation "E" => CoordinateSpace
local notation "Param" => E × (Tensor2 × Covector)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

omit [SecondCountableTopology M] in
private theorem chartInverseMetric_isUnit (B : Field (M := M)) (hn : IsNondegenerate B)
    (c : AtlasChart M) {x : E} (hx : x ∈ c.chart.target) :
    IsUnit (Matrix.det (chartInverseMetric B c x)) := by
  change IsUnit (Matrix.det (@Inv.inv ScreenMatrix Matrix.inv (metricComponents (fixedForm B c) x)))
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact (isUnit_iff_ne_zero.mpr (fixedForm_det_ne_zero B hn c hx)).inv

omit [SecondCountableTopology M] in
private theorem chartInverseMetric_has_frame (B : Field (M := M)) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) {y : E} (hy : y ∈ c.chart.target) :
    Nonempty (LorentzFrame (chartInverseMetric B c y)) := by
  let x := c.chart.symm y
  have hx : x ∈ c.chart.source := c.chart.symm_mapsTo hy
  let b := chartTangentBasis c x hx
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  obtain ⟨e, he⟩ := hSig x
  have h := chartInverseMetric_in_basis B hSig.isSymmetric hSig.isNondegenerate c x hx
  rw [show c.chart x = y from c.chart.right_inv hy] at h
  rw [h]
  exact ⟨BasisFrame.lorentzFrame (covariantForm B x) (hSig.isNondegenerate x) b e he⟩

private theorem globalScreen_smul (inner outer : ℝ) (B H : ScreenMatrix) (q : Covector) (t : ℝ) :
    globalAngularScreenSymbol inner outer B (t • H) q = t • globalAngularScreenSymbol inner outer B H q := by
  simp only [globalAngularScreenSymbol, frozenScreenSymbol, frozenScreenProjection, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_sub, smul_smul, smul_eq_mul, mul_div_assoc,
    mul_comm, mul_left_comm]

/-- The actual global V06 multiplier symbol has a bound linear in both
the chart displacement and the input tensor, uniformly across directions. -/
theorem exists_actualWideScreen_chart_lipschitz
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ inner outer C : ℝ, 0 < inner ∧ inner < outer ∧ 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ H : Tensor2, ∀ q : Covector, q ≠ 0 →
        let S (z : E) : Tensor2 := globalAngularScreenSymbol inner outer (chartInverseMetric B c z) H q
        ‖S x - S y‖ ≤ C * ‖x - y‖ * ‖H‖ := by
  obtain ⟨δ, hδ, hδSub⟩ := hK.exists_cthickening_subset_open c.chart.open_target hKU
  obtain ⟨a, ha, haComp⟩ := hK.exists_isCompact_cthickening
  let ε := min δ a
  have hε : 0 < ε := lt_min hδ ha
  let W := Metric.cthickening ε K
  have hW : IsCompact W :=
    haComp.of_isClosed_subset Metric.isClosed_cthickening (Metric.cthickening_mono (min_le_right _ _) K)
  have hWU : W ⊆ c.chart.target := (Metric.cthickening_mono (min_le_left _ _) K).trans hδSub
  let V := Metric.thickening ε K
  have hKV : K ⊆ V := Metric.self_subset_thickening hε K
  have hVW : V ⊆ W := Metric.thickening_subset_cthickening ε K
  let G := chartInverseMetric B c
  have hGs := chartInverseMetric_smooth B hB hSig.isNondegenerate c
  let Cfg := G '' W
  have hCfg : IsCompact Cfg := hW.image_of_continuousOn (hGs.continuousOn.mono hWU)
  have hInv (R : ScreenMatrix) (hR : R ∈ Cfg) : IsUnit R.det := by
    obtain ⟨z, hz, rfl⟩ := hR
    exact chartInverseMetric_isUnit B hSig.isNondegenerate c (hWU hz)
  have hFrame (R : ScreenMatrix) (hR : R ∈ Cfg) : Nonempty (LorentzFrame R) := by
    obtain ⟨z, hz, rfl⟩ := hR
    exact chartInverseMetric_has_frame B hSig c (hWU hz)
  obtain ⟨inner, outer, hInner, hIO, hSmooth⟩ :=
    @exists_globalAngularScreenSymbol_contDiffOn Param _ _ Cfg hCfg hInv hFrame
  let U : Set Param := V ×ˢ (univ ×ˢ ({0}ᶜ : Set Covector))
  have hU : IsOpen U := Metric.isOpen_thickening.prod (isOpen_univ.prod isOpen_compl_singleton)
  let F (p : Param) : Tensor2 := globalAngularScreenSymbol inner outer (G p.1) p.2.1 p.2.2
  have hG : ContDiffOn ℝ ∞ (fun p : Param => G p.1) U :=
    hGs.comp contDiff_fst.contDiffOn (fun _ hp => hWU (hVW hp.1))
  have hAll : ContDiffOn ℝ ∞ F U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact hSmooth U (fun p : Param => G p.1) (fun p : Param => p.2.1) (fun p : Param => p.2.2)
      (fun p hp => mem_image_of_mem _ (hVW hp.1))
      (fun a b => contDiffOn_pi.mp (contDiffOn_pi.mp hG a) b)
      (fun a b => (contDiff_pi.mp (contDiff_pi.mp
        (contDiff_snd.fst : ContDiff ℝ ∞ (fun p : Param => p.2.1)) a) b).contDiffOn)
      (fun a => (contDiff_pi.mp (contDiff_snd.snd : ContDiff ℝ ∞ (fun p : Param => p.2.2)) a).contDiffOn)
      (fun _ hp => hp.2.2) i j
  let Ks : Set Param := K ×ˢ (Metric.closedBall (0 : Tensor2) 1 ×ˢ euclideanUnit)
  have hKs : IsCompact Ks := hK.prod ((isCompact_closedBall _ _).prod compact_euclideanUnit)
  have hKsU : Ks ⊆ U := by
    intro p hp
    refine ⟨hKV hp.1, mem_univ _, ?_⟩
    have hUnit : p.2.2 ⬝ᵥ p.2.2 = 1 := hp.2.2
    change p.2.2 ≠ 0
    intro hz
    simp [hz] at hUnit
  have hD : ContDiffOn ℝ 0 (fderiv ℝ F) U := hAll.fderiv_of_isOpen hU (by simp)
  obtain ⟨C, hC, hBound⟩ := (hKs.image_of_continuousOn (hD.continuousOn.mono hKsU)).isBounded.exists_pos_norm_le
  refine ⟨inner, outer, C, hInner, hIO, hC.le, ?_⟩
  intro x hx y hy H q hq S
  by_cases hH : H = 0
  · subst H
    have hz (z : E) : S z = 0 := by
      simpa only [S, zero_smul] using globalScreen_smul inner outer (G z) (0 : Tensor2) q 0
    simp [hz]
  · let H₀ := ‖H‖⁻¹ • H
    let q₀ := screenUnitCovector q
    have hHNorm : ‖H‖ ≠ 0 := norm_ne_zero_iff.mpr hH
    have hH₀ : H₀ ∈ Metric.closedBall (0 : Tensor2) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖‖H‖⁻¹ • H‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg H)), inv_mul_cancel₀ hHNorm]
    have hq₀ : q₀ ∈ euclideanUnit := screenUnitCovector_unit q hq
    let Slice : Set Param := K ×ˢ ({H₀} ×ˢ {q₀})
    have hSlice : Slice ⊆ Ks := by
      intro p hp
      have hH' : p.2.1 = H₀ := hp.2.1
      have hq' : p.2.2 = q₀ := hp.2.2
      exact ⟨hp.1, hH'.symm ▸ hH₀, hq'.symm ▸ hq₀⟩
    have hConv' : Convex ℝ Slice := hConv.prod ((convex_singleton _).prod (convex_singleton _))
    have hM := hConv'.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hAll.contDiffAt (hU.mem_nhds (hKsU (hSlice hz)))).differentiableAt (by simp))
      (fun z hz => hBound _ (mem_image_of_mem _ (hSlice hz)))
      (show (y, H₀, q₀) ∈ Slice from ⟨hy, rfl, rfl⟩)
      (show (x, H₀, q₀) ∈ Slice from ⟨hx, rfl, rfl⟩)
    have hSq : 0 < q ⬝ᵥ q := lt_of_le_of_ne
      (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) (Ne.symm (fun hz => hq (dotProduct_self_eq_zero.mp hz)))
    have hqScale : 0 < (Real.sqrt (q ⬝ᵥ q))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hSq)
    let S₀ (z : E) : Tensor2 := globalAngularScreenSymbol inner outer (G z) H₀ q
    let S₁ (z : E) : Tensor2 := globalAngularScreenSymbol inner outer (G z) H₀ q₀
    have hqEq (z : E) : S₁ z = S₀ z :=
      globalAngularScreenSymbol_degreeZero inner outer (G z) H₀ q _ hqScale
    have hSmall : ‖S₀ x - S₀ y‖ ≤ C * ‖x - y‖ := by
      change ‖S₁ x - S₁ y‖ ≤ C * ‖((x - y, H₀ - H₀, q₀ - q₀) : Param)‖ at hM
      rw [hqEq x, hqEq y] at hM
      simpa only [sub_self, Prod.norm_def, norm_zero, max_self, max_eq_left (norm_nonneg _)] using hM
    have hRep : ‖H‖ • H₀ = H := by
      change ‖H‖ • (‖H‖⁻¹ • H) = H
      rw [smul_smul, mul_inv_cancel₀ hHNorm, one_smul]
    have hScale (z : E) : S z = ‖H‖ • S₀ z := by
      calc
        S z = globalAngularScreenSymbol inner outer (G z) (‖H‖ • H₀) q :=
          congrArg (fun T => globalAngularScreenSymbol inner outer (G z) T q) hRep.symm
        _ = ‖H‖ • S₀ z := globalScreen_smul inner outer (G z) H₀ q ‖H‖
    rw [hScale x, hScale y, ← smul_sub, norm_smul, Real.norm_of_nonneg (norm_nonneg H)]
    exact (mul_le_mul_of_nonneg_left hSmall (norm_nonneg H)).trans_eq (mul_comm _ _)

end Burnett.C02
