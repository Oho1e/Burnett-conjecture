import Burnett.Analysis.TransportClosure.C04HamiltonChartRegularity
import Burnett.Analysis.TransportClosure.C04PreferredCotangentSymplectic

/-! The scalar bracket in the C04 antipodal reduction is independent of the actual
preferred chart. The phase-space calculation uses the genuine lift and its
reverse derivative on the open overlap. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.C04

open Bundle Filter Function Module Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart UnitNullCompactness
open FixedCotangentChart CotangentAngularExtension
open UnitNullAngular (chartPunctured)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open scoped ContDiff Manifold Topology BigOperators

local notation "E" => CoordinateSpace

/-- The phase-space vector with the momentum derivative of the Hamiltonian in its
base component and the negative base derivative in its cotangent component. -/
def canonicalHamiltonVector (P : E → Covector → ℝ) (z : Phase) : Phase :=
  (WithLp.toLp 2 (fun i => momentumPartial i P z.1 z.2), fun i => -basePartial i P z.1 z.2)

private theorem phaseSymplectic_sum (U V : Phase) :
    phaseSymplectic U V = ∑ i : Index, (V.2 i * U.1 i - U.2 i * V.1 i) := by
  rw [phaseSymplectic_apply, Finset.sum_sub_distrib]

private theorem phaseSymplectic_sub_left (U V W : Phase) :
    phaseSymplectic (U - V) W = phaseSymplectic U W - phaseSymplectic V W := by
  simp only [phaseSymplectic, map_sub, ContinuousLinearMap.sub_apply]
  ring

private theorem phaseSymplectic_nondegenerate (U : Phase)
    (hU : ∀ V : Phase, phaseSymplectic U V = 0) : U = 0 := by
  have hx : U.1 = 0 := by
    ext i
    simpa [phaseSymplectic_sum, Pi.single_apply] using hU ((0 : E), Pi.single i 1)
  have hξ : U.2 = 0 := by
    ext i
    simpa [phaseSymplectic_sum, coordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply] using hU (coordinateBasis i, (0 : Covector))
  exact Prod.ext hx hξ

private theorem phase_linear_decomposition (D : Phase →L[ℝ] ℝ) (V : Phase) :
    D V = (∑ i : Index, V.1 i * D (coordinateBasis i, 0)) +
      ∑ i : Index, V.2 i * D (0, Pi.single i 1) := by
  have hb : D (V.1, 0) = ∑ i : Index, V.1 i * D (coordinateBasis i, 0) := by
    have h := congrArg (D.comp (ContinuousLinearMap.inl ℝ E Covector))
      (coordinateBasis.sum_repr V.1)
    simpa only [map_sum, map_smul, smul_eq_mul, coordinateBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr] using h.symm
  have hξ : D (0, V.2) = ∑ i : Index, V.2 i * D (0, Pi.single i 1) := by
    have h := congrArg (D.comp (ContinuousLinearMap.inr ℝ E Covector))
      ((Pi.basisFun ℝ Index).sum_repr V.2)
    simpa only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_repr, Pi.basisFun_apply] using h.symm
  calc
    _ = D (V.1, 0) + D (0, V.2) := by rw [← map_add]; congr 1; ext <;> simp
    _ = _ := by rw [hb, hξ]

private theorem basePartial_eq_fderiv {a : E → Covector → ℝ} {z : Phase}
    (ha : DifferentiableAt ℝ (uncurry a) z) (i : Index) :
    basePartial i a z.1 z.2 = fderiv ℝ (uncurry a) z (coordinateBasis i, 0) := by
  have h := DFunLike.congr_fun (ha.hasFDerivAt.comp z.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv (coordinateBasis i)
  have hb : Burnett.CubicExplicit.basis i = coordinateBasis i :=
    (EuclideanSpace.basisFun_apply _ _ i).symm
  simpa only [basePartial, hb] using h

private theorem momentumPartial_eq_fderiv {a : E → Covector → ℝ} {z : Phase}
    (ha : DifferentiableAt ℝ (uncurry a) z) (i : Index) :
    momentumPartial i a z.1 z.2 = fderiv ℝ (uncurry a) z (0, Pi.single i 1) := by
  have h := DFunLike.congr_fun (ha.hasFDerivAt.comp z.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv (Pi.single i 1)
  exact h

theorem phaseSymplectic_canonicalHamiltonVector (P : E → Covector → ℝ) (z V : Phase)
    (hP : DifferentiableAt ℝ (uncurry P) z) :
    phaseSymplectic (canonicalHamiltonVector P z) V = fderiv ℝ (uncurry P) z V := by
  rw [phaseSymplectic_sum, phase_linear_decomposition, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← basePartial_eq_fderiv hP, ← momentumPartial_eq_fderiv hP]
  change V.2 i * momentumPartial i P z.1 z.2 - (-basePartial i P z.1 z.2) * V.1 i =
    V.1 i * basePartial i P z.1 z.2 + V.2 i * momentumPartial i P z.1 z.2
  ring

theorem canonicalBracket_eq_fderiv (P a : E → Covector → ℝ) (z : Phase)
    (ha : DifferentiableAt ℝ (uncurry a) z) :
    canonicalBracket P a z.1 z.2 = fderiv ℝ (uncurry a) z (canonicalHamiltonVector P z) := by
  rw [canonicalBracket, phase_linear_decomposition, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← basePartial_eq_fderiv ha, ← momentumPartial_eq_fderiv ha]
  change momentumPartial i P z.1 z.2 * basePartial i a z.1 z.2 -
    basePartial i P z.1 z.2 * momentumPartial i a z.1 z.2 =
    momentumPartial i P z.1 z.2 * basePartial i a z.1 z.2 +
      (-basePartial i P z.1 z.2) * momentumPartial i a z.1 z.2
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem canonicalHamiltonVector_fixedPhaseTransition (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) (Pc Pd : E → Covector → ℝ)
    (hPc : DifferentiableAt ℝ (uncurry Pc) z)
    (hPd : DifferentiableAt ℝ (uncurry Pd) (fixedPhaseTransition c d z))
    (hP : uncurry Pd ∘ fixedPhaseTransition c d =ᶠ[𝓝 z] uncurry Pc) :
    fderiv ℝ (fixedPhaseTransition c d) z (canonicalHamiltonVector Pc z) =
      canonicalHamiltonVector Pd (fixedPhaseTransition c d z) := by
  let Φ := fixedPhaseTransition c d
  have hΦ : DifferentiableAt ℝ Φ z :=
    ((contDiffOn_fixedPhaseTransition c d).contDiffAt
      ((isOpen_phaseOverlap c d).mem_nhds hz)).differentiableAt (by simp)
  have hChain : (fderiv ℝ (uncurry Pd) (Φ z)).comp (fderiv ℝ Φ z) =
      fderiv ℝ (uncurry Pc) z := by
    rw [← fderiv_comp z hPd hΦ, hP.fderiv_eq]
  apply sub_eq_zero.mp
  apply phaseSymplectic_nondegenerate
  intro W
  obtain ⟨V, rfl⟩ := fixedPhaseTransition_fderiv_surjective c d z hz W
  rw [phaseSymplectic_sub_left, fixedPhaseTransition_symplectic c d z hz,
    phaseSymplectic_canonicalHamiltonVector _ _ _ hPc,
    phaseSymplectic_canonicalHamiltonVector _ _ _ hPd]
  exact sub_eq_zero.mpr (DFunLike.congr_fun hChain V).symm

/-- Scalar canonical brackets agree whenever both functions are the local
representatives of common functions through the actual cotangent lift. -/
theorem canonicalBracket_fixedPhaseTransition (c d : AtlasChart M)
    (z : Phase) (hz : z ∈ phaseOverlap c d) (Pc Pd ac ad : E → Covector → ℝ)
    (hPc : DifferentiableAt ℝ (uncurry Pc) z)
    (hPd : DifferentiableAt ℝ (uncurry Pd) (fixedPhaseTransition c d z))
    (hac : DifferentiableAt ℝ (uncurry ac) z)
    (had : DifferentiableAt ℝ (uncurry ad) (fixedPhaseTransition c d z))
    (hP : uncurry Pd ∘ fixedPhaseTransition c d =ᶠ[𝓝 z] uncurry Pc)
    (ha : uncurry ad ∘ fixedPhaseTransition c d =ᶠ[𝓝 z] uncurry ac) :
    canonicalBracket Pc ac z.1 z.2 =
      canonicalBracket Pd ad (fixedPhaseTransition c d z).1 (fixedPhaseTransition c d z).2 := by
  let Φ := fixedPhaseTransition c d
  have hΦ : DifferentiableAt ℝ Φ z :=
    ((contDiffOn_fixedPhaseTransition c d).contDiffAt
      ((isOpen_phaseOverlap c d).mem_nhds hz)).differentiableAt (by simp)
  have hChain : fderiv ℝ (uncurry ac) z =
      (fderiv ℝ (uncurry ad) (Φ z)).comp (fderiv ℝ Φ z) := by
    rw [← fderiv_comp z had hΦ, ha.fderiv_eq]
  rw [canonicalBracket_eq_fderiv Pc ac z hac, canonicalBracket_eq_fderiv Pd ad (Φ z) had, hChain,
    ContinuousLinearMap.comp_apply, canonicalHamiltonVector_fixedPhaseTransition c d z hz Pc Pd hPc hPd hP]

variable [IsManifold Model ∞ M]

/-- The two inverse coordinate descriptions represent the same intrinsic cotangent
point throughout the true overlap. -/
theorem cotangentChartInverse_fixedPhaseTransition_eventuallyEq (c d : M) {z : Phase}
    (hz : z ∈ phaseOverlap (.atPoint c) (.atPoint d)) :
    cotangentChartInverse d ∘ fixedPhaseTransition (.atPoint c) (.atPoint d) =ᶠ[𝓝 z]
      cotangentChartInverse c := by
  filter_upwards [(isOpen_phaseOverlap (.atPoint c) (.atPoint d)).mem_nhds hz] with y hy
  rw [Function.comp_apply, fixedPhaseTransition_atPoint_eqOn c d hy, Function.comp_apply]
  exact cotangentChart_left_inv d (show cotangentChartInverse c y ∈ cotangentSource d from hy.2)

/-- The actual local derivatives of one intrinsic punctured test, using the actual
metric Hamiltonian `dualEnergy / 2`, agree at the same cotangent point. -/
theorem chartHamiltonDerivative_eq_on_overlap
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (a : CotangentBundle M → ℝ) (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (c d : M) (p : CotangentBundle M) (hp : p ∈ puncturedCotangent)
    (hc : p.proj ∈ (chartAt E c).source) (hd : p.proj ∈ (chartAt E d).source) :
    chartHamiltonDerivative c B hn a p = chartHamiltonDerivative d B hn a p := by
  let cc := AtlasChart.atPoint c
  let dd := AtlasChart.atPoint d
  let Φ := fixedPhaseTransition cc dd
  let z := cotangentChart c p
  let Pc := chartHamiltonian c B hn
  let Pd := chartHamiltonian d B hn
  let ac (x : E) (ξ : Covector) := a (cotangentChartInverse c (x, ξ))
  let ad (x : E) (ξ : Covector) := a (cotangentChartInverse d (x, ξ))
  have he : fixedChartPhase cc p = z := fixedChartPhase_preferred c p hc
  have hz : z ∈ phaseOverlap cc dd := he ▸ fixedChartPhase_mem_overlap cc dd p hc hd
  have hzd : Φ z = cotangentChart d p :=
    (congrArg Φ he.symm).trans ((fixedPhaseTransition_fixedChartPhase cc dd p hc hd).trans
      (fixedChartPhase_preferred d p hd))
  have hzcP := cotangentChart_mem_chartPunctured c p hc hp
  have hzdP : Φ z ∈ chartPunctured d := hzd.symm ▸ cotangentChart_mem_chartPunctured d p hd hp
  have hPcT : z ∈ phaseTarget c := ⟨hzcP.1, trivial⟩
  have hPdT : Φ z ∈ phaseTarget d := ⟨hzdP.1, trivial⟩
  have hPc : DifferentiableAt ℝ (uncurry Pc) z :=
    ((contDiffOn_chartHamiltonian_joint c B hB hn hs).contDiffAt
      ((isOpen_phaseTarget c).mem_nhds hPcT)).differentiableAt (by simp)
  have hPd : DifferentiableAt ℝ (uncurry Pd) (Φ z) :=
    ((contDiffOn_chartHamiltonian_joint d B hB hn hs).contDiffAt
      ((isOpen_phaseTarget d).mem_nhds hPdT)).differentiableAt (by simp)
  have hac : DifferentiableAt ℝ (uncurry ac) z :=
    ((contDiffOn_cotangentChartTest_joint c a ha).contDiffAt
      ((isOpen_chartPunctured c).mem_nhds hzcP)).differentiableAt (by simp)
  have had : DifferentiableAt ℝ (uncurry ad) (Φ z) :=
    ((contDiffOn_cotangentChartTest_joint d a ha).contDiffAt
      ((isOpen_chartPunctured d).mem_nhds hzdP)).differentiableAt (by simp)
  have hLift := cotangentChartInverse_fixedPhaseTransition_eventuallyEq c d hz
  have hP : uncurry Pd ∘ Φ =ᶠ[𝓝 z] uncurry Pc := by
    filter_upwards [hLift] with y hy
    exact congrArg (fun q : CotangentBundle M => dualEnergy B hn q / 2) hy
  have ha' : uncurry ad ∘ Φ =ᶠ[𝓝 z] uncurry ac := by
    filter_upwards [hLift] with y hy
    exact congrArg a hy
  have h : canonicalBracket Pc ac z.1 z.2 = canonicalBracket Pd ad (Φ z).1 (Φ z).2 :=
    canonicalBracket_fixedPhaseTransition cc dd z hz Pc Pd ac ad hPc hPd hac had hP ha'
  rw [hzd] at h
  exact h

/-- The base-point choice used in the C04 parity step can be evaluated in any
preferred chart containing the base point. -/
theorem basePointHamiltonDerivative_eq_chart
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (a : CotangentBundle M → ℝ) (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (c : M) (p : CotangentBundle M) (hp : p ∈ puncturedCotangent)
    (hc : p.proj ∈ (chartAt E c).source) :
    basePointHamiltonDerivative B hn a p = chartHamiltonDerivative c B hn a p :=
  chartHamiltonDerivative_eq_on_overlap B hB hn hs a ha p.proj c p hp (mem_chart_source E _) hc

end Burnett.C04
