import Burnett.Analysis.Microlocal.Overlap.ReceivingSeparablePairing
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetAmplitudeMeasure
import Burnett.Analysis.Microlocal.RowKernelDensity

/-! An actual finite principal row annihilates the same jet covariance in a receiving chart. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.AngularCommutator (DegreeZero cutoffCommutator)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz fixedVolumeGradientSchwartz_tsupport
  fixedVolumeGradient_weak_and_uniform_L2)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixPolarization (quadratic form)
open Burnett.Microlocal.RowKernelDensity (groupRow quadratic_groupRow separableRowAction)
open Burnett.Microlocal.SeparablePositive
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff InnerProduct Manifold Matrix Topology

local notation "E" => CoordinateSpace

/-- The row-kernel argument acts on the actual cosphere in its own universe. -/
private theorem receiving_ae_quadratic_zero_and_row_kernel_of_integral_zero {I : Type} {X : Type*}
    [Fintype I] [MeasurableSpace X] (τ : Measure X) (N : X → Matrix I I ℂ) (P : X → I → ℂ)
    (hPSD : ∀ᵐ p ∂τ, (N p).PosSemidef) (hInt : Integrable (fun p => quadratic (N p) (P p)) τ)
    (hZero : (∫ p, quadratic (N p) (P p) ∂τ) = 0) :
    ∀ᵐ p ∂τ, quadratic (N p) (P p) = 0 ∧ P p ᵥ* (N p)ᵀ = 0 := by
  have hDot (p : X) : quadratic (N p) (P p) = star (P p) ⬝ᵥ (N p *ᵥ P p) := by
    simp only [quadratic, form, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSign : ∀ᵐ p ∂τ, 0 ≤ (quadratic (N p) (P p)).re ∧ (quadratic (N p) (P p)).im = 0 := by
    filter_upwards [hPSD] with p hp
    have h : 0 ≤ quadratic (N p) (P p) := by rw [hDot]; exact hp.2 _
    exact ⟨(Complex.nonneg_iff.mp h).1, (Complex.nonneg_iff.mp h).2.symm⟩
  have hRe : (∫ p, (quadratic (N p) (P p)).re ∂τ) = 0 := by
    change (∫ p, RCLike.re (quadratic (N p) (P p)) ∂τ) = 0
    rw [integral_re hInt, hZero]
    rfl
  have hReAE : (fun p => (quadratic (N p) (P p)).re) =ᵐ[τ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (hSign.mono fun _ hp => hp.1) hInt.re).mp hRe
  filter_upwards [hPSD, hSign, hReAE] with p hp hsign hre
  have hQ : quadratic (N p) (P p) = 0 := Complex.ext hre hsign.2
  refine ⟨hQ, ?_⟩
  rw [Matrix.vecMul_transpose]
  apply (hp.dotProduct_mulVec_zero_iff (P p)).mp
  rwa [← hDot p]

/-- A fixed finite sum of separated terms has the sum of the actual square-term limits. -/
theorem tendsto_separableRowInner_of_squareLimits {I J : Type} [Fintype J]
    (component : J → I) (a m : J → BoundedSymbol E) (u : ℕ → I → ComplexL2 E)
    (B : ℝ) (hB : ∀ n i, ‖u n i‖ ≤ B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hcomm : ∀ s t, Tendsto (fun n =>
      cutoffCommutator (m t) (productSymbol (conjugateSymbol (a s)) (a t)) (u n (component t)))
      atTop (𝓝 0))
    (L : J → J → ℂ)
    (hlim : ∀ s t, Tendsto (fun n => inner ℂ (u (σ n) (component s))
      (squareSymbolTerm (a t) (a s) (m t) (m s) (u (σ n) (component t)))) atTop (𝓝 (L s t))) :
    Tendsto (fun n => inner ℂ (separableRowAction component a m (u (σ n)))
      (separableRowAction component a m (u (σ n)))) atTop (𝓝 (∑ s, ∑ t, L s t)) := by
  let T (s : J) := separableOperator (a s) (m s)
  let Q (s t : J) (n : ℕ) := inner ℂ (T s (u (σ n) (component s))) (T t (u (σ n) (component t)))
  let P (s t : J) (n : ℕ) := inner ℂ (u (σ n) (component s))
    (squareSymbolTerm (a t) (a s) (m t) (m s) (u (σ n) (component t)))
  have hQ (s t : J) : Tendsto (Q s t) atTop (𝓝 (L s t)) := by
    have h := separableOperator_cross_difference_tendsto_zero (a t) (a s) (m t) (m s)
      (fun n => u n (component t)) (fun n => u n (component s)) B (fun n => hB n (component t)) (hcomm t s)
    have hc := (Complex.continuous_conj.tendsto (0 : ℂ)).comp (h.comp hσ.tendsto_atTop)
    rw [map_zero] at hc
    have he : Tendsto (fun n => Q s t n - P s t n) atTop (𝓝 0) := by
      apply hc.congr
      intro n
      change conj (Q t s n - inner ℂ
        (squareSymbolTerm (a t) (a s) (m t) (m s) (u (σ n) (component t)))
        (u (σ n) (component s))) = _
      rw [map_sub]
      congr 1
      · exact inner_conj_symm _ _
      · exact inner_conj_symm _ _
    simpa only [P, sub_add_cancel, zero_add] using (he.add (hlim s t))
  apply (tendsto_finset_sum Finset.univ (fun s _ => tendsto_finset_sum Finset.univ (fun t _ => hQ s t))).congr
  intro n
  symm
  change inner ℂ (∑ s, T s (u (σ n) (component s))) (∑ t, T t (u (σ n) (component t))) = ∑ s, ∑ t, Q s t n
  rw [sum_inner]
  simp only [inner_sum, Q]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The half-density cutoff is included in the principal row read by the global covariance. -/
def receivingPrincipalRow {r : Metric (M := M)} {J : Type} [Fintype J]
    (c : AtlasChart M) (χ : D) (component : J → JetSlot) (a m : J → BoundedSymbol E)
    (p : Cosphere r) : JetSlot → ℂ :=
  let z := atlasAngularPhaseCode c p
  groupRow component (fun s => physicalCoefficient χ z.1 * (a s z.1 * m s z.2.val))

theorem original_receiving_separableRow_kernel {J : Type} [Fintype J]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K)
    (component : J → JetSlot) (a m : J → BoundedSymbol E)
    (ha : ∀ s, ContDiff ℝ ∞ (a s : E → ℂ)) (haS : ∀ s, HasCompactSupport (a s : E → ℂ))
    (hm : ∀ s, ContDiffOn ℝ ∞ (m s : E → ℂ) ({0}ᶜ : Set E)) (hDeg : ∀ s, DegreeZero (m s : E → ℂ))
    (hStrong : let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let u := fixedVolumeGradientSchwartz B g hB hg hnB c χ hχc
      Tendsto (fun n => separableRowAction component a m (fun i => (u (σ n) i).toLp 2 volume)) atTop (𝓝 0)) :
    let ρ := A.control.restrict (amplitudeCosphereWindow r K)
    let N (p : Cosphere r) : Matrix JetSlot JetSlot ℂ := fun i j => atlasOrderedJetEntry c A.density p i j
    let R := receivingPrincipalRow c χ component a m
    (∫ p, quadratic (N p) (R p) ∂ρ) = 0 ∧
      ∀ᵐ p ∂ρ, quadratic (N p) (R p) = 0 ∧ R p ᵥ* (N p)ᵀ = 0 := by
  intro ρ N R
  let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
  let u := fixedVolumeGradientSchwartz B g hB hg hnB c χ hχc
  let w (s : J) (p : Cosphere r) :=
    let z := atlasAngularPhaseCode c p
    physicalCoefficient χ z.1 * (a s z.1 * m s z.2.val)
  let q (s t : J) (p : Cosphere r) := conj (w s p) * w t p * N p (component s) (component t)
  obtain ⟨C, _, hU, hW⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb c χ hχc
  have hComm (s t : J) : Tendsto (fun n => cutoffCommutator (m t)
      (productSymbol (conjugateSymbol (a s)) (a t)) ((u n (component t)).toLp 2 volume)) atTop (𝓝 0) := by
    exact cutoffCommutator_tendsto_zero_of_supported_weakL2 (m t)
      (productSymbol (conjugateSymbol (a s)) (a t)) (hm t) (hDeg t)
      (((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (ha s)).mul (ha t))
      (((haS s).comp_left (by simp : (starRingEnd ℂ) 0 = 0)).mul_right)
      (tsupport (χ : E → ℝ)) (test_compactSupport χ) (fun n => u n (component t))
      (fun n => fixedVolumeGradientSchwartz_tsupport B g hB hg hnB c χ hχc n (component t)) C
      (fun n => hU n (component t)) (hW (component t))
  have hTerms (s t : J) : Integrable (q s t) ρ ∧
      Tendsto (fun n => inner ℂ ((u (σ n) (component s)).toLp 2 volume)
        (squareSymbolTerm (a t) (a s) (m t) (m s) ((u (σ n) (component t)).toLp 2 volume)))
        atTop (𝓝 (∫ p, q s t p ∂ρ)) := by
    let b := productSymbol (a t) (conjugateSymbol (a s))
    let p := productSymbol (conjugateSymbol (m s)) (m t)
    have hBs : ContDiff ℝ ∞ (b : E → ℂ) := (ha t).mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (ha s))
    have hBc : HasCompactSupport (b : E → ℂ) := (haS t).mul_right
    have hPs : ContDiffOn ℝ ∞ (p : E → ℂ) ({0}ᶜ : Set E) :=
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn (hm s)).mul (hm t)
    have hPd : DegreeZero (p : E → ℂ) := by
      intro d hd ξ
      simp only [p, productSymbol_apply, conjugateSymbol_apply, hDeg s d hd ξ, hDeg t d hd ξ]
    have hG : receivingClassicalTest c A (fun x ξ => b x * p ξ) χ χ (component s) (component t) = q s t := by
      funext y
      simp only [receivingClassicalTest, q, w, N, b, p, productSymbol_apply, conjugateSymbol_apply, map_mul]
      rw [show conj (physicalCoefficient χ (atlasAngularPhaseCode c y).1) =
        physicalCoefficient χ (atlasAngularPhaseCode c y).1 from Complex.conj_ofReal _]
      ac_rfl
    have hPair := tendsto_originalVolume_receivingSeparablePairing r B g hB hg hsB hsG hnB hnG hconv hb hv
      σ hσ A hA c K hK hKc b p hBs hBc hPs hPd χ χ hχ hχ (component s) (component t)
    simpa only [hG, u, squareSymbolTerm, b, p] using hPair
  have hRow := tendsto_separableRowInner_of_squareLimits component a m
    (fun n i => (u n i).toLp 2 volume) C hU σ hσ hComm
    (fun s t => ∫ p, q s t p ∂ρ) (fun s t => (hTerms s t).2)
  have hZero : Tendsto (fun n =>
      inner ℂ (separableRowAction component a m (fun i => (u (σ n) i).toLp 2 volume))
        (separableRowAction component a m (fun i => (u (σ n) i).toLp 2 volume))) atTop (𝓝 0) := by
    simpa only [inner_zero_right] using hStrong.inner (𝕜 := ℂ) hStrong
  have hQ (p : Cosphere r) : quadratic (N p) (R p) = ∑ s, ∑ t, q s t p :=
    quadratic_groupRow (N p) component (fun s => w s p)
  have hgI (s : J) : Integrable (fun p => ∑ t, q s t p) ρ :=
    integrable_finset_sum _ (fun t _ => (hTerms s t).1)
  have hI : Integrable (fun p => quadratic (N p) (R p)) ρ := by
    simp_rw [hQ]
    exact integrable_finset_sum _ (fun s _ => hgI s)
  have hIntegral : (∫ p, quadratic (N p) (R p) ∂ρ) = 0 := by
    simp_rw [hQ]
    rw [integral_finset_sum _ (fun s _ => hgI s)]
    have hSum (s : J) : (∫ p, ∑ t, q s t p ∂ρ) = ∑ t, ∫ p, q s t p ∂ρ :=
      integral_finset_sum _ (fun t _ => (hTerms s t).1)
    simp_rw [hSum]
    exact tendsto_nhds_unique hRow hZero
  have hPos := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).1
  have hPSD : ∀ᵐ p ∂ρ, (N p).PosSemidef := by
    have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
    filter_upwards [ae_restrict_of_ae hPos, ae_restrict_mem (μ := A.control) hWin] with p hp hpc
    let b := chartTangentBasis c (projection p) (hKc hpc)
    have hN : N p = (jetAmplitudeComponents b (intrinsicJetAmplitude A.density p))ᵀ := by
      ext i j
      exact atlasOrderedJetEntry_eq_intrinsicJetComponents c A.density p (hKc hpc) i j
    rw [hN]
    exact (hp b).transpose
  exact ⟨hIntegral, receiving_ae_quadratic_zero_and_row_kernel_of_integral_zero ρ N R hPSD hI hIntegral⟩

end Burnett.Microlocal.Overlap
