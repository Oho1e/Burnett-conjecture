import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderActualSectionAction
import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSymmetricJet

/-! Localize the original covariance using one actual differential action. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 6500000
set_option synthInstance.maxHeartbeats 380000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Set Matrix MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz)
open Burnett.P01
  (exists_projectedChartCutoff inverseHalfDensityCutoff inverseHalfDensityCutoff_tsupport)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [T2Space M]

omit [T2Space M] in
/-- The canonical projection does not change the ordinary original covariant
first-order source on the actual chart, even before taking a limit. -/
theorem receivingRawFirstOrderRow_projected_original
    {J L : Type*} [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (c : AtlasChart M) (n : ℕ) (x : E) (hx : x ∈ c.chart.target)
    (a : J → E → ℝ) (v : J → E) (i : J → JetSlot)
    (b : L → E → ℝ) (j : L → JetSlot) :
    receivingRawFirstOrderRow (fun h y => a h.1 y / 2) (fun h => v h.1) (projectedRowSlot i)
        (fun h y => b h.1 y / 2) (projectedRowSlot j) (receivingRawCovariantJet r B g c n) x =
      receivingRawFirstOrderRow a v i b j (receivingRawCovariantJet r B g c n) x := by
  obtain ⟨η₀, hη₀, hCompact, hηc, V, hV, hXV, _, hOne⟩ :=
    exists_projectedChartCutoff isCompact_singleton c.chart.open_target (singleton_subset_iff.mpr hx)
  let η : D := ⟨η₀, hη₀, hCompact⟩
  let e := inverseHalfDensityCutoff B hB hn c η hηc
  let he := (inverseHalfDensityCutoff_tsupport B hB hn c η hηc).trans hηc
  let W := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c e he n
  let u := receivingRawCovariantJet r B g c n
  have hxV : x ∈ V := hXV (mem_singleton x)
  have hAt (k : JetSlot) (y : E) (hy : y ∈ V) : W k y = u k y := by
    have hU := fixedVolumeCovariantGradient_inverseHalfDensity_apply r B g hB hg hn c η hηc n k y
    change W k y = ((η₀ y : ℝ) : ℂ) * u k y at hU
    simpa only [hOne hy, Pi.one_apply, Complex.ofReal_one, one_mul] using hU
  have hNear (k : JetSlot) : u k =ᶠ[𝓝 x] (W k : E → ℂ) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact (hAt k y hy).symm
  have hDiff (k : JetSlot) : DifferentiableAt ℝ (u k) x :=
    (((W k).smooth ⊤).contDiffAt.differentiableAt (by simp)).congr_of_eventuallyEq (hNear k)
  have hProject (k : JetSlot) :
      (fun y => symmetrizeOrderedJet (fun l => u l y) k) =ᶠ[𝓝 x] u k := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    have hSwapW : W (jetPairSwap k) y = W k y :=
      congrArg (fun z : SchwartzMap E ℂ => z y)
        (fixedVolumeCovariantGradientSchwartz_pairSwap r B g hB hg hn hsB hsG c e he n k)
    have hSwap : u (jetPairSwap k) y = u k y :=
      (hAt _ y hy).symm.trans (hSwapW.trans (hAt _ y hy))
    change (2 : ℂ)⁻¹ * (u k y + u (jetPairSwap k) y) = u k y
    rw [hSwap]
    ring
  exact (receivingRawFirstOrderRow_projected a v i b j u x hDiff).trans
    (receivingRawFirstOrderRow_congr_of_eventuallyEq a v i b j hProject)

variable [MeasurableSpace M] [BorelSpace M]

/-- A single actual differential action on compact symmetric sections supplies
the intrinsic principal symbol. Ordinary local negative-energy convergence of
its unprojected source kills the same original covariance range. -/
theorem original_intrinsic_symmetricJet_kernel_of_actualFirstOrderAction
    {Rows J L : Type} [Fintype Rows] [Fintype J] [Fintype L]
    {Y : M → Type} [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (Q : smoothCompactSymmetricJet M →ₗ[ℂ] (∀ x : M, Y x))
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot)
    (ha : ∀ c s h, ContDiffOn ℝ ∞ (a c s h) c.chart.target)
    (hb₀ : ∀ c s h, ContDiffOn ℝ ∞ (b c s h) c.chart.target)
    (hRepresentation : ∀ (c : AtlasChart M) (x : M) (hc : x ∈ c.chart.source)
      (s : smoothCompactSymmetricJet M),
      coordinates c x hc (Q s x) =
        fun t => receivingRawFirstOrderRow (a c t) (v c t) (i c t) (b c t) (j c t)
          (fun k y => symmetricJetComponent c s k (c.chart.symm y)) (c.chart x))
    (hLocal : ∀ (c : AtlasChart M) (χ : D), tsupport (χ : E → ℝ) ⊆ c.chart.target →
      ∃ F : Rows → ℕ → SchwartzMap E ℂ,
        (∀ s n x, F s n x = ((χ : E → ℝ) x : ℂ) * receivingRawFirstOrderRow
          (a c s) (v c s) (i c s) (b c s) (j c s) (receivingRawCovariantJet r B g c n) x) ∧
        ∀ s, Tendsto (fun n => negativeEnergy (F s n)) atTop (𝓝 0)) :
    ∃ S : ∀ p : Cosphere r, complexSymmetricJet (TangentSpace Model (projection p)) →ₗ[ℂ] Y (projection p),
      (∀ (c : AtlasChart M) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
        (F : complexSymmetricJet (TangentSpace Model (projection p))),
        coordinates c (projection p) hp (S p F) =
          (fun s : Rows => receivingRawFirstOrderSymbol c (fun h y => a c s h.1 y / 2) (fun h => v c s h.1)
            (projectedRowSlot (i c s)) p) *ᵥ
            jetFiberCoordinates (chartTangentBasis c (projection p) hp)
              (F : ComplexCovariantJet (TangentSpace Model (projection p)))) ∧
      ∀ᵐ p ∂A.control, ∀ F : complexSymmetricJet (TangentSpace Model (projection p)),
        S p (intrinsicSymmetricJetCovariance A.density p F) = 0 := by
  let a' (c : AtlasChart M) (t : Rows) (h : J × Fin 2) (y : E) := a c t h.1 y / 2
  let v' (c : AtlasChart M) (t : Rows) (h : J × Fin 2) := v c t h.1
  let i' (c : AtlasChart M) (t : Rows) := projectedRowSlot (i c t)
  let b' (c : AtlasChart M) (t : Rows) (h : L × Fin 2) (y : E) := b c t h.1 y / 2
  let j' (c : AtlasChart M) (t : Rows) := projectedRowSlot (j c t)
  have hAction : HasCompatibleRawFirstOrderActions coordinates a' v' i' b' j' :=
    hasCompatibleRawFirstOrderActions_of_actualSymmetricSectionAction
      (Rows := Rows) (J := J) (L := L) (Y := Y) B hB hnB Q coordinates a v i b j hRepresentation
  have hLocal' (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
      ∃ F : Rows → ℕ → SchwartzMap E ℂ,
        (∀ s n x, F s n x = ((χ : E → ℝ) x : ℂ) * receivingRawFirstOrderRow
          (a' c s) (v' c s) (i' c s) (b' c s) (j' c s) (receivingRawCovariantJet r B g c n) x) ∧
        ∀ s, Tendsto (fun n => negativeEnergy (F s n)) atTop (𝓝 0) := by
    obtain ⟨F, hF, hStrong⟩ := hLocal c χ hχ
    refine ⟨F, ?_, hStrong⟩
    intro s n x
    refine (hF s n x).trans ?_
    by_cases hx : x ∈ c.chart.target
    · exact congrArg (((χ : E → ℝ) x : ℂ) * ·)
        (receivingRawFirstOrderRow_projected_original r B g hB hg hnB hsB hsG c n x hx
          (a c s) (v c s) (i c s) (b c s) (j c s)).symm
    · have hχx : (χ : E → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχ h))
      simp only [hχx, Complex.ofReal_zero, zero_mul]
  exact original_intrinsic_symmetricJet_kernel_of_compatible_firstOrderActions
    (Rows := Rows) (J := J × Fin 2) (L := L × Fin 2) (Y := Y)
    r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA coordinates a' v' i' b' j'
    (fun c t h => (ha c t h.1).div_const 2) (fun c t h => (hb₀ c t h.1).div_const 2) hAction hLocal'

end Burnett.Microlocal.Overlap
