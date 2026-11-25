import Burnett.Analysis.Microlocal.Overlap.UnweightedReceivingFirstOrderRange
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetSymmetricProjection
import Burnett.Analysis.Microlocal.PhysicalChartCover

/-! The arbitrary-chart unweighted sources localize one intrinsic range on a common conull set. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 5200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.CountableAuxiliaryCharts (exists_countable_compactChartInput_cover)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- For one compatible intrinsic symbol with an unweighted local differential
action in each chart, take the countable chart cover internally and localize
the range of the same symmetric jet covariance almost everywhere. -/
theorem original_intrinsic_symmetricJet_kernel_of_unweightedChartSources
    {Rows : Type*} {J L : Type} [Fintype Rows] [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot)
    (ha : ∀ c s h, ContDiffOn ℝ ∞ (a c s h) c.chart.target)
    (hb₀ : ∀ c s h, ContDiffOn ℝ ∞ (b c s h) c.chart.target)
    (hLocal : ∀ (c : AtlasChart M) (χ : D), tsupport (χ : E → ℝ) ⊆ c.chart.target →
      ∃ F : Rows → ℕ → SchwartzMap E ℂ,
        (∀ s n x, F s n x = ((χ : E → ℝ) x : ℂ) * receivingRawFirstOrderRow
          (a c s) (v c s) (i c s) (b c s) (j c s) (receivingRawCovariantJet r B g c n) x) ∧
        ∀ s, Tendsto (fun n => negativeEnergy (F s n)) atTop (𝓝 0))
    (Y : M → Type*) [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (S : ∀ p : Cosphere r, complexSymmetricJet (TangentSpace Model (projection p)) →ₗ[ℂ] Y (projection p))
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (hSymbol : ∀ (c : AtlasChart M) (p : Cosphere r) (hp : projection p ∈ c.chart.source),
      ∀ F : complexSymmetricJet (TangentSpace Model (projection p)),
        coordinates c (projection p) hp (S p F) =
          (fun s : Rows => receivingRawFirstOrderSymbol c (a c s) (v c s) (i c s) p) *ᵥ
            jetFiberCoordinates (chartTangentBasis c (projection p) hp)
              (F : ComplexCovariantJet (TangentSpace Model (projection p)))) :
    ∀ᵐ p ∂A.control, ∀ F : complexSymmetricJet (TangentSpace Model (projection p)),
      S p (intrinsicSymmetricJetCovariance A.density p F) = 0 := by
  by_cases hM : Nonempty M
  swap
  · filter_upwards with p
    exact (hM ⟨projection p⟩).elim
  letI := hM
  obtain ⟨q, _, hCover⟩ := exists_countable_compactChartInput_cover (M := M)
  let c (m : ℕ) := AtlasChart.atPoint (q m).center
  let K (m : ℕ) := (c m).chart.symm '' (q m).ball.closedBall
  let χ (m : ℕ) := (q m).cutoff
  have hBall (m : ℕ) : (q m).ball.closedBall ⊆ (c m).chart.target := (q m).ball_in_chart
  have hK (m : ℕ) : IsCompact (K m) :=
    (isCompact_closedBall _ _).image_of_continuousOn ((c m).chart.continuousOn_symm.mono (hBall m))
  have hKc (m : ℕ) : K m ⊆ (c m).chart.source :=
    image_subset_iff.mpr ((c m).chart.symm_mapsTo.mono_left (hBall m))
  have hχ (m : ℕ) : tsupport (χ m : E → ℝ) ⊆ (c m).chart '' K m := by
    intro x hx
    have hx' := (q m).cutoff_support hx
    exact ⟨(c m).chart.symm x, mem_image_of_mem _ hx', (c m).chart.right_inv (hBall m hx')⟩
  let P (m : ℕ) (p : Cosphere r) : Matrix Rows JetSlot ℂ :=
    fun s => receivingRawFirstOrderSymbol (c m) (a (c m) s) (v (c m) s) (i (c m) s) p
  have hRows (m : ℕ) : ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r (K m)),
      (χ m : E → ℝ) ((c m).chart (projection p)) ≠ 0 → ∀ w : JetSlot → ℂ,
        P m p *ᵥ (atlasJetCovarianceOperator (c m) A.density p *ᵥ w) = 0 := by
    obtain ⟨F, hF, hSmall⟩ := hLocal (c m) (χ m) ((q m).cutoff_support.trans (hBall m))
    apply (original_receiving_covariant_kernel_of_unweightedFirstOrderSources r B g hB hg hsB hsG
      hnB hnG hconv hb hv σ hσ A hA (c m) (K m) (hK m) (hKc m) (χ m) (hχ m)
      (a (c m)) (v (c m)) (i (c m)) (b (c m)) (j (c m)) (ha _) (hb₀ _) F hF hSmall).mono
    intro _ hp hn
    exact (hp hn).2
  have hConull : ∀ᵐ p ∂A.control, ∀ m : ℕ, p ∈ amplitudeCosphereWindow r (K m) →
      (χ m : E → ℝ) ((c m).chart (projection p)) ≠ 0 → ∀ w : JetSlot → ℂ,
        P m p *ᵥ (atlasJetCovarianceOperator (c m) A.density p *ᵥ w) = 0 :=
    ae_all_iff.mpr fun m =>
      (ae_restrict_iff' (measurableSet_amplitudeCosphereWindow r (hK m).isClosed.measurableSet)).mp (hRows m)
  filter_upwards [hConull, hA.2.2.2.2.2] with p hp hData
  intro F
  obtain ⟨m, hm⟩ := mem_iUnion.mp (hCover.symm ▸ mem_univ (projection p))
  have hSource : projection p ∈ (c m).chart.source := hm.1
  have hNonzero : (χ m : E → ℝ) ((c m).chart (projection p)) ≠ 0 := hm.2
  have hpm : projection p ∈ K m := ⟨(c m).chart (projection p),
    (q m).cutoff_support (subset_tsupport _ hNonzero), (c m).chart.left_inv hSource⟩
  let V := TangentSpace Model (projection p)
  let W := jetFiberCoordinates (chartTangentBasis (c m) (projection p) hSource)
  have hRic : HasIntrinsicAmplitudeRicciKernel r B hnB A.density p := hData.2.2
  have hOut : (intrinsicSymmetricJetCovariance A.density p F : ComplexCovariantJet V) =
      intrinsicJetCovarianceEndomorphism A.density p (F : ComplexCovariantJet V) := by
    let T := intrinsicJetCovarianceEndomorphism A.density p (F : ComplexCovariantJet V)
    change (projectComplexSymmetricJet V T : ComplexCovariantJet V) = T
    exact coe_projectComplexSymmetricJet_of_mem T (intrinsicJetCovarianceEndomorphism_mem_symmetric hRic _)
  have hW : W (intrinsicSymmetricJetCovariance A.density p F : ComplexCovariantJet V) =
      atlasJetCovarianceOperator (c m) A.density p *ᵥ W (F : ComplexCovariantJet V) :=
    (congrArg W hOut).trans
      (intrinsicJetCovarianceEndomorphism_coordinates A.density p (c m) hSource (F : ComplexCovariantJet V))
  apply (coordinates (c m) (projection p) hSource).injective
  calc
    _ = P m p *ᵥ W (intrinsicSymmetricJetCovariance A.density p F : ComplexCovariantJet V) :=
      hSymbol (c m) p hSource (intrinsicSymmetricJetCovariance A.density p F)
    _ = P m p *ᵥ (atlasJetCovarianceOperator (c m) A.density p *ᵥ W (F : ComplexCovariantJet V)) :=
      congrArg (fun z => P m p *ᵥ z) hW
    _ = 0 := hp m hpm hNonzero (W (F : ComplexCovariantJet V))
    _ = _ := (coordinates (c m) (projection p) hSource).map_zero.symm

end Burnett.Microlocal.Overlap
