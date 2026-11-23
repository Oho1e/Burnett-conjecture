import Burnett.Analysis.Microlocal.OriginalGradientInputs
import Burnett.Analysis.Microlocal.OriginalRicciRowSource
import Burnett.Analysis.Sobolev.SchwartzHminusDual
import Burnett.Geometry.IntrinsicRicciTrace

/-!
# Strong localization of the original vacuum Ricci rows
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace Burnett.Microlocal.RicciRemainder

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldMetricSequence
open Burnett.Microlocal.RicciRow Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.GeometricNegativeEnergy
open Burnett.X02.SobolevTestJet (D)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The assembled Schwartz differential row is the complexification of
the exact Ricci source and cutoff remainder on the original metric sequence. -/
theorem chartFirstOrderRow_eq_complexSource (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0) (c : M)
    (χ θ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ1 : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (b d : Index) (n : ℕ) (hS : ContDiff ℝ ∞ (chartRowSource g0 (g n) c χ θ b d))
    (hC : HasCompactSupport (chartRowSource g0 (g n) c χ θ b d)) :
    chartFirstOrderRow g0 g h0 hg hn0 c χ θ hχ hθ b d n =
      complexSource (chartRowSource g0 (g n) c χ θ b d) hS hC := by
  ext x
  rw [chartFirstOrderRow_apply g0 g h0 hg hn0 c χ θ hχ hθ hθ1 b d n x]
  apply congrArg Complex.ofReal
  let G := backgroundInverse g0 c
  let W := chartRawPerturbationJet g0 (g n) c
  have hRaw := localizedSum_eq_principal_add_cutoff G W χ θ (chartAt CoordinateSpace c).open_target
    hχ hθ1 (chartRawPerturbationJet_smoothOn g0 (g n) h0 (hg n) c) x b d
  exact hRaw.symm.trans
    (chartLocalizedSum_eq_linearizedRicci_add_error g0 (g n) h0 (hg n) hn0 c χ θ hχ hθ1 x b d)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

set_option maxHeartbeats 900000 in
/-- The actual Schwartz differential row on the localized coordinate gradients
has Fourier negative energy tending to zero along the full original sequence. -/
theorem chartFirstOrderRow_negativeEnergy_tendsto_zero_of_original (r : Metric (M := M))
    (g0 : Field (M := M)) (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
    (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (χ θ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ1 : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (b d : Index) :
    Tendsto (fun n => negativeEnergy (chartFirstOrderRow g0 g h0 hg hn0 c χ θ hχ hθ b d n)) atTop (𝓝 0) := by
  obtain ⟨hS, hC, hT⟩ :=
    exists_chartRowSource_strong_zero_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac χ θ hχ hθ b d
  have hE := Burnett.Microlocal.HminusReverse.negativeEnergy_tendsto_zero_of_sourceFunctional_tendsto_zero hS hC hT
  refine hE.congr (fun n => congrArg negativeEnergy ?_)
  exact (chartFirstOrderRow_eq_complexSource g0 g h0 hg hn0 c χ θ hχ hθ hθ1 b d n (hS n) (hC n)).symm

end Burnett.Microlocal.RicciRemainder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 900000

noncomputable section

namespace Burnett.Microlocal.RicciRemainder

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldMetricSequence
open Burnett.Microlocal.RicciRow Burnett.Microlocal.BesselLocalization
open Burnett.F05.OriginalCoordinateCurl
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Fourier
open Burnett.X02.SobolevTestJet (D)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def chartRicciPrincipal (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0) (c : M)
    (χ θ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (b d : Index) (n : ℕ) : ComplexL2 CoordinateSpace :=
  rowPrincipal (chartRicciCoefficient g0 h0 hn0 c θ hθ) (ricciRowDirectionVector d) (termInput b d)
    (originalGradientSchwartz g0 g h0 hg c χ hχ n)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Every actual Ricci principal row tends strongly to zero on the same
localized raw gradients as the curl rows. This is along the original sequence. -/
theorem chartRicciPrincipal_tendsto_zero_of_original (r : Metric (M := M))
    (g0 : Field (M := M)) (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
    (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (χ θ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ1 : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (b d : Index) :
    Tendsto (chartRicciPrincipal g0 g h0 hg hn0 c χ θ hχ hθ b d) atTop (𝓝 0) := by
  obtain ⟨f, hS, hF, χ0, hχ0, B, _, hB, ht, _, _, hSchwartz, _⟩ :=
    exists_originalGradient_sourceSchwartz_inputs r g0 g h0 hg hn0 hconv hb c χ hχ θ hθ1
  let a := chartRicciCoefficient g0 h0 hn0 c θ hθ
  let v := ricciRowDirectionVector d
  let i := termInput b d
  let z := (Fin.elim0 : Fin 0 → D)
  let j := (Fin.elim0 : Fin 0 → JetIndex)
  have he0 := chartFirstOrderRow_negativeEnergy_tendsto_zero_of_original r g0 g h0 hg hs0 hs
    hn0 hn hconv hb c hVac χ θ hχ hθ hθ1 b d
  have he : Tendsto (fun n => negativeEnergy
      (firstOrderRow a v i z j (fun k => sourceSchwartz (hS n k) χ0 (hχ0 n k)))) atTop (𝓝 0) := by
    refine he0.congr (fun n => ?_)
    rw [hSchwartz n]
    rfl
  have hp := rowPrincipal_tendsto_zero_of_negativeEnergy_tendsto_zero a v i z j f hS hF χ0 hχ0 B hB ht he
  refine hp.congr (fun n => ?_)
  rw [hSchwartz n]
  rfl

/-- In the paper's Hausdorff manifold, the same conclusion follows from
the intrinsic vacuum equations of the original metrics. -/
theorem chartRicciPrincipal_tendsto_zero_of_intrinsicVacuum [T2Space M] (r : Metric (M := M))
    (g0 : Field (M := M)) (g : ℕ → Field (M := M)) (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
    (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g0)
    (hb : ∀ S : Set M, IsCompact S → ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
        ((Burnett.Geometry.ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal A)
    (c : M) (hv : ∀ n, Burnett.Geometry.IntrinsicRicciTrace.IsVacuum (g n))
    (χ θ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ : tsupport (θ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hθ1 : ∀ x ∈ tsupport (χ : CoordinateSpace → ℝ), (θ : CoordinateSpace → ℝ) x = 1)
    (b d : Index) :
    Tendsto (chartRicciPrincipal g0 g h0 hg hn0 c χ θ hχ hθ b d) atTop (𝓝 0) :=
  chartRicciPrincipal_tendsto_zero_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c
    (Burnett.Geometry.IntrinsicRicciTrace.sequence_coordinateVacuum_of_intrinsic g hg hs hn hv c)
    χ θ hχ hθ hθ1 b d

end Burnett.Microlocal.RicciRemainder
