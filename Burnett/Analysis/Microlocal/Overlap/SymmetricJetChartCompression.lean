import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSourceReplacement
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetPairingKernel
import Burnett.Analysis.Microlocal.Overlap.FirstOrderCutoffCommutator

/-! Actual linear chart lifts of compact smooth symmetric jet sections. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 5100000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Function MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (coeffMul_tsupport_subset_real)
open Burnett.Microlocal.BesselLocalization (coeffMul)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped BigOperators ContDiff InnerProduct Manifold

open private coeffMul_apply from Burnett.Analysis.Microlocal.Overlap.FirstOrderCutoffCommutator

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Lift a compactly multiplied ordered array and apply the true symmetric
fiber projection. The target is the genuine smooth compact section module. -/
def compactSymmetricJetChartTestLinear (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    (JetSlot → SchwartzMap E ℂ) →ₗ[ℂ] smoothCompactSymmetricJet M := by
  let f (u : JetSlot → SchwartzMap E ℂ) (i : JetSlot) : E → ℂ := coeffMul χ (u i)
  let lift (u : JetSlot → SchwartzMap E ℂ) : smoothCompactSymmetricJet M :=
    compactSymmetricJetChartTest B hB hn c (f u) (fun i => (coeffMul χ (u i)).smooth ⊤)
      (tsupport (χ : E → ℝ)) (test_compactSupport χ) hχ
      (fun i => (subset_tsupport _).trans (coeffMul_tsupport_subset_real χ (u i)))
  refine { toFun := lift, map_add' := ?_, map_smul' := ?_ }
  · intro u v
    apply Subtype.ext
    funext x
    change symmetricJetChartLift B c (f (u + v)) x =
      symmetricJetChartLift B c (f u) x + symmetricJetChartLift B c (f v) x
    by_cases hx : x ∈ c.chart.source
    · simp only [symmetricJetChartLift, dif_pos hx]
      have hArr :
          (fun i => receivingScalarPhysicalLift B c (f (u + v) i) x) =
            (fun i => receivingScalarPhysicalLift B c (f u i) x) +
              (fun i => receivingScalarPhysicalLift B c (f v i) x) := by
        funext i
        simp only [receivingScalarPhysicalLift, indicator_of_mem hx, f, Pi.add_apply, coeffMul_apply,
          SchwartzMap.add_apply, mul_add]
      rw [hArr, map_add, map_add]
    · simp only [symmetricJetChartLift, dif_neg hx, add_zero]
  · intro z u
    apply Subtype.ext
    funext x
    change symmetricJetChartLift B c (f (z • u)) x = z • symmetricJetChartLift B c (f u) x
    by_cases hx : x ∈ c.chart.source
    · simp only [symmetricJetChartLift, dif_pos hx]
      have hArr :
          (fun i => receivingScalarPhysicalLift B c (f (z • u) i) x) =
            z • (fun i => receivingScalarPhysicalLift B c (f u i) x) := by
        funext i
        simp only [receivingScalarPhysicalLift, indicator_of_mem hx, f, Pi.smul_apply, coeffMul_apply,
          SchwartzMap.smul_apply, smul_eq_mul]
        ring
      rw [hArr, map_smul, map_smul]
    · simp only [symmetricJetChartLift, dif_neg hx, smul_zero]

end Burnett.Microlocal.Overlap
