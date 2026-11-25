import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalCovariantCutoff
import Burnett.Analysis.Microlocal.Overlap.OriginalSymmetricJetSeparatedGlobalPairings

/-! Each true proper-tail term vanishes on the original unrefined sequence. -/
set_option autoImplicit false
set_option maxRecDepth 4650
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 410000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Topology BigOperators

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

omit [T2Space M] in
/-- The exact tail cutoff is the product with the difference of the two
physical cutoffs. The covariant derivative is the same in every term. -/
theorem scale_originalCovariantGlobalCutoffTest_sub
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (β ρ η : M → ℝ)
    (hβ : ContMDiff Model 𝓘(ℝ) ∞ β) (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ) (hη : ContMDiff Model 𝓘(ℝ) ∞ η)
    (hβc : HasCompactSupport β) (hρc : HasCompactSupport ρ) (hηc : HasCompactSupport η) (n : ℕ) :
    scaleCompactSymmetricJet β hβ
        (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc n +
          (-1 : ℂ) • originalCovariantGlobalCutoffTest r B g hB hg hsB hsG η hη hηc n) =
      originalCovariantGlobalCutoffTest r B g hB hg hsB hsG (β * (ρ - η))
        (hβ.mul (hρ.sub hη)) hβc.mul_right n := by
  apply Subtype.ext
  funext p
  simp only [scaleCompactSymmetricJet_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, originalCovariantGlobalCutoffTest, globalCutoffSymmetricJetTest_apply,
    Pi.mul_apply, Pi.sub_apply, Complex.ofReal_mul, Complex.ofReal_sub]
  rw [smul_smul, ← add_smul, smul_smul]
  congr 1
  ring

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- A single true separated tail uses the same global form and the same
original sequence, in the two charts containing the physical supports. -/
theorem tendsto_symmetricJetGlobalForm_scale_originalDifference
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (Q : SymmetricJetGlobalForm M) (K : SymmetricJetPairingKernel M)
    (hQ : HasSeparatedSymmetricJetKernel (ManifoldVolume.geometricMeasure B) Q K)
    (c d : AtlasChart M) (S T : Set M) (hS : IsCompact S) (hT : IsCompact T) (hST : Disjoint S T)
    (hSc : S ⊆ c.chart.source) (hTd : T ⊆ d.chart.source)
    (hK : ∀ i j, ContinuousOn (uncurry (symmetricJetKernelEntry K c d i j)) (S ×ˢ T))
    (α β ρ η : M → ℝ)
    (hα : ContMDiff Model 𝓘(ℝ) ∞ α) (hβ : ContMDiff Model 𝓘(ℝ) ∞ β)
    (hρ : ContMDiff Model 𝓘(ℝ) ∞ ρ) (hη : ContMDiff Model 𝓘(ℝ) ∞ η)
    (hαc : HasCompactSupport α) (hβc : HasCompactSupport β)
    (hρc : HasCompactSupport ρ) (hηc : HasCompactSupport η)
    (hαS : tsupport α ⊆ S) (hβT : tsupport β ⊆ T) :
    Tendsto (fun n =>
      Q (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc n)
        (scaleCompactSymmetricJet β hβ
          (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG ρ hρ hρc n +
            (-1 : ℂ) • originalCovariantGlobalCutoffTest r B g hB hg hsB hsG η hη hηc n)))
      atTop (𝓝 0) := by
  let θ := β * (ρ - η)
  have hθ : ContMDiff Model 𝓘(ℝ) ∞ θ := hβ.mul (hρ.sub hη)
  have hθc : HasCompactSupport θ := hβc.mul_right
  have hθT : tsupport θ ⊆ T := tsupport_mul_subset_left.trans hβT
  obtain ⟨χ, hχ, hχEq⟩ := exists_chartCutoff_of_globalScalar c α hα hαc (hαS.trans hSc)
  obtain ⟨ξ, hξ, hξEq⟩ := exists_chartCutoff_of_globalScalar d θ hθ hθc (hθT.trans hTd)
  have hχS : tsupport (χ : E → ℝ) ⊆ c.chart '' S := hχ.trans (image_mono hαS)
  have hξT : tsupport (ξ : E → ℝ) ⊆ d.chart '' T := hξ.trans (image_mono hθT)
  have hχc := hχS.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hSc))
  have hξd := hξT.trans (image_subset_iff.mpr (d.chart.mapsTo.mono_left hTd))
  apply (tendsto_symmetricJetGlobalForm_originalSeparated r B g hB hg hn hsB hsG hconv hb Q K hQ
    c d S T hS hT hST hSc hTd hK χ ξ hχS hξT).congr
  intro n
  rw [scale_originalCovariantGlobalCutoffTest_sub r B g hB hg hsB hsG β ρ η hβ hρ hη hβc hρc hηc n]
  rw [originalCovariantGlobalCutoffTest_eq_chartTest r B g hB hg hn hsB hsG c α hα hαc
      (hαS.trans hSc) χ hχc hχEq n,
    originalCovariantGlobalCutoffTest_eq_chartTest r B g hB hg hn hsB hsG d θ hθ hθc
      (hθT.trans hTd) ξ hξd hξEq n]

end Burnett.Microlocal.Overlap
