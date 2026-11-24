import Burnett.Analysis.BaseMarginal.IntrinsicAngularTestedMoments
import Burnett.Analysis.BaseMarginal.IntrinsicFrameTensorTests

/-! Simultaneous components of the conditional moment in one actual chart frame. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 3600000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory ProbabilityTheory Module Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open scoped ContDiff Manifold ProbabilityTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem einsteinPair_supportedFrameTensorTest_at_plateau
    (B : Field (M := M)) (hn : IsNondegenerate B) (c x : M) (φ : M → ℝ) (i j : Index)
    (hx : x ∈ (chartAt CoordinateSpace c).source) (hφ : φ x = 1) :
    let b := tensorTangentBasis c x hx
    einsteinPair B hn (supportedFrameTensorTest c φ i j) x =
      (intrinsicEinstein B hn x (b i) (b j) + intrinsicEinstein B hn x (b j) (b i)) / 2 := by
  intro b
  let G := intrinsicEinstein B hn x
  rw [einsteinPair, supportedFrameTensorTest_eq_at_plateau c x φ i j hx hφ, contractAt_eq_sum x b]
  let w (i j a d : Index) := b.dualBasis a (b i) * b.dualBasis d (b j) * G (b a) (b d)
  have hW (i j : Index) : (∑ a, ∑ d, w i j a d) = G (b i) (b j) := by
    calc
      _ = ∑ d, w i j i d := by
        apply Finset.sum_eq_single i
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro d _
          simp [w, Ne.symm ha]
        · simp
      _ = w i j i j := by
        apply Finset.sum_eq_single j
        · intro d _ hd
          simp [w, Ne.symm hd]
        · simp
      _ = _ := by simp [w]
  calc
    _ = ((∑ a, ∑ d, w i j a d) + ∑ a, ∑ d, w j i a d) / 2 := by
      simp only [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      rw [symmetricTangentDyad_apply]
      dsimp only [w, G]
      ring
    _ = _ := by rw [hW, hW]

theorem intrinsicTensorPhase_supportedFrameTensorTest {r : Metric (M := M)}
    (c : M) (φ : M → ℝ) (i j : Index) (p : Cosphere r) :
    intrinsicTensorPhase (supportedFrameTensorTest c φ i j) p.val =
      p.val.2 (supportedFrameVector c φ i (projection p)) * p.val.2 (supportedFrameVector c φ j (projection p)) := by
  let a := p.val.2 (supportedFrameVector c φ i (projection p))
  let b := p.val.2 (supportedFrameVector c φ j (projection p))
  change (a * b + b * a) / 2 = a * b
  ring

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- One common full measure set carries every component in this chart on the plateau. -/
theorem ae_intrinsicAngularFrameMoments (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (hMom : HasCosphereEinsteinMoments r B hn μ) (κ : Kernel M (Cosphere r)) [IsSFiniteKernel κ]
    (hLaw : ManifoldVolume.geometricMeasure B ⊗ₘ κ = μ.map (fun p => (projection p, p)))
    (c : M) (φ : M → ℝ) (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hC : HasCompactSupport φ)
    (hSupp : tsupport φ ⊆ (chartAt CoordinateSpace c).source) :
    ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, ∀ i j : Index,
      Integrable (fun p : Cosphere r => p.val.2 (supportedFrameVector c φ i (projection p)) *
        p.val.2 (supportedFrameVector c φ j (projection p))) (κ x) ∧
      ∀ (hx : x ∈ (chartAt CoordinateSpace c).source), φ x = 1 →
          let b := tensorTangentBasis c x hx
          (intrinsicEinstein B hn x (b i) (b j) + intrinsicEinstein B hn x (b j) (b i)) / 2 =
            ∫ p : Cosphere r, p.val.2 (supportedFrameVector c φ i (projection p)) *
              p.val.2 (supportedFrameVector c φ j (projection p)) ∂κ x := by
  let V := ManifoldVolume.geometricMeasure B
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  letI : IsLocallyFiniteMeasure V := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  have hπ : Measurable (projection (r := r)) := (UnitCosphere.continuous_projection r).measurable
  have hCμ : κ ∘ₘ V = μ := by
    rw [← Measure.snd_compProd, hLaw, Measure.snd_map_prodMk hπ]
    exact Measure.map_id
  have hFixed (i j : Index) := ae_einsteinPair_eq_angularKernel_moment r B hB hn μ hMom κ hLaw
    (supportedFrameTensorTest c φ i j) (isTensorTest_supportedFrameTensorTest c φ i j hφ hC hSupp)
  have hIntegrable (i j : Index) :
      ∀ᵐ x ∂V, Integrable (fun p : Cosphere r => intrinsicTensorPhase (supportedFrameTensorTest c φ i j) p.val)
        (κ x) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [hCμ]
    exact (hMom _ (isTensorTest_supportedFrameTensorTest c φ i j hφ hC hSupp)).2.1
  have hAllMoments := ae_all_iff.mpr (fun i : Index => ae_all_iff.mpr (hFixed i))
  have hAllIntegrable := ae_all_iff.mpr (fun i : Index => ae_all_iff.mpr (hIntegrable i))
  filter_upwards [hAllMoments, hAllIntegrable] with x hx hi i j
  refine ⟨?_, fun hxChart hPlateau => ?_⟩
  · simpa only [intrinsicTensorPhase_supportedFrameTensorTest] using hi i j
  · simpa only [einsteinPair_supportedFrameTensorTest_at_plateau B hn c x φ i j hxChart hPlateau,
      intrinsicTensorPhase_supportedFrameTensorTest] using hx i j

end Burnett.F08.IntrinsicBaseMarginal
