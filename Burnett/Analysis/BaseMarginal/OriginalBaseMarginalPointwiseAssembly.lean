import Burnett.Analysis.BaseMarginal.IntrinsicAngularPointwiseMoments
import Burnett.Analysis.BaseMarginal.IntrinsicVacuumMarginal
import Burnett.Analysis.BaseMarginal.OriginalEinsteinSymmetry
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude

/-! Base marginal, conditional Einstein tensor, and vacuum vanishing for one original physical measure. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory ProbabilityTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open IntrinsicScalarEinstein Burnett.Microlocal.Overlap
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open scoped ContDiff Manifold ProbabilityTheory ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The pointwise angular identities and the base marginal use the physical contraction
of the same original covariance on one refinement. -/
theorem exists_originalVacuum_baseMarginal_and_angularFiberMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    let V := ManifoldVolume.geometricMeasure B
    let e := auxiliaryEinsteinDensity r B hSig.isNondegenerate
    ContMDiff Model 𝓘(ℝ) ∞ e ∧ (∀ x, 0 ≤ e x) ∧
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        let ρ := μ.map (fun p => (projection p, p))
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        μ.map projection = V.withDensity (fun x => ENNReal.ofReal (e x)) ∧ μ.map projection ≪ V ∧
        (∀ U : Set M, IsOpen U → (∀ x ∈ U, ∀ u v : TangentSpace Model x,
          IntrinsicRicciTrace.ricci B x u v = 0) → μ (projection ⁻¹' U) = 0) ∧
        ∃ κ : Kernel M (Cosphere r), IsSFiniteKernel κ ∧ V ⊗ₘ κ = ρ ∧
          (∀ x, IsFiniteMeasure (κ x)) ∧
          (∀ᵐ x ∂V, κ x univ = ENNReal.ofReal (e x) ∧
            κ x {p | projection p ≠ x ∨ hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
            (e x = 0 → κ x = 0) ∧
            ∀ u v : TangentSpace Model x, Integrable (fiberQuadraticPhase x u v) (κ x) ∧
              intrinsicEinstein B hSig.isNondegenerate x u v = ∫ p, fiberQuadraticPhase x u v p ∂κ x) ∧
          (∀ U : Set (Cosphere r), MeasurableSet U → μ U = ∫⁻ x, κ x U ∂V) ∧
          ∀ κ' : Kernel M (Cosphere r), (∀ S : Set (M × Cosphere r), MeasurableSet S →
            ρ S = ∫⁻ x, κ' x (Prod.mk x ⁻¹' S) ∂V) → κ' =ᵐ[V] κ := by
  intro V e
  let hn := hSig.isNondegenerate
  let hSym := hSig.isSymmetric
  obtain ⟨t, ht, A, μ, hA, hPhysical, hLoc, hReg, hFin, hNull, hMom, hScal, _⟩ :=
    exists_originalVacuum_intrinsicAmplitude_and_cosphereEinsteinMoments r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hMarg := auxiliaryEinsteinDensity_baseMarginal r B hB hSym hn μ hFin hMom
  have hSymm := intrinsicEinstein_isSymm_of_originalVacuum r B g hB hg hSym hsG hn hnG hconv hb hv
  obtain ⟨κ, hk, hLaw, hKFin, hSupport, hRec, hUnique⟩ :=
    exists_original_angularDisintegration r B hB hSym hn μ hFin hNull hMom
  letI : IsSFiniteKernel κ := hk
  have hFiber : ∀ᵐ x ∂V, κ x {p | projection p ≠ x} = 0 :=
    hSupport.mono fun x h => measure_mono_null (fun p hp => Or.inl hp) h.2
  have hPointwise := ae_intrinsicEinstein_eq_angularFiberMoment r B hB hn hSymm μ hMom κ hLaw hFiber
  refine ⟨contMDiff_auxiliaryEinsteinDensity r B hB hSym hn,
    auxiliaryEinsteinDensity_nonneg_of_moments r B hB hSym hn μ hMom,
    t, ht, A, μ, hA, hPhysical, hLoc, hReg, hFin, hNull, hMom, hMarg,
    physicalMarginal_absolutelyContinuous r B hn μ hMarg,
    physicalMeasure_zero_over_vacuumOpen r B hn μ hMarg hScal,
    κ, hk, hLaw, hKFin, ?_, hRec, hUnique⟩
  filter_upwards [hSupport, hPointwise] with x h hPoint
  refine ⟨h.1, h.2, fun hx => Measure.measure_univ_eq_zero.mp ?_, hPoint⟩
  calc
    κ x univ = ENNReal.ofReal (e x) := h.1
    _ = 0 := by rw [hx, ENNReal.ofReal_zero]

end Burnett.F08.IntrinsicBaseMarginal
