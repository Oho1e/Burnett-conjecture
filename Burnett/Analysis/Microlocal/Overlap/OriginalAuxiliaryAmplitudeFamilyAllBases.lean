import Burnett.Analysis.Microlocal.Overlap.OriginalAuxiliaryAmplitudeFamily

/-! The auxiliary-change conclusion also includes the empty manifold. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 2350000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Geometry.CotangentAngularExtension (cotangentNorm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeFiber)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The full measure identities on a fixed subsequence for all receiving
auxiliary metrics. On an empty base all measures are zero. -/
theorem exists_originalVacuum_intrinsicAmplitude_weightedPushforward_allAuxiliaryMetrics
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ StrictMono (s ∘ t) ∧
      ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        ∀ r' : Metric (M := M),
          ∃ A' : IntrinsicAmplitudeCovariance r', ∃ μ' : Measure (Cosphere r'),
            HasOriginalIntrinsicAmplitude r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
            HasOriginalReceivingLocalClassicalPairings r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
            HasIntrinsicPhysicalContraction r' B hSig.isNondegenerate A' μ' ∧
            HasIntrinsicAmplitudeWeightedPushforward r r' A A' ∧
            (∀ (L : ∀ p : Cosphere r', AmplitudeFiber (projection p) →ₗ[ℝ] ℂ),
              Integrable (fun p => L p (A'.density p)) A'.control →
              A'.control.withDensityᵥ (fun p => L p (A'.density p)) =
                (A.control.withDensityᵥ (fun p => (cotangentNorm r' p.val ^ 2) •
                  pullbackAmplitudeFiberTest r r' L p (A.density p))).map
                    (renormalizeUnitCosphere r r')) ∧
            μ' = (μ.withDensity (fun p => ENNReal.ofReal (cotangentNorm r' p.val ^ 2))).map
              (renormalizeUnitCosphere r r') := by
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨t, ht, hσ, _, _, _, _, _, A, μ, hA, hPair, hPhysical, hFamily⟩ :=
      exists_originalVacuum_intrinsicAmplitude_weightedPushforward_allAuxiliaryMetrics_sameWitnesses
        r B g hB hg hSig hsG hnG hconv hb hv s hs
    exact ⟨t, ht, hσ, A, μ, hA, hPair, hPhysical, hFamily⟩
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    let zeroAmplitude (aux : Metric (M := M)) : IntrinsicAmplitudeCovariance aux := ⟨0, fun _ => 0⟩
    have hσ : StrictMono (s ∘ id) := hs.comp strictMono_id
    have emptyOriginal (aux : Metric (M := M))
        (hConv : LocallyUniformlyConverges aux g B) (hBound : AuxiliaryAdmissibility.CompactDhBound aux B g) :
        HasOriginalIntrinsicAmplitude aux B g hB hg hSig.isNondegenerate (s ∘ id) (zeroAmplitude aux) ∧
          HasOriginalReceivingLocalClassicalPairings aux B g hB hg hSig.isNondegenerate (s ∘ id)
            (zeroAmplitude aux) ∧
          HasIntrinsicPhysicalContraction aux B hSig.isNondegenerate (zeroAmplitude aux) 0 := by
      letI : IsEmpty (Cosphere aux) := ⟨fun p => isEmptyElim (projection p)⟩
      have hA : HasOriginalIntrinsicAmplitude aux B g hB hg hSig.isNondegenerate (s ∘ id)
          (zeroAmplitude aux) := by
        refine ⟨fun h => (hM h).elim, ?_, ?_, by simp [zeroAmplitude], ?_, by simp [zeroAmplitude]⟩
        · change IsLocallyFiniteMeasure (0 : Measure (Cosphere aux))
          infer_instance
        · change (0 : Measure (Cosphere aux)).Regular
          infer_instance
        · intro q
          exact (hM ⟨q.center⟩).elim
      refine ⟨hA, hasOriginalReceivingLocalClassicalPairings_of_intrinsicAmplitude aux B g hB hg
        hSig.isSymmetric hsG hSig.isNondegenerate hnG hConv hBound hv (s ∘ id) hσ (zeroAmplitude aux) hA, ?_⟩
      unfold HasIntrinsicPhysicalContraction
      have hZ : {p : Cosphere aux | hamiltonian B hSig.isNondegenerate p = 0} = ∅ := Set.eq_empty_of_isEmpty _
      simp [zeroAmplitude, hZ]
    obtain ⟨hA, hPair, hPhysical⟩ := emptyOriginal r hconv hb
    refine ⟨id, strictMono_id, hσ, zeroAmplitude r, 0, hA, hPair, hPhysical, ?_⟩
    intro r'
    have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
    have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
    obtain ⟨hA', hPair', hPhysical'⟩ := emptyOriginal r' hconv' hb'
    have hWeighted : HasIntrinsicAmplitudeWeightedPushforward r r' (zeroAmplitude r) (zeroAmplitude r') := by
      intro L
      simp [zeroAmplitude]
    refine ⟨zeroAmplitude r', 0, hA', hPair', hPhysical', hWeighted,
      intrinsicAmplitude_testMeasure_changeAuxiliary r r' _ _ hWeighted, ?_⟩
    simp

end Burnett.Microlocal.Overlap
