import Burnett.Analysis.Microlocal.Overlap.AssembledRicciMoments
import Burnett.Analysis.Microlocal.Overlap.GlobalCosphereRicciMoments
import Burnett.Geometry.Cotangent.CosphereFixedChartNaturality

/-! The original subsequence gives full tensor Einstein moments on its unit cosphere. -/

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open ContravariantTensor IntrinsicScalarEinstein UnitNullCompactness
open Burnett.Analysis.ScalarCurvatureFromMoments
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian measurableEmbedding_coe FixedChartNaturality fixedChartNaturality)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- Einstein moments tested by every actual smooth compactly supported symmetric tensor. -/
def HasCosphereEinsteinMoments (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (Cosphere r)) : Prop :=
  ∀ Q : ContravariantTwoTensor M, IsTensorTest Q →
    Integrable (einsteinPair B hn Q) (ManifoldVolume.geometricMeasure B) ∧
    Integrable (fun p : Cosphere r => intrinsicTensorPhase Q p.val) μ ∧
    (∫ x, einsteinPair B hn Q x ∂ManifoldVolume.geometricMeasure B) =
      ∫ p : Cosphere r, intrinsicTensorPhase Q p.val ∂μ

/-- The same glued measure gives all Einstein tests after tracing its Ricci
moments, with the integral taken directly on the actual unit cosphere. -/
theorem exists_originalVacuum_cosphereEinsteinMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ μr : Measure (Cosphere r),
      IsLocallyFiniteMeasure μr ∧ μr.Regular ∧
      (∀ K : Set M, IsCompact K → μr (projection ⁻¹' K) < ⊤) ∧
      μr {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
      HasCosphereEinsteinMoments r B hSig.isNondegenerate μr ∧
      (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧
      FixedChartNaturality μr := by
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨t, ht, q, hCover, ν, hf, hRep, μ, hLoc, hReg, hNull, hFinite, μr, hmap,
      hLocR, hRegR, hFiniteR, hNullR, hChart⟩ :=
      exists_originalVacuum_physicalMeasure_on_cosphere_and_representedChartMoments
        r B g hB hg hSig hsG hnG hconv hb hv s hs
    have hCoverage : ⋃ i, (q i).nonzeroLocus = univ := by
      apply eq_univ_of_forall
      intro x
      have hx : x ∈ ⋃ i, (q i).cutoffLocusAbove (1 / 2) := hCover.symm ▸ mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, (q i).cutoffLocusAbove_subset_nonzeroLocus (by norm_num) hi⟩
    let ambientMap := μr.map (Subtype.val : Cosphere r → CotangentBundle M)
    have hRicci : HasRicciMoments B ambientMap := by
      refine hasRicciMoments_of_nonzero_chartMoments B hB hSig.isSymmetric hSig.isNondegenerate
        q hCoverage ambientMap ?_
      intro i ψ hψ a b
      exact (hChart (q i) (ν i) (hf i) (hRep i).1).2 ψ hψ a b
    have hMapNull : ambientMap (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 := by
      change (μr.map (Subtype.val : Cosphere r → CotangentBundle M)) _ = _
      rw [hmap]
      exact hNull
    obtain ⟨hScalar, hEinstein⟩ := scalarFlat_and_EinsteinMoments_of_null_RicciMoments
      r B hB hSig.isSymmetric hSig.isNondegenerate ambientMap hMapNull hRicci
    refine ⟨t, ht, μr, hLocR, hRegR, hFiniteR, hNullR, ?_, hScalar, fixedChartNaturality μr⟩
    intro Q hQ
    obtain ⟨hIntBase, hIntPhase, hEq⟩ := hEinstein Q hQ
    let e : Cosphere r → CotangentBundle M := Subtype.val
    have he : MeasurableEmbedding e := measurableEmbedding_coe r
    change Integrable (intrinsicTensorPhase Q) (μr.map e) at hIntPhase
    have hInt : Integrable (intrinsicTensorPhase Q ∘ e) μr := he.integrable_map_iff.mp hIntPhase
    have hPush : (∫ p, intrinsicTensorPhase Q p ∂μr.map e) =
        ∫ p, intrinsicTensorPhase Q (e p) ∂μr := he.integral_map (intrinsicTensorPhase Q)
    exact ⟨hIntBase, hInt, hEq.trans hPush⟩
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨id, strictMono_id, 0, inferInstance, inferInstance, by simp, by simp, ?_, ?_, fixedChartNaturality 0⟩
    · intro Q _
      rw [(ManifoldVolume.geometricMeasure B).eq_zero_of_isEmpty]
      simp
    · exact isEmptyElim

end Burnett.Microlocal.Overlap
