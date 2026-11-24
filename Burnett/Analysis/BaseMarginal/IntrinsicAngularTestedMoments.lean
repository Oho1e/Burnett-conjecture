import Burnett.Analysis.BaseMarginal.IntrinsicAngularDisintegration
import Burnett.Analysis.BaseMarginal.IntrinsicSmoothDensityTests

/-! The actual disintegration gives the tested Einstein moments almost everywhere. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set MeasureTheory Filter ProbabilityTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open scoped ContDiff Manifold ENNReal ProbabilityTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem isTensorTest_scalar_mul (Q : ContravariantTwoTensor M) (hQ : IsTensorTest Q)
    (φ : M → ℝ) (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hC : HasCompactSupport φ) :
    IsTensorTest (fun x => φ x • Q x) := by
  refine ⟨fun x => ⟨fun u v => congrArg (φ x * ·) ((hQ.1 x).eq u v)⟩, ?_, ?_⟩
  · apply hC.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    exact fun h => hx (by simp [h])
  · intro c i j
    let e := chartAt CoordinateSpace c
    have hφc : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target :=
      (hφ.contMDiffOn.comp contMDiffOn_chart_symm e.symm.mapsTo).contDiffOn
    exact hφc.mul (hQ.2.2 c i j)

private theorem einsteinPair_scalar_mul (B : Field (M := M)) (hn : IsNondegenerate B)
    (Q : ContravariantTwoTensor M) (φ : M → ℝ) (x : M) :
    einsteinPair B hn (fun y => φ y • Q y) x = φ x * einsteinPair B hn Q x := by
  let b := tensorTangentBasis x x (mem_chart_source CoordinateSpace x)
  simp only [einsteinPair, contractAt_eq_sum x b, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_assoc _ _ _

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

private theorem cosphere_graph_measurableEmbedding (r : Metric (M := M)) :
    MeasurableEmbedding (fun p : Cosphere r => (projection p, p)) := by
  let g (p : Cosphere r) := (projection p, p)
  refine ⟨fun p q h => congrArg Prod.snd h, (continuous_projection r).measurable.prodMk measurable_id, ?_⟩
  intro S hS
  have hIm : g '' S = (Prod.snd ⁻¹' S) ∩ {z : M × Cosphere r | z.1 = projection z.2} := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, rfl⟩
    · intro hz
      exact ⟨z.2, hz.1, Prod.ext hz.2.symm rfl⟩
  change MeasurableSet (g '' S)
  rw [hIm]
  exact (measurable_snd hS).inter
    (isClosed_eq continuous_fst ((continuous_projection r).comp continuous_snd)).measurableSet

/-- Every compact smooth symmetric tensor test has the correct conditional moment for the same kernel. -/
theorem ae_einsteinPair_eq_angularKernel_moment (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (hMom : HasCosphereEinsteinMoments r B hn μ) (κ : Kernel M (Cosphere r)) [IsSFiniteKernel κ]
    (hLaw : ManifoldVolume.geometricMeasure B ⊗ₘ κ = μ.map (fun p => (projection p, p)))
    (Q : ContravariantTwoTensor M) (hQ : IsTensorTest Q) :
    ∀ᵐ x ∂ManifoldVolume.geometricMeasure B,
      einsteinPair B hn Q x = ∫ p : Cosphere r, intrinsicTensorPhase Q p.val ∂κ x := by
  let V := ManifoldVolume.geometricMeasure B
  let G (p : Cosphere r) := intrinsicTensorPhase Q p.val
  let M₁ (x : M) := ∫ p, G p ∂κ x
  let E := einsteinPair B hn Q
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  letI : IsLocallyFiniteMeasure V := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  have hπ : Measurable (projection (r := r)) := (continuous_projection r).measurable
  have hGraph := cosphere_graph_measurableEmbedding r
  have hC : κ ∘ₘ V = μ := by
    rw [← Measure.snd_compProd, hLaw, Measure.snd_map_prodMk hπ]
    exact Measure.map_id
  obtain ⟨hE, hG, _⟩ := hMom Q hQ
  have hM : Integrable M₁ V := by
    change Integrable G μ at hG
    rw [← hC, Measure.comp_eq_comp_const_apply] at hG
    exact hG.integral_comp
  have h0 : (fun x => E x - M₁ x) =ᵐ[V] 0 := by
    apply ae_eq_zero_of_integrable_mul_smooth_compact_tests V _ (hE.sub hM)
    intro φ hφ hc
    let Qφ : ContravariantTwoTensor M := fun x => φ x • Q x
    let ψ (z : M × Cosphere r) := φ z.1 * G z.2
    obtain ⟨hBase, hPhase, hEq⟩ := hMom Qφ (isTensorTest_scalar_mul Q hQ φ hφ hc)
    have hIe : Integrable (fun x => φ x * E x) V :=
      hBase.congr (Eventually.of_forall (einsteinPair_scalar_mul B hn Q φ))
    have hIψ : Integrable ψ (V ⊗ₘ κ) := by
      rw [hLaw]
      exact hGraph.integrable_map_iff.mpr hPhase
    obtain ⟨C, hCn, hCb⟩ := ((hc : IsCompact (tsupport φ)).image hφ.continuous).isBounded.exists_pos_norm_le
    have hφb : ∀ᵐ x ∂V, ‖φ x‖ ≤ C := Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport φ
      · exact hCb _ (mem_image_of_mem _ hx)
      · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
        exact hCn.le
    have hIm : Integrable (fun x => φ x * M₁ x) V := hM.bdd_mul' hφ.continuous.aestronglyMeasurable hφb
    have hh : (∫ x, φ x * E x ∂V) = ∫ x, φ x * M₁ x ∂V := by
      calc
        _ = ∫ x, einsteinPair B hn Qφ x ∂V :=
          integral_congr_ae (Eventually.of_forall fun x => (einsteinPair_scalar_mul B hn Q φ x).symm)
        _ = ∫ p : Cosphere r, intrinsicTensorPhase Qφ p.val ∂μ := hEq
        _ = ∫ z, ψ z ∂(V ⊗ₘ κ) := by
          rw [hLaw, hGraph.integral_map]
          rfl
        _ = ∫ x, ∫ p, φ x * G p ∂κ x ∂V := Measure.integral_compProd hIψ
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => integral_smul (φ x) G
    have hSplit : (fun x => φ x * (E x - M₁ x)) = (fun x => φ x * E x) - (fun x => φ x * M₁ x) :=
      funext fun x => mul_sub _ _ _
    change Integrable (fun x => φ x * (E x - M₁ x)) V ∧ (∫ x, φ x * (E x - M₁ x) ∂V) = 0
    rw [hSplit]
    refine ⟨hIe.sub hIm, ?_⟩
    change (∫ x, φ x * E x - φ x * M₁ x ∂V) = 0
    rw [integral_sub hIe hIm, hh, sub_self]
  exact h0.mono fun _ h => sub_eq_zero.mp h

end Burnett.F08.IntrinsicBaseMarginal
