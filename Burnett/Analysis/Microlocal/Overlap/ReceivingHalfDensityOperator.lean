import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSourceReplacement

/-! The actual cut half-density transport extends as a bounded L² operator. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 3500000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Set MeasureTheory Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (coeffMul_tsupport_subset_real)
open Burnett.Microlocal.BesselLocalization (coeffMul coeffMul_toLp physicalCoefficient)
open Burnett.X02.SobolevTestJet (D)
open scoped InnerProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Transport with a fixed compact cutoff, extended from the Schwartz image
with its inherited L² norm. -/
theorem exists_receivingHalfDensityOperator
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ K) :
    ∃ U : ComplexL2 E →L[ℂ] ComplexL2 E, ∀ f : SchwartzMap E ℂ,
      U (f.toLp 2 volume) =
        (transportedHalfDensitySchwartz c d K hK hKU (coeffMul χ f)
          ((coeffMul_tsupport_subset_real χ f).trans hχ)).toLp 2 volume := by
  let F (f : SchwartzMap E ℂ) := transportedHalfDensitySchwartz c d K hK hKU (coeffMul χ f)
    ((coeffMul_tsupport_subset_real χ f).trans hχ)
  let V := schwartzL2Range (V := E)
  let e := schwartzRangeEquiv (V := E)
  have hRaw (f : SchwartzMap E ℂ) (z : E) :
      F f z = (c.transition d '' K).indicator
        (fun y => overlapJacobianWeight d c y • (((χ : E → ℝ) (overlapTransition d c y) : ℂ) *
          f (overlapTransition d c y))) z := rfl
  let A : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap E ℂ :=
    { toFun := F
      map_add' := fun f g => by
        ext z
        simp only [SchwartzMap.add_apply, hRaw]
        by_cases hz : z ∈ c.transition d '' K
        · simp only [indicator_of_mem hz, mul_add, smul_add]
        · simp only [indicator_of_notMem hz, add_zero]
      map_smul' := fun t f => by
        ext z
        simp only [RingHom.id_apply, SchwartzMap.smul_apply, hRaw]
        by_cases hz : z ∈ c.transition d '' K
        · simp only [indicator_of_mem hz, Complex.real_smul, smul_eq_mul]
          ring
        · simp only [indicator_of_notMem hz, smul_zero] }
  let B : V →ₗ[ℂ] ComplexL2 E := (schwartzLpMap (V := E)).toLinearMap.comp (A.comp e.symm.toLinearMap)
  have hB (v : V) : ‖B v‖ ≤ (physicalCoefficient χ).bound * ‖v‖ := by
    obtain ⟨f, rfl⟩ := e.surjective v
    change ‖(F (e.symm (e f))).toLp 2 volume‖ ≤ (physicalCoefficient χ).bound * ‖f.toLp 2 volume‖
    rw [LinearEquiv.symm_apply_apply]
    change ‖(transportedHalfDensitySchwartz c d K hK hKU (coeffMul χ f) _).toLp 2 volume‖ ≤ _
    rw [transportedHalfDensitySchwartz_norm_toLp, coeffMul_toLp]
    exact symbolL2_norm_le (physicalCoefficient χ) (f.toLp 2 volume)
  let B' : V →L[ℂ] ComplexL2 E := B.mkContinuous (physicalCoefficient χ).bound hB
  have hDense : DenseRange V.subtypeL := schwartzL2Range_dense.denseRange_val
  have hInd := V.subtypeₗᵢ.isometry.isUniformInducing
  let U := B'.extend V.subtypeL hDense hInd
  refine ⟨U, fun f => ?_⟩
  have h := ContinuousLinearMap.extend_eq B' V.subtypeL hDense hInd (e f)
  change U (f.toLp 2 volume) = (F (e.symm (e f))).toLp 2 volume at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end Burnett.Microlocal.AtlasOverlapKernel
