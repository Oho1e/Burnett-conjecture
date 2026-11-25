import Burnett.Analysis.Microlocal.Overlap.SymmetricJetPairingKernel

/-! Pair an actual bundle endomorphism kernel using the intrinsic auxiliary metric. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 380000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Matrix Burnett.Geometry ConnectionDifference ManifoldMetric MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped Manifold ContDiff Matrix ComplexConjugate

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The actual Gram paired in the preferred basis at the point. The next
theorem identifies it in every compatible chart. -/
def symmetricJetFiberGram (r : Metric (M := M)) (p : M) :
    SymmetricJetFiber M p →ₛₗ[starRingEnd ℂ] SymmetricJetFiber M p →ₗ[ℂ] ℂ := by
  let c := AtlasChart.atPoint p
  let b := chartTangentBasis c p (mem_chart_source E p)
  let W : SymmetricJetFiber M p →ₗ[ℂ] (JetSlot → ℂ) :=
    (jetFiberCoordinates b).toLinearMap.comp (complexSymmetricJet (TangentSpace Model p)).subtype
  let H := atlasJetGram r c p
  exact {
    toFun := fun v =>
      { toFun := fun u => star (W v) ⬝ᵥ (H *ᵥ W u)
        map_add' := fun u w => by simp only [map_add, Matrix.mulVec_add, dotProduct_add]
        map_smul' := fun a u => by simp only [RingHom.id_apply, map_smul, Matrix.mulVec_smul, dotProduct_smul] }
    map_add' := fun v w => by
      apply LinearMap.ext
      intro u
      change star (W (v + w)) ⬝ᵥ (H *ᵥ W u) = _
      simp only [map_add, star_add, add_dotProduct, LinearMap.add_apply]
      rfl
    map_smul' := fun a v => by
      apply LinearMap.ext
      intro u
      change star (W (a • v)) ⬝ᵥ (H *ᵥ W u) = _
      simp only [map_smul, star_smul, smul_dotProduct, LinearMap.smul_apply, Complex.star_def]
      rfl }

theorem symmetricJetFiberGram_in_chart (r : Metric (M := M)) (p : M) (c : AtlasChart M)
    (hc : p ∈ c.chart.source) (v u : SymmetricJetFiber M p) :
    let W := jetFiberCoordinates (chartTangentBasis c p hc)
    symmetricJetFiberGram r p v u =
      star (W v.val) ⬝ᵥ (atlasJetGram r c p *ᵥ W u.val) := by
  intro W
  let d := AtlasChart.atPoint p
  have hd : p ∈ d.chart.source := mem_chart_source E p
  let D := jetFiberCoordinates (chartTangentBasis d p hd)
  let U := atlasJetTransition c d p
  have hV : D v.val = U *ᵥ W v.val := jetFiberCoordinates_atlasChange c d hc hd v.val
  have hU : D u.val = U *ᵥ W u.val := jetFiberCoordinates_atlasChange c d hc hd u.val
  have hGram : Uᴴ * atlasJetGram r d p * U = atlasJetGram r c p :=
    atlasJetGram_transition r c d p hc hd
  change star (D v.val) ⬝ᵥ (atlasJetGram r d p *ᵥ D u.val) = _
  rw [hV, hU, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hGram]

/-- The geometric kernel maps the actual input fiber to the actual output fiber. -/
abbrev SymmetricJetLinearKernel (M : Type*) [TopologicalSpace M] [ChartedSpace E M] :=
  ∀ p q : M, SymmetricJetFiber M q →ₗ[ℂ] SymmetricJetFiber M p

/-- Insert the true metric on the left of the kernel, without a global frame. -/
def pairSymmetricJetLinearKernel (r : Metric (M := M)) (K : SymmetricJetLinearKernel M) :
    SymmetricJetPairingKernel M := fun p q =>
  { toFun := fun v => (symmetricJetFiberGram r p v).comp (K p q)
    map_add' := fun v w => by rw [map_add, LinearMap.add_comp]
    map_smul' := fun a v => by rw [map_smulₛₗ, LinearMap.smul_comp] }

theorem pairSymmetricJetLinearKernel_in_chart (r : Metric (M := M)) (K : SymmetricJetLinearKernel M)
    (p q : M) (c : AtlasChart M) (hc : p ∈ c.chart.source)
    (v : SymmetricJetFiber M p) (u : SymmetricJetFiber M q) :
    let W := jetFiberCoordinates (chartTangentBasis c p hc)
    pairSymmetricJetLinearKernel r K p q v u =
      star (W v.val) ⬝ᵥ (atlasJetGram r c p *ᵥ W (K p q u).val) :=
  symmetricJetFiberGram_in_chart r p c hc v (K p q u)

end Burnett.Microlocal.Overlap
