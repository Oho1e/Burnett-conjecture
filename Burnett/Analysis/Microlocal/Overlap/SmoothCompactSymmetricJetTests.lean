import Burnett.Analysis.Microlocal.Overlap.SymmetricJetChartSections

/-! Smooth compact tests on the actual symmetric jet bundle. -/

set_option autoImplicit false
set_option maxHeartbeats 6250000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical Matrix Burnett.Fourier Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart ChartVolume
open Burnett.F07.IntrinsicAmplitudeCoordinates (fixedCotangentTransitionMatrix)
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity fixedHalfDensity_smooth)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped Manifold ContDiff Topology BigOperators Matrix Kronecker

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Smoothness is checked on true ordered coordinates in every compatible chart. -/
def IsSmoothSymmetricJetSection (s : SymmetricJetSection M) : Prop :=
  ∀ (c : AtlasChart M) (i : JetSlot),
    ContDiffOn ℝ ∞ (fun x => symmetricJetComponent c s i (c.chart.symm x)) c.chart.target

private theorem symmetricJetComponent_add (c : AtlasChart M)
    (f g : SymmetricJetSection M) (i : JetSlot) (p : M) :
    symmetricJetComponent c (f + g) i p = symmetricJetComponent c f i p + symmetricJetComponent c g i p := by
  by_cases hp : p ∈ c.chart.source <;> simp [symmetricJetComponent, hp, map_add]

private theorem symmetricJetComponent_smul (c : AtlasChart M) (a : ℂ)
    (f : SymmetricJetSection M) (i : JetSlot) (p : M) :
    symmetricJetComponent c (a • f) i p = a * symmetricJetComponent c f i p := by
  by_cases hp : p ∈ c.chart.source <;> simp [symmetricJetComponent, hp, map_smul, smul_eq_mul]

/-- The test space \(\Gamma_c\) of actual complex symmetric jets, with compact
support in the manifold and smoothness in the genuine chart trivializations. -/
def smoothCompactSymmetricJet (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] :
    Submodule ℂ (SymmetricJetSection M) where
  carrier := {s | IsSmoothSymmetricJetSection s ∧
    ∃ K : Set M, IsCompact K ∧ symmetricJetSectionSupport s ⊆ K}
  zero_mem' := by
    refine ⟨fun c i => (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) c.chart.target).congr ?_,
      ⟨∅, isCompact_empty, ?_⟩⟩
    · intro x _
      exact symmetricJetComponent_eq_zero c 0 i (c.chart.symm x) rfl
    · intro p hp
      exact False.elim (hp rfl)
  add_mem' := by
    intro f g hf hg
    obtain ⟨hfs, K, hK, hfK⟩ := hf
    obtain ⟨hgs, U, hU, hgU⟩ := hg
    refine ⟨fun c i => ((hfs c i).add (hgs c i)).congr ?_, ⟨K ∪ U, hK.union hU, ?_⟩⟩
    · intro x _
      exact symmetricJetComponent_add c f g i (c.chart.symm x)
    · intro p hp
      by_contra h
      have hf0 : f p = 0 := by
        by_contra hf'
        exact h (Or.inl (hfK hf'))
      have hg0 : g p = 0 := by
        by_contra hg'
        exact h (Or.inr (hgU hg'))
      exact hp (by simp [hf0, hg0])
  smul_mem' := by
    intro a f hf
    obtain ⟨hfs, K, hK, hfK⟩ := hf
    refine ⟨fun c i => ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => a) c.chart.target).mul
      (hfs c i)).congr ?_, ⟨K, hK, ?_⟩⟩
    · intro x _
      exact symmetricJetComponent_smul c a f i (c.chart.symm x)
    · intro p hp
      by_contra h
      have hf0 : f p = 0 := by
        by_contra hf'
        exact h (hfK hf')
      exact hp (by simp [hf0])

/-- Smooth pointwise scalar multiplication keeps a genuine symmetric section
in the same compact smooth test module. -/
def scaleCompactSymmetricJet (β : M → ℝ) (hβ : ContMDiff Model 𝓘(ℝ) ∞ β)
    (s : smoothCompactSymmetricJet M) : smoothCompactSymmetricJet M := by
  let u : SymmetricJetSection M := fun p => (β p : ℂ) • s.val p
  refine ⟨u, ?_, ?_⟩
  · intro c i
    have hCoef : ContDiffOn ℝ ∞ (fun y => (β (c.chart.symm y) : ℂ)) c.chart.target := by
      intro y hy
      have hManifold := hβ.contMDiffAt.comp y (contMDiffAt_symm_of_mem_maximalAtlas c.compatible hy)
      have hReal := contMDiffAt_iff_contDiffAt.mp hManifold
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y hReal).contDiffWithinAt
    refine (hCoef.mul (s.property.1 c i)).congr ?_
    intro y hy
    have hcy := c.chart.symm_mapsTo hy
    rw [symmetricJetComponent_of_mem c _ i _ hcy, symmetricJetComponent_of_mem c _ i _ hcy]
    change jetFiberCoordinates _ ((β (c.chart.symm y) : ℂ) •
        (s.val (c.chart.symm y) : ComplexCovariantJet (TangentSpace Model (c.chart.symm y)))) i = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  · obtain ⟨C, hC, hs⟩ := s.property.2
    exact ⟨C, hC, fun p hp => hs (by
      intro hz
      exact hp (by simp [u, hz]))⟩

theorem scaleCompactSymmetricJet_apply (β : M → ℝ) (hβ : ContMDiff Model 𝓘(ℝ) ∞ β)
    (s : smoothCompactSymmetricJet M) (p : M) :
    (scaleCompactSymmetricJet β hβ s).val p = (β p : ℂ) • s.val p := rfl

variable [T2Space M] [SecondCountableTopology M]

omit [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] in
private theorem contDiffOn_atlasJetTransition_in_chart (c d : AtlasChart M) (i j : JetSlot) :
    ContDiffOn ℝ ∞ (fun y => atlasJetTransition c d (d.chart.symm y) i j) (d.transition c).source := by
  let e := d.transition c
  let R := fixedCotangentTransitionMatrix c d
  have h (a b : Index) :
      ContDiffOn ℝ ∞ (fun y => (R (d.chart.symm y) a b : ℂ)) e.source := by
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn (fixedJacobian_entry_smooth d c b a)).congr ?_
    intro y hy
    change ((derivativeMatrix (fderiv ℝ e (d.chart (d.chart.symm y))))ᵀ a b : ℂ) =
      (derivativeMatrix (fderiv ℝ e y) b a : ℂ)
    rw [d.chart.right_inv hy.1, Matrix.transpose_apply]
  change ContDiffOn ℝ ∞ (fun y => (R (d.chart.symm y) i.1 j.1 : ℂ) *
    ((R (d.chart.symm y) i.2.1 j.2.1 : ℂ) * (R (d.chart.symm y) i.2.2 j.2.2 : ℂ))) e.source
  exact (h i.1 j.1).mul ((h i.2.1 j.2.1).mul (h i.2.2 j.2.2))

/-- A smooth array supported in a compact chart window gives a genuine
globally smooth section, including across the boundary of that chart. -/
theorem isSmoothSymmetricJetSection_chartLift (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (c : AtlasChart M) (f : JetSlot → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (K : Set E) (hK : IsCompact K)
    (hKc : K ⊆ c.chart.target) (hSupp : ∀ i, support (f i) ⊆ K) :
    IsSmoothSymmetricJetSection (symmetricJetChartLift B c f) := by
  let S := c.chart.symm '' K
  let v := symmetricJetChartLift B c f
  have hS : IsCompact S := hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKc)
  have hSc : S ⊆ c.chart.source := (c.chart.symm_mapsTo.mono_left hKc).image_subset
  have hS' : symmetricJetSectionSupport v ⊆ S := symmetricJetChartLift_support B c f K hSupp
  intro d i
  let e := d.transition c
  let hcoord (y : E) (j : JetSlot) := (fixedHalfDensity B c y : ℂ)⁻¹ *
    ((2 : ℂ)⁻¹ * (f j y + f (jetPairSwap j) y))
  have hδ : ContDiffOn ℝ ∞ (fun y => (fixedHalfDensity B c y : ℂ)⁻¹) c.chart.target := by
    have h := (fixedHalfDensity_smooth B hB hn c).inv (fun y hy => (fixedHalfDensity_pos B hn c y hy).ne')
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn h).congr ?_
    intro y _
    exact (Complex.ofReal_inv (fixedHalfDensity B c y)).symm
  have hLocal (j : JetSlot) : ContDiffOn ℝ ∞ (fun y => hcoord y j) c.chart.target :=
    hδ.mul (contDiffOn_const.mul (((hf j).add (hf (jetPairSwap j))).contDiffOn))
  have hMap : MapsTo e e.source c.chart.target := fun y hy => (e.mapsTo hy).1
  have hExpr : ContDiffOn ℝ ∞ (fun y => ∑ j, atlasJetTransition c d (d.chart.symm y) i j *
      hcoord (e y) j) e.source :=
    ContDiffOn.sum fun j _ => (contDiffOn_atlasJetTransition_in_chart c d i j).mul
      ((hLocal j).comp (d.smooth_transition c) hMap)
  have hOver : ContDiffOn ℝ ∞ (fun y => symmetricJetComponent d v i (d.chart.symm y)) e.source := by
    refine hExpr.congr ?_
    intro y hy
    have hdp := d.chart.symm_mapsTo hy.1
    have hcp : d.chart.symm y ∈ c.chart.source := hy.2
    have hTrans (j : JetSlot) :
        jetFiberCoordinates (Burnett.F07.IntrinsicAmplitudeCoordinates.chartTangentBasis c (d.chart.symm y) hcp)
          (v (d.chart.symm y) : ComplexCovariantJet (TangentSpace Model (d.chart.symm y))) j =
          hcoord (e y) j := by
      rw [← symmetricJetComponent_of_mem c v j _ hcp]
      change symmetricJetComponent c (symmetricJetChartLift B c f) j (d.chart.symm y) = _
      rw [symmetricJetComponent_chartLift B c f j _ hcp]
      simp only [receivingScalarPhysicalLift, indicator_of_mem hcp, hcoord, e, AtlasChart.transition,
        OpenPartialHomeomorph.trans_apply]
      ring
    rw [symmetricJetComponent_of_mem d v i _ hdp]
    rw [jetFiberCoordinates_atlasChange c d hcp hdp]
    simp only [Matrix.mulVec, dotProduct, hTrans]
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  by_cases hxOver : x ∈ e.source
  · exact ⟨e.source, e.open_source, hxOver, hOver.mono inter_subset_right⟩
  · let W := d.chart.target ∩ d.chart.symm ⁻¹' Sᶜ
    have hW : IsOpen W := d.chart.continuousOn_symm.isOpen_inter_preimage d.chart.open_target hS.isClosed.isOpen_compl
    have hxW : x ∈ W := by
      refine ⟨hx, fun h => hxOver ?_⟩
      exact ⟨hx, hSc h⟩
    refine ⟨W, hW, hxW,
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) (d.chart.target ∩ W)).congr ?_⟩
    intro y hy
    have hzero : v (d.chart.symm y) = 0 := by
      by_contra h
      exact hy.2.2 (hS' h)
    exact symmetricJetComponent_eq_zero d v i _ hzero

/-- A compact chart lift as an element of the genuine smooth compact test module. -/
def compactSymmetricJetChartTest (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (c : AtlasChart M) (f : JetSlot → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (hSupp : ∀ i, support (f i) ⊆ K) :
    smoothCompactSymmetricJet M :=
  ⟨symmetricJetChartLift B c f, isSmoothSymmetricJetSection_chartLift B hB hn c f hf K hK hKc hSupp,
    ⟨c.chart.symm '' K, hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKc),
      symmetricJetChartLift_support B c f K hSupp⟩⟩

end Burnett.Microlocal.Overlap
