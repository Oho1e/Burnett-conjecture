import Burnett.Geometry.Cotangent.OpenRegion.CotangentHomeomorph
import Burnett.Geometry.Cotangent.WeightedMomentumTransport
import Burnett.Geometry.Cotangent.RadialExtension

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter Bundle
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.ActualTestLift (isOpen_puncturedCotangent)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def cotangentOverOpen (U : Opens M) : Opens (CotangentBundle M) := ⟨cotangentOver U, isOpen_cotangentOver U⟩

theorem contMDiff_cotangentOpenHomeomorph_inv (U : Opens M) :
    ContMDiff CotangentModelWithCorners CotangentModelWithCorners ∞
      (fun p : cotangentOverOpen U => (cotangentOpenHomeomorph U).symm p) := by
  intro p
  let e := cotangentOpenHomeomorph U
  let c := (e.symm p).1
  let O := cotangentOverOpen U
  let s : Set O := Subtype.val ⁻¹' cotangentSource c.val
  have hs : IsOpen s := (isOpen_cotangentSource c.val).preimage continuous_subtype_val
  have hp : p ∈ s := mem_chart_source CoordinateSpace c.val
  let L := (cotangentChart c.val) ∘ (Subtype.val : O → CotangentBundle M)
  have hL : ContMDiffOn CotangentModelWithCorners CoordinatePhaseModel ∞ L s :=
    (contMDiffOn_cotangentChart c.val).comp contMDiff_subtype_val.contMDiffOn (fun _ h => h)
  have hSrc (q : O) (hq : q ∈ s) : e.symm q ∈ cotangentSource c := ⟨trivial, hq⟩
  have hEq (q : O) (hq : q ∈ s) : L q = cotangentChart c (e.symm q) := by
    have hVal : cotangentOpenVal U (e.symm q) = q.val := congrArg Subtype.val (e.apply_symm_apply q)
    rw [← cotangentChart_openVal U c (hSrc q hq), hVal]
    rfl
  have hmap : MapsTo L s (phaseTarget c) := by
    intro q hq
    rw [hEq q hq]
    exact cotangentChart_mapsTo c (hSrc q hq)
  have hcomp := (contMDiffOn_cotangentChartInverse c).comp hL hmap
  have hlocal : ContMDiffOn CotangentModelWithCorners CotangentModelWithCorners ∞ (fun q : O => e.symm q) s := by
    apply hcomp.congr
    intro q hq
    rw [Function.comp_apply, hEq q hq, cotangentChart_left_inv c (hSrc q hq)]
  exact hlocal.contMDiffAt (hs.mem_nhds hp)

/-- The original local test is used in the region and extended by zero outside. -/
def extendCotangentTest (U : Opens M) (a : CotangentBundle U → ℝ) (p : CotangentBundle M) : ℝ := by
  classical
  exact if h : p ∈ cotangentOver U then a ((cotangentOpenHomeomorph U).symm ⟨p, h⟩) else 0

theorem extendCotangentTest_on_region (U : Opens M) (a : CotangentBundle U → ℝ) (p : CotangentBundle U) :
    extendCotangentTest U a (cotangentOpenVal U p) = a p := by
  have hp : cotangentOpenVal U p ∈ cotangentOver U := p.1.property
  rw [extendCotangentTest, dif_pos hp]
  exact congrArg a ((cotangentOpenHomeomorph U).symm_apply_apply p)

theorem extendCotangentTest_support [T2Space M] (U : Opens M) (a : CotangentBundle U → ℝ)
    {K : Set U} (hK : IsCompact K) (hSupp : tsupport a ⊆ (fun q => q.1) ⁻¹' K) :
    tsupport (extendCotangentTest U a) ⊆ (fun p : CotangentBundle M => p.1) ⁻¹' (Subtype.val '' K) := by
  apply closure_minimal _ ((hK.image continuous_subtype_val).isClosed.preimage continuous_cotangent_projection)
  intro p hp
  by_cases hIn : p ∈ cotangentOver U
  · rw [Function.mem_support, extendCotangentTest, dif_pos hIn] at hp
    let q := (cotangentOpenHomeomorph U).symm ⟨p, hIn⟩
    have hBase : q.1 ∈ K := hSupp (subset_tsupport _ hp)
    have hProj : q.1.val = p.1 := congrArg (fun z : cotangentOver U => z.val.1)
      ((cotangentOpenHomeomorph U).apply_symm_apply ⟨p, hIn⟩)
    exact ⟨q.1, hBase, hProj⟩
  · exact (hp (by rw [extendCotangentTest, dif_neg hIn])).elim

theorem extendCotangentTest_smooth [T2Space M] (U : Opens M) (a : CotangentBundle U → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    {K : Set U} (hK : IsCompact K) (hSupp : tsupport a ⊆ (fun p => p.1) ⁻¹' K) :
    ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ (extendCotangentTest U a) puncturedCotangent := by
  intro p hp
  by_cases hIn : p ∈ cotangentOver U
  · let O := cotangentOverOpen U
    let q : O := ⟨p, hIn⟩
    let L := (cotangentOpenHomeomorph U).symm
    have hpun : L q ∈ puncturedCotangent := hp
    have hAt := ha.contMDiffAt (isOpen_puncturedCotangent.mem_nhds hpun)
    have hcomp := hAt.comp q (contMDiff_cotangentOpenHomeomorph_inv U).contMDiffAt
    have hEq : (fun x : O => extendCotangentTest U a x.val) = a ∘ L := by
      funext x
      exact dif_pos x.property
    have hc : ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞
        (fun x : O => extendCotangentTest U a x.val) q := hEq.symm ▸ hcomp
    exact (contMDiffAt_subtype_iff.mp hc).contMDiffWithinAt
  · have hOut : p.1 ∉ Subtype.val '' K := by
      rintro ⟨x, _, hx⟩
      exact hIn (show p.1 ∈ U from hx ▸ x.property)
    have hClosed : IsClosed (Subtype.val '' K : Set M) := (hK.image continuous_subtype_val).isClosed
    have hNear : ∀ᶠ q in 𝓝 p, q.1 ∉ (Subtype.val '' K : Set M) :=
      continuous_cotangent_projection.continuousAt.preimage_mem_nhds (hClosed.isOpen_compl.mem_nhds hOut)
    have hEq : extendCotangentTest U a =ᶠ[𝓝 p] (fun _ => 0) := hNear.mono fun q hq =>
      image_eq_zero_of_notMem_tsupport (fun hz => hq (extendCotangentTest_support U a hK hSupp hz))
    exact (hEq.contMDiffAt_iff.mpr contMDiffAt_const).contMDiffWithinAt

theorem extendCotangentTest_degreeOne (U : Opens M) (a : CotangentBundle U → ℝ)
    (hA : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) :
    ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ),
      extendCotangentTest U a (cotangentScale t p) = t * extendCotangentTest U a p := by
  intro p hp t ht
  by_cases hIn : p ∈ cotangentOver U
  · have hIn' : cotangentScale t p ∈ cotangentOver U := hIn
    let L := (cotangentOpenHomeomorph U).symm
    have hScale : L ⟨cotangentScale t p, hIn'⟩ = cotangentScale t (L ⟨p, hIn⟩) := rfl
    rw [extendCotangentTest, dif_pos hIn', extendCotangentTest, dif_pos hIn, hScale]
    exact hA _ hp t ht
  · have hIn' : cotangentScale t p ∉ cotangentOver U := hIn
    rw [extendCotangentTest, dif_neg hIn', extendCotangentTest, dif_neg hIn, mul_zero]

end Burnett.Geometry.OpenRegion
