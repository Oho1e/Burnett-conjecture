import Burnett.Analysis.Microlocal.Overlap.JointClassicalPrincipalUniqueness

/-! Identify the principal symbol of a finite weighted bilateral pairing. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 6200000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open Burnett.Analysis.HminusWeightedDual (complexTest)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct RealInnerProductSpace Topology

open private eqOn_interior_of_local_diagonal_pairings from Burnett.Analysis.Microlocal.Overlap.JointClassicalPrincipalUniqueness

local notation "E" => CoordinateSpace

/-- Global bounds for modulation and continuity at each nonzero frequency. -/
structure HasAngularPrincipalRegularity (a : E → E → ℂ) : Prop where
  bounded : ∃ C : ℝ, ∀ x η, ‖a x η‖ ≤ C
  continuous_infrared : Continuous (uncurry (infraredAngularPrincipal a))
  continuous_base : ∀ ξ, ξ ≠ 0 → Continuous (fun x => a x ξ)
  continuous_frequency : ∀ x ξ, ξ ≠ 0 → ContinuousAt (a x) ξ
  degree_zero : ∀ x, DegreeZero (a x)

/-- A smooth weight times a compactly supported Schwartz test is Schwartz. -/
def compactWeightedSchwartz (w : E → ℂ) (hw : ContDiff ℝ ∞ w)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) : SchwartzMap E ℂ :=
  hf.mul_left.toSchwartzMap (hw.mul (f.smooth ⊤))

@[simp] theorem compactWeightedSchwartz_apply (w : E → ℂ) (hw : ContDiff ℝ ∞ w)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) (x : E) :
    compactWeightedSchwartz w hw f hf x = w x * f x := rfl

theorem compactWeightedSchwartz_hasCompactSupport (w : E → ℂ) (hw : ContDiff ℝ ∞ w)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) :
    HasCompactSupport (compactWeightedSchwartz w hw f hf : E → ℂ) :=
  hf.mul_left

private theorem compactWeightedSchwartz_tsupport (w : E → ℂ) (hw : ContDiff ℝ ∞ w)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) :
    tsupport (compactWeightedSchwartz w hw f hf : E → ℂ) ⊆ tsupport (f : E → ℂ) :=
  tsupport_mul_subset_right

private theorem compactModulatedSchwartz_hasCompactSupport (k : E)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) :
    HasCompactSupport (compactModulatedSchwartz k f hf : E → ℂ) :=
  hf.of_isClosed_subset isClosed_closure (compactModulatedSchwartz_tsupport k f hf)

private theorem compactWeightedSchwartz_modulated (k : E) (w : E → ℂ) (hw : ContDiff ℝ ∞ w)
    (f : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ)) :
    compactWeightedSchwartz w hw (compactModulatedSchwartz k f hf)
      (compactModulatedSchwartz_hasCompactSupport k f hf) =
    compactModulatedSchwartz k (compactWeightedSchwartz w hw f hf)
      (compactWeightedSchwartz_hasCompactSupport w hw f hf) := by
  ext x
  change w x * ((Real.fourierChar ⟪x, k⟫ : ℂ) * f x) =
    (Real.fourierChar ⟪x, k⟫ : ℂ) * (w x * f x)
  exact mul_left_comm _ _ _

/-- Exact agreement of the actual local pairings determines the mixed principal.
The weights act on compact tests, so their global extensions need no norm bound. -/
theorem eqOn_interior_principalSymbol_of_bilateralWeightedPairings
    {I J : Type*} [Fintype I] [Fintype J]
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (Tij : I → J → ComplexL2 E →L[ℂ] ComplexL2 E)
    (a : E → E → ℂ) (aij : I → J → E → E → ℂ)
    (u : I → E → ℂ) (v : J → E → ℂ) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (hv : ∀ j, ContDiff ℝ ∞ (v j)) (L : Set E)
    (hT : HasLocalClassicalRepresentation T a L)
    (hTij : ∀ i j, HasLocalClassicalRepresentation (Tij i j) (aij i j) L)
    (ha : HasAngularPrincipalRegularity a) (haij : ∀ i j, HasAngularPrincipalRegularity (aij i j))
    (hPair : ∀ (f g : SchwartzMap E ℂ) (hf : HasCompactSupport (f : E → ℂ))
      (hg : HasCompactSupport (g : E → ℂ)),
      tsupport (f : E → ℂ) ⊆ L → tsupport (g : E → ℂ) ⊆ L →
      inner ℂ (f.toLp 2 volume) (T (g.toLp 2 volume)) =
        ∑ i, ∑ j, inner ℂ ((compactWeightedSchwartz (u i) (hu i) f hf).toLp 2 volume)
          (Tij i j ((compactWeightedSchwartz (v j) (hv j) g hg).toLp 2 volume)))
    (ξ : E) (hξ : ξ ≠ 0) :
    EqOn (fun x => a x ξ) (fun x => ∑ i, ∑ j, conj (u i x) * aij i j x ξ * v j x)
      (interior L) := by
  classical
  let b (x : E) := ∑ i, ∑ j, conj (u i x) * aij i j x ξ * v j x
  have hb : Continuous b :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((Complex.continuous_conj.comp (hu i).continuous).mul ((haij i j).continuous_base ξ hξ)).mul
        (hv j).continuous
  apply eqOn_interior_of_local_diagonal_pairings _ b (ha.continuous_base ξ hξ) hb L
  intro φ hφ
  let f := complexTest φ
  have hSupport : tsupport (f : E → ℂ) ⊆ tsupport (φ : E → ℝ) := by
    apply closure_mono
    intro x hx
    change ((φ : E → ℝ) x : ℂ) ≠ 0 at hx
    exact Complex.ofReal_ne_zero.mp hx
  have hfc : HasCompactSupport (f : E → ℂ) := (test_compactSupport φ).comp_left Complex.ofReal_zero
  have hfL : tsupport (f : E → ℂ) ⊆ L := hSupport.trans hφ
  let F (i : I) := compactWeightedSchwartz (u i) (hu i) f hfc
  let G (j : J) := compactWeightedSchwartz (v j) (hv j) f hfc
  have hF (i : I) : HasCompactSupport (F i : E → ℂ) :=
    compactWeightedSchwartz_hasCompactSupport (u i) (hu i) f hfc
  have hG (j : J) : HasCompactSupport (G j : E → ℂ) :=
    compactWeightedSchwartz_hasCompactSupport (v j) (hv j) f hfc
  have hGL (j : J) : tsupport (G j : E → ℂ) ⊆ L :=
    (compactWeightedSchwartz_tsupport (v j) (hv j) f hfc).trans hfL
  obtain ⟨C, hC⟩ := ha.bounded
  have hTLimit := tendsto_modulated_pairing_of_hasLocalClassicalRepresentation T a L hT C hC
    ha.continuous_infrared ξ hξ (fun x => ha.continuous_frequency x ξ hξ) ha.degree_zero f f hfc hfc hfL
  let P (i : I) (j : J) (n : ℕ) :=
    inner ℂ ((compactModulatedSchwartz ((n : ℝ) • ξ) (F i) (hF i)).toLp 2 volume)
      (Tij i j ((compactModulatedSchwartz ((n : ℝ) • ξ) (G j) (hG j)).toLp 2 volume))
  let p (i : I) (j : J) (x : E) := conj (F i x) * (aij i j x ξ * G j x)
  have hEach (i : I) (j : J) : Tendsto (P i j) atTop (𝓝 (∫ x, p i j x)) := by
    obtain ⟨Cij, hCij⟩ := (haij i j).bounded
    exact tendsto_modulated_pairing_of_hasLocalClassicalRepresentation (Tij i j) (aij i j) L
      (hTij i j) Cij hCij (haij i j).continuous_infrared ξ hξ
      (fun x => (haij i j).continuous_frequency x ξ hξ) (haij i j).degree_zero
      (F i) (G j) (hF i) (hG j) (hGL j)
  have hMixLimit := tendsto_finset_sum Finset.univ fun i _ =>
    tendsto_finset_sum Finset.univ fun j _ => hEach i j
  have hModPair (n : ℕ) :
      inner ℂ ((compactModulatedSchwartz ((n : ℝ) • ξ) f hfc).toLp 2 volume)
        (T ((compactModulatedSchwartz ((n : ℝ) • ξ) f hfc).toLp 2 volume)) =
      ∑ i, ∑ j, P i j n := by
    let k : E := (n : ℝ) • ξ
    let f' := compactModulatedSchwartz k f hfc
    have hc' := compactModulatedSchwartz_hasCompactSupport k f hfc
    have hs' := (compactModulatedSchwartz_tsupport k f hfc).trans hfL
    simpa only [P, F, G, f', k, compactWeightedSchwartz_modulated] using
      hPair f' f' hc' hc' hs' hs'
  have hMixed := tendsto_nhds_unique hTLimit (hMixLimit.congr fun n => (hModPair n).symm)
  have hI (i : I) (j : J) : Integrable (p i j) := by
    apply ((Complex.continuous_conj.comp (F i).continuous).mul
      (((haij i j).continuous_base ξ hξ).mul (G j).continuous)).integrable_of_hasCompactSupport
    exact ((hF i).comp_left (map_zero (starRingEnd ℂ))).mul_right
  have hMove : (∑ i, ∑ j, ∫ x, p i j x) = ∫ x, ∑ i, ∑ j, p i j x := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hI i j)]
    exact Finset.sum_congr rfl (fun i _ => (integral_finset_sum _ (fun j _ => hI i j)).symm)
  have hPoint (x : E) : (∑ i, ∑ j, p i j x) = conj (f x) * (b x * f x) := by
    calc
      _ = ∑ i, ∑ j, conj (f x) * ((conj (u i x) * aij i j x ξ * v j x) * f x) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [p, F, G, compactWeightedSchwartz_apply, map_mul]
        ring
      _ = _ := by simp only [b, Finset.mul_sum, Finset.sum_mul]
  rw [hMove, integral_congr_ae (Eventually.of_forall hPoint)] at hMixed
  change (∫ x, conj ((φ : E → ℝ) x : ℂ) * (a x ξ * ((φ : E → ℝ) x : ℂ))) =
    (∫ x, conj ((φ : E → ℝ) x : ℂ) * (b x * ((φ : E → ℝ) x : ℂ))) at hMixed
  simpa only [Complex.conj_ofReal] using hMixed

end Burnett.Microlocal.AtlasOverlapKernel
