import Burnett.Geometry.Cotangent.HamiltonianCoordinates

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.CotangentCauchyCrossing

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- An actual cotangent-bundle curve obeys the canonical Hamilton ODE in the specified true chart. -/
def IsHamiltonCurveInChart (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) : Prop :=
  (∀ t ∈ I, γ t ∈ cotangentSource c) ∧
    ∀ t ∈ I, HasDerivAt (fun s => cotangentChart c (γ s))
      (hamiltonVector (chartInverse g c) (cotangentChart c (γ t))) t

def scaledDomain (a : ℝ) (I : Set ℝ) : Set ℝ := {t | a * t ∈ I}

def scaledCurve (a : ℝ) (γ : ℝ → CotangentBundle M) (t : ℝ) : CotangentBundle M :=
  cotangentScale a (γ (a * t))

theorem scaledCurve_initial (a : ℝ) (γ : ℝ → CotangentBundle M) :
    scaledCurve a γ 0 = cotangentScale a (γ 0) := by simp [scaledCurve]

theorem scaledCurve_hamilton (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hγ : IsHamiltonCurveInChart g c γ I)
    {a : ℝ} (ha : 0 < a) :
    IsHamiltonCurveInChart g c (scaledCurve a γ) (scaledDomain a I) := by
  constructor
  · intro t ht
    exact hγ.1 (a * t) ht
  · intro t ht
    have htime : HasDerivAt (fun s : ℝ => a * s) a t := by simpa using (hasDerivAt_id t).const_mul a
    have h := (phaseScale a).hasFDerivAt.comp_hasDerivAt t ((hγ.2 (a * t) ht).scomp t htime)
    simpa only [scaledCurve, cotangentChart_scale, map_smul,
      hamiltonVector_scale _ _ ha.ne'] using h

theorem scaledCurve_at_div (γ : ℝ → CotangentBundle M) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    scaledCurve a γ (t / a) = cotangentScale a (γ t) := by
  have h : a * (t / a) = t := by field_simp
  unfold scaledCurve
  rw [h]

theorem scaledCurve_punctured (γ : ℝ → CotangentBundle M) (I : Set ℝ)
    (hγ : ∀ t ∈ I, γ t ∈ puncturedCotangent) {a : ℝ} (ha : 0 < a) :
    ∀ t ∈ scaledDomain a I, scaledCurve a γ t ∈ puncturedCotangent := by
  intro t ht
  exact smul_ne_zero ha.ne' (hγ (a * t) ht)

theorem scaledCurve_null (g : ManifoldBilinear.Field (M := M))
    (hgn : ManifoldBilinear.IsNondegenerate g) (γ : ℝ → CotangentBundle M) (I : Set ℝ)
    (hγ : ∀ t ∈ I, dualEnergy g hgn (γ t) = 0) (a : ℝ) :
    ∀ t ∈ scaledDomain a I, dualEnergy g hgn (scaledCurve a γ t) = 0 := by
  intro t ht
  rw [scaledCurve, dualEnergy_cotangentScale, hγ (a * t) ht, mul_zero]

/-- This is an orbit-segment crossing assertion, not a globally-hyperbolic existence axiom. -/
def UniqueCrossing (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M) : Prop :=
  ∃! t : ℝ, t ∈ I ∧ (γ t).1 ∈ S

def crossingTime (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) : ℝ := Classical.choose h.exists

theorem crossingTime_spec (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) : crossingTime S I γ h ∈ I ∧ (γ (crossingTime S I γ h)).1 ∈ S :=
  Classical.choose_spec h.exists

theorem crossingTime_unique (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) (t : ℝ) (ht : t ∈ I ∧ (γ t).1 ∈ S) :
    t = crossingTime S I γ h := h.unique ht (crossingTime_spec S I γ h)

theorem scaled_uniqueCrossing (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) {a : ℝ} (ha : 0 < a) :
    UniqueCrossing S (scaledDomain a I) (scaledCurve a γ) := by
  let t₀ := crossingTime S I γ h
  have ht₀ := crossingTime_spec S I γ h
  have he : a * (t₀ / a) = t₀ := by field_simp
  refine ⟨t₀ / a, ?_, ?_⟩
  · change a * (t₀ / a) ∈ I ∧ (γ (a * (t₀ / a))).1 ∈ S
    rw [he]
    exact ht₀
  · intro t ht
    have heq : a * t = t₀ := h.unique ht ht₀
    apply (eq_div_iff ha.ne').mpr
    nlinarith

theorem scaled_crossingTime (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) {a : ℝ} (ha : 0 < a) :
    crossingTime S (scaledDomain a I) (scaledCurve a γ) (scaled_uniqueCrossing S I γ h ha) =
      crossingTime S I γ h / a := by
  apply (crossingTime_unique S (scaledDomain a I) (scaledCurve a γ)
    (scaled_uniqueCrossing S I γ h ha) (crossingTime S I γ h / a) ?_).symm
  have he : a * (crossingTime S I γ h / a) = crossingTime S I γ h := by field_simp
  change a * (crossingTime S I γ h / a) ∈ I ∧
    (γ (a * (crossingTime S I γ h / a))).1 ∈ S
  rw [he]
  exact crossingTime_spec S I γ h

def crossingEnergy (r : Metric (M := M)) (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) : ℝ := cotangentNorm r (γ (crossingTime S I γ h))

theorem crossingEnergy_pos (r : Metric (M := M)) (S : Set M) (I : Set ℝ)
    (γ : ℝ → CotangentBundle M) (h : UniqueCrossing S I γ)
    (hpunct : ∀ t ∈ I, γ t ∈ puncturedCotangent) : 0 < crossingEnergy r S I γ h :=
  cotangentNorm_pos r (hpunct _ (crossingTime_spec S I γ h).1)

theorem scaled_crossingEnergy (r : Metric (M := M)) (S : Set M) (I : Set ℝ)
    (γ : ℝ → CotangentBundle M) (h : UniqueCrossing S I γ) {a : ℝ} (ha : 0 < a) :
    crossingEnergy r S (scaledDomain a I) (scaledCurve a γ) (scaled_uniqueCrossing S I γ h ha) =
      a * crossingEnergy r S I γ h := by
  unfold crossingEnergy
  rw [scaled_crossingTime S I γ h ha, scaledCurve_at_div γ ha.ne', cotangentNorm_scale r _ ha]

end Burnett.Geometry.CotangentCauchyCrossing

namespace Burnett.Geometry.CotangentCauchyCrossing

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentHamiltonNaturality Burnett.Geometry.CotangentSymplecticTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The actual-curve Hamilton equation is independent of the true cotangent chart. -/
theorem hamiltonCurve_chart_change (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c d : M) (γ : ℝ → CotangentBundle M)
    (I : Set ℝ) (hI : IsOpen I) (hγ : IsHamiltonCurveInChart g c γ I)
    (hd : ∀ t ∈ I, γ t ∈ cotangentSource d) : IsHamiltonCurveInChart g d γ I := by
  refine ⟨hd, ?_⟩
  intro t ht
  have hz := chart_mem_transitionSource c d (γ t) (hγ.1 t ht) (hd t ht)
  have hD : DifferentiableAt ℝ (cotangentTransition c d) (cotangentChart c (γ t)) :=
    ((cotangentTransition_contDiffOn c d).contDiffAt
      ((transitionSource_isOpen c d).mem_nhds hz)).differentiableAt (by simp)
  have h := hD.hasFDerivAt.comp_hasDerivAt t (hγ.2 t ht)
  have he : (fun s => cotangentChart d (γ s)) =ᶠ[𝓝 t]
      (cotangentTransition c d ∘ fun s => cotangentChart c (γ s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (cotangentTransition_chart c d (γ s) (hγ.1 s hs)).symm
  have hh := h.congr_of_eventuallyEq he
  rw [actual_hamiltonVector_chart_compatible g hg hgn hgs c d (γ t) (hγ.1 t ht) (hd t ht)] at hh
  exact hh

end Burnett.Geometry.CotangentCauchyCrossing

namespace Burnett.Geometry.CotangentCauchyCrossing

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def shiftedDomain (b : ℝ) (I : Set ℝ) : Set ℝ := {t | t + b ∈ I}

def shiftedCurve (b : ℝ) (γ : ℝ → CotangentBundle M) (t : ℝ) : CotangentBundle M := γ (t + b)

theorem shiftedCurve_hamilton (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hγ : IsHamiltonCurveInChart g c γ I) (b : ℝ) :
    IsHamiltonCurveInChart g c (shiftedCurve b γ) (shiftedDomain b I) := by
  refine ⟨fun t ht => hγ.1 (t + b) ht, ?_⟩
  intro t ht
  have htime : HasDerivAt (fun s : ℝ => s + b) 1 t := (hasDerivAt_id t).add_const b
  have h := (hγ.2 (t + b) ht).scomp t htime
  simpa only [shiftedCurve, one_smul, Function.comp_def] using h

theorem shifted_uniqueCrossing (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) (b : ℝ) :
    UniqueCrossing S (shiftedDomain b I) (shiftedCurve b γ) := by
  let t₀ := crossingTime S I γ h
  have ht₀ := crossingTime_spec S I γ h
  refine ⟨t₀ - b, ?_, ?_⟩
  · change t₀ - b + b ∈ I ∧ (γ (t₀ - b + b)).1 ∈ S
    simpa only [sub_add_cancel] using ht₀
  · intro t ht
    have he : t + b = t₀ := h.unique ht ht₀
    linarith

theorem shifted_crossingTime (S : Set M) (I : Set ℝ) (γ : ℝ → CotangentBundle M)
    (h : UniqueCrossing S I γ) (b : ℝ) :
    crossingTime S (shiftedDomain b I) (shiftedCurve b γ) (shifted_uniqueCrossing S I γ h b) =
      crossingTime S I γ h - b := by
  apply (crossingTime_unique S (shiftedDomain b I) (shiftedCurve b γ)
    (shifted_uniqueCrossing S I γ h b) (crossingTime S I γ h - b) ?_).symm
  change crossingTime S I γ h - b + b ∈ I ∧
    (γ (crossingTime S I γ h - b + b)).1 ∈ S
  simpa only [sub_add_cancel] using crossingTime_spec S I γ h

/-- Changing the initial parameter on the same actual orbit segment leaves its crossing energy unchanged. -/
theorem shifted_crossingEnergy (r : Metric (M := M)) (S : Set M) (I : Set ℝ)
    (γ : ℝ → CotangentBundle M) (h : UniqueCrossing S I γ) (b : ℝ) :
    crossingEnergy r S (shiftedDomain b I) (shiftedCurve b γ) (shifted_uniqueCrossing S I γ h b) =
      crossingEnergy r S I γ h := by
  unfold crossingEnergy
  rw [shifted_crossingTime S I γ h b]
  simp only [shiftedCurve, sub_add_cancel]

end Burnett.Geometry.CotangentCauchyCrossing

namespace Burnett.Geometry.CotangentCauchyCrossing

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The chart ODE is realized by the actual manifold derivative of the actual cotangent curve. -/
theorem hamiltonCurve_actual_derivative (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) (t : ℝ) (ht : t ∈ I) :
    HasMFDerivAt 𝓘(ℝ) CotangentModelWithCorners γ t
      ((mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c)
        (cotangentChart c (γ t))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (hamiltonVector (chartInverse g c) (cotangentChart c (γ t))))) := by
  have hf : HasMFDerivAt 𝓘(ℝ) CoordinatePhaseModel (fun s => cotangentChart c (γ s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (hamiltonVector (chartInverse g c) (cotangentChart c (γ t)))) := by
    have h := (hγ.2 t ht).hasFDerivAt.hasMFDerivAt
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hi : MDifferentiableAt CoordinatePhaseModel CotangentModelWithCorners
      (cotangentChartInverse c) (cotangentChart c (γ t)) :=
    ((contMDiffOn_cotangentChartInverse c).contMDiffAt
      ((isOpen_phaseTarget c).mem_nhds (cotangentChart_mapsTo c (hγ.1 t ht)))).mdifferentiableAt (by simp)
  have h := hi.hasMFDerivAt.comp t hf
  have he : γ =ᶠ[𝓝 t] (cotangentChartInverse c ∘ fun s => cotangentChart c (γ s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (cotangentChart_left_inv c (hγ.1 s hs)).symm
  exact h.congr_of_eventuallyEq he

end Burnett.Geometry.CotangentCauchyCrossing

namespace Burnett.Geometry.CotangentCrossingTransversality

open Set Filter Bundle Module
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

theorem momentumPartial_coordinateP (G : CoordinateSpace → Tensor2) (p : Phase)
    (hG : IsSymmetricTensor (G p.1)) (i : Index) :
    momentumPartial (coordinateP G) p i = raiseCovector (G p.1) p.2 i := by
  let e : Covector := Pi.single i 1
  have he : HasDerivAt (fun t : ℝ => p.2 + t • e) e 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p.2
  have hc := (contDiff_coordinateP_momentum G p.1).differentiable (by simp)
  have hf : HasFDerivAt (fun ξ => coordinateP G (p.1,ξ))
      (fderiv ℝ (fun ξ => coordinateP G (p.1,ξ)) p.2) (p.2 + (0 : ℝ) • e) := by
    simpa using (hc p.2).hasFDerivAt
  have hd := hf.comp_hasDerivAt (0 : ℝ) he
  have hfun : (fun t : ℝ => coordinateP G (p.1, p.2 + t • e)) =
      fun t => (dualPair (G p.1) p.2 p.2 +
        2 * dualPair (G p.1) p.2 e * t + dualPair (G p.1) e e * t^2) / 2 := by
    funext t
    simp only [coordinateP, ← dualPair_self, dualPair_add_smul_self _ hG]
  have hp : HasDerivAt (fun t : ℝ =>
      (dualPair (G p.1) p.2 p.2 + 2 * dualPair (G p.1) p.2 e * t +
        dualPair (G p.1) e e * t^2) / 2) (dualPair (G p.1) p.2 e) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (dualPair (G p.1) p.2 p.2)).add
      ((hasDerivAt_id (0 : ℝ)).const_mul (2 * dualPair (G p.1) p.2 e))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (dualPair (G p.1) e e))).div_const 2 using 1; norm_num
  change HasDerivAt (fun t : ℝ => coordinateP G (p.1, p.2 + t • e))
    (fderiv ℝ (fun ξ => coordinateP G (p.1,ξ)) p.2 e) 0 at hd
  rw [hfun] at hd
  have hh := hd.unique hp
  change fderiv ℝ (fun ξ => coordinateP G (p.1,ξ)) p.2 e = _
  rw [hh, dualPair_symm _ hG, dualPair_apply]
  simp [e, raiseCovector, Pi.single_apply]

theorem hamiltonVector_fst_eq_raise (G : CoordinateSpace → Tensor2) (p : Phase)
    (hG : IsSymmetricTensor (G p.1)) :
    (hamiltonVector G p).1 = WithLp.toLp 2 (raiseCovector (G p.1) p.2) := by
  apply congrArg (WithLp.toLp 2)
  funext i
  exact momentumPartial_coordinateP G p hG i

theorem inverse_raise_lower (B : LinearMap.BilinForm ℝ CoordinateSpace)
    (hn : B.Nondegenerate) (hs : B.IsSymm) (ξ : Covector) (v : CoordinateSpace) :
    B (WithLp.toLp 2 (raiseCovector
      (InverseField.matrixInverse (FiberMetric.covariant B coordinateBasis)) ξ)) v =
      covectorCLM ξ v := by
  have hξ : FiberMetric.covector coordinateBasis (covectorCLM ξ).toLinearMap = ξ := by
    funext i
    exact covectorCLM_apply_basis ξ i
  have h := FiberMetric.raiseCovector_eq_sharp B hn coordinateBasis (covectorCLM ξ).toLinearMap
  rw [← InverseField.matrixInverse_covariant B hn hs coordinateBasis, hξ] at h
  have hv : WithLp.toLp 2 (FiberMetric.vector coordinateBasis
      (FiberMetric.sharp B hn coordinateBasis (covectorCLM ξ).toLinearMap)) =
      FiberMetric.sharp B hn coordinateBasis (covectorCLM ξ).toLinearMap := by
    ext i
    rfl
  rw [h, hv]
  exact FiberMetric.sharp_lower B hn coordinateBasis (covectorCLM ξ).toLinearMap v

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The coordinate canonical Hamilton base velocity, transported to the actual tangent fiber. -/
def projectedHamilton (g : ManifoldBilinear.Field (M := M)) (c : M) (p : CotangentBundle M) :
    TangentSpace Model p.1 :=
  tangentFrame c p.1 (hamiltonVector (chartInverse g c) (cotangentChart c p)).1

theorem covectorCLM_eval (ξ : Covector) (v : CoordinateSpace) :
    covectorCLM ξ v = ∑ i, ξ i * v i := by
  simp only [covectorCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

theorem cotangentCoords_eval (c : M) (p : CotangentBundle M) (v : CoordinateSpace) :
    covectorCLM (cotangentCoords c p) v = p.2 (tangentFrame c p.1 v) := by
  rw [← cotangentTrivialization_apply c p v]
  rw [covectorCLM_eval]
  exact CotangentHamiltonNaturality.coordinatePairing_eq_actual c p v

/-- This is the actual metric-dual identity, not an assumed Hamilton transformation rule. -/
theorem projectedHamilton_lower (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c)
    (U : TangentSpace Model p.1) : g p.1 (projectedHamilton g c p) U = p.2 U := by
  obtain ⟨v, rfl⟩ := ManifoldBilinear.tangentFrame_surjective c p.1 hp U
  have hnB := ManifoldBilinear.coordinateBilinear_nondegenerate g hn c
    ((chartAt CoordinateSpace c).mapsTo hp)
  have hsB := ManifoldBilinear.coordinateBilinear_symmetric g hs c
    (chartAt CoordinateSpace c p.1)
  have he := inverse_raise_lower (coordinateBilinear g c (chartAt CoordinateSpace c p.1))
    hnB hsB (cotangentCoords c p) v
  rw [cotangentCoords_eval] at he
  unfold projectedHamilton
  rw [hamiltonVector_fst_eq_raise _ _ (chartInverse_symm g hs c _)]
  change g ((chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c p.1))
    (tangentFrame c ((chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c p.1))
      (WithLp.toLp 2 (raiseCovector (chartInverse g c (chartAt CoordinateSpace c p.1))
        (cotangentCoords c p))))
    (tangentFrame c ((chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c p.1)) v) = _ at he
  rw [(chartAt CoordinateSpace c).left_inv hp] at he
  exact he

theorem projectedHamilton_ne_zero (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c)
    (hpun : p ∈ puncturedCotangent) : projectedHamilton g c p ≠ 0 := by
  intro hz
  apply hpun
  ext U
  have he := projectedHamilton_lower g hn hs c p hp U
  rw [hz] at he
  simpa using he.symm

theorem projectedHamilton_self (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c) :
    g p.1 (projectedHamilton g c p) (projectedHamilton g c p) = dualEnergy g hn p := by
  rw [projectedHamilton_lower g hn hs c p hp,
    dualEnergy_chart g hn hs c p hp]
  unfold projectedHamilton
  rw [← cotangentCoords_eval, hamiltonVector_fst_eq_raise _ _ (chartInverse_symm g hs c _)]
  rw [covectorCLM_eval]
  change (∑ i, cotangentCoords c p i * raiseCovector _ (cotangentCoords c p) i) = _
  simp only [raiseCovector, symbolNorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [chartInverse, cotangentChart]
  ring

/-- Positivity of the actual metric on the tangent kernel of a local defining function. -/
def SpacelikeLevelAt (g : ManifoldBilinear.Field (M := M)) (f : M → ℝ) (m : M) : Prop :=
  ∀ v : TangentSpace Model m, mfderiv Model 𝓘(ℝ) f m v = 0 → v ≠ 0 → 0 < g m v v

theorem projectedHamilton_transverse (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c)
    (hpun : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (f : M → ℝ) (hS : SpacelikeLevelAt g f p.1) :
    mfderiv Model 𝓘(ℝ) f p.1 (projectedHamilton g c p) ≠ 0 := by
  intro hz
  have hpos := hS _ hz (projectedHamilton_ne_zero g hn hs c p hp hpun)
  rw [projectedHamilton_self g hn hs c p hp, hnull] at hpos
  exact (lt_irrefl 0) hpos

theorem projectedHamilton_chart_independent (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c d : M) (p : CotangentBundle M)
    (hc : p ∈ cotangentSource c) (hd : p ∈ cotangentSource d) :
    projectedHamilton g c p = projectedHamilton g d p := by
  apply sub_eq_zero.mp
  apply hn p.1
  intro U
  simp only [map_sub, ContinuousLinearMap.sub_apply,
    projectedHamilton_lower g hn hs c p hc U, projectedHamilton_lower g hn hs d p hd U, sub_self]

theorem level_differential_surjective (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c)
    (hpun : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (f : M → ℝ) (hS : SpacelikeLevelAt g f p.1) :
    Function.Surjective (mfderiv Model 𝓘(ℝ) f p.1) := by
  have he := projectedHamilton_transverse g hn hs c p hp hpun hnull f hS
  intro z
  change ℝ at z
  let D : ℝ := mfderiv Model 𝓘(ℝ) f p.1 (projectedHamilton g c p)
  refine ⟨(z / D) •
    projectedHamilton g c p, ?_⟩
  rw [map_smul]
  change (z / D) * D = z
  exact div_mul_cancel₀ z he

end Burnett.Geometry.CotangentCrossingTransversality

namespace Burnett.Geometry.CotangentCrossingTransversality

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Transport the actual canonical Hamilton vector by the true cotangent chart inverse derivative. -/
def intrinsicHamilton (g : ManifoldBilinear.Field (M := M)) (c : M) (p : CotangentBundle M) :
    TangentSpace CotangentModelWithCorners p :=
  mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c)
    (cotangentChart c p) (hamiltonVector (chartInverse g c) (cotangentChart c p))

theorem mfderiv_projection_inverse (c : M) (p : CotangentBundle M)
    (hp : p ∈ cotangentSource c) (V : Phase) :
    mfderiv CotangentModelWithCorners Model (fun q : CotangentBundle M => q.1) p
      (mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c)
        (cotangentChart c p) V) = tangentFrame c p.1 V.1 := by
  have hπ : MDifferentiableAt CotangentModelWithCorners Model
      (fun q : CotangentBundle M => q.1) p :=
    (contMDiffAt_proj (𝕜 := ℝ) (IB := Model) (n := ∞) (CotangentFiber (M := M))).mdifferentiableAt (by simp)
  have hi : MDifferentiableAt CoordinatePhaseModel CotangentModelWithCorners
      (cotangentChartInverse c) (cotangentChart c p) :=
    ((contMDiffOn_cotangentChartInverse c).contMDiffAt
      ((isOpen_phaseTarget c).mem_nhds (cotangentChart_mapsTo c hp))).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_apply_of_eq (cotangentChart c p) hπ hi (cotangentChart_left_inv c hp) V
  have hσ := (mdifferentiable_chart (I := Model) c).mdifferentiableAt_symm
    ((chartAt CoordinateSpace c).mapsTo hp)
  have hfst : MDifferentiableAt CoordinatePhaseModel Model
      (Prod.fst : Phase → CoordinateSpace) (cotangentChart c p) := mdifferentiableAt_fst
  have hs := mfderiv_comp_apply (cotangentChart c p) hσ hfst V
  rw [mfderiv_fst] at hs
  change mfderiv CoordinatePhaseModel Model
    ((chartAt CoordinateSpace c).symm ∘ (Prod.fst : Phase → CoordinateSpace)) (cotangentChart c p) V =
      mfderiv Model Model (chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c p.1) V.1 at hs
  rw [← ChartDifferential.tangentFrame_eq_mfderiv_symm c p.1 hp] at hs
  exact hcomp.symm.trans hs

theorem intrinsicHamilton_projection (g : ManifoldBilinear.Field (M := M))
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c) :
    mfderiv CotangentModelWithCorners Model (fun q : CotangentBundle M => q.1) p
      (intrinsicHamilton g c p) = projectedHamilton g c p :=
  mfderiv_projection_inverse c p hp _

theorem intrinsicHamilton_transverse (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c)
    (hpun : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (f : M → ℝ) (hS : SpacelikeLevelAt g f p.1) :
    mfderiv Model 𝓘(ℝ) f p.1
      (mfderiv CotangentModelWithCorners Model (fun q : CotangentBundle M => q.1) p
        (intrinsicHamilton g c p)) ≠ 0 := by
  rw [intrinsicHamilton_projection g c p hp]
  exact projectedHamilton_transverse g hn hs c p hp hpun hnull f hS

end Burnett.Geometry.CotangentCrossingTransversality

namespace Burnett.Geometry.CotangentCrossingTransversality

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

set_option synthInstance.maxHeartbeats 200000 in
/-- Actual canonical curves have the computed actual metric-dual base velocity. -/
theorem hamiltonCurve_projected_derivative (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) (t : ℝ) (ht : t ∈ I) :
    HasMFDerivAt 𝓘(ℝ) Model (fun s => (γ s).1) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (projectedHamilton g c (γ t))) := by
  have hcurve := hamiltonCurve_actual_derivative g c γ I hI hγ t ht
  have hπ : MDifferentiableAt CotangentModelWithCorners Model
      (fun q : CotangentBundle M => q.1) (γ t) :=
    (contMDiffAt_proj (𝕜 := ℝ) (IB := Model) (n := ∞) (CotangentFiber (M := M))).mdifferentiableAt (by simp)
  have h := hπ.hasMFDerivAt.comp t hcurve
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv CotangentModelWithCorners Model (fun q : CotangentBundle M => q.1) (γ t)
    (mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c)
      (cotangentChart c (γ t)) (a • hamiltonVector (chartInverse g c) (cotangentChart c (γ t)))) =
        a • projectedHamilton g c (γ t)
  rw [map_smul, map_smul, mfderiv_projection_inverse c (γ t) (hγ.1 t ht)]
  rfl

theorem hamiltonCurve_level_derivative (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) (t : ℝ) (ht : t ∈ I)
    (f : M → ℝ) (hf : MDifferentiableAt Model 𝓘(ℝ) f (γ t).1) :
    HasDerivAt (fun s => f (γ s).1)
      (mfderiv Model 𝓘(ℝ) f (γ t).1 (projectedHamilton g c (γ t))) t := by
  have h := hf.hasMFDerivAt.comp t
    (hamiltonCurve_projected_derivative g c γ I hI hγ t ht)
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv Model 𝓘(ℝ) f (γ t).1 (a • projectedHamilton g c (γ t)) =
    a • mfderiv Model 𝓘(ℝ) f (γ t).1 (projectedHamilton g c (γ t))
  exact map_smul _ _ _

/-- A genuine smooth defining function crosses zero in an isolated actual Hamilton event. -/
theorem hamilton_crossing_isolated (g : ManifoldBilinear.Field (M := M))
    (hn : ManifoldBilinear.IsNondegenerate g) (hs : ManifoldBilinear.IsSymmetric g)
    (c : M) (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) (t : ℝ) (ht : t ∈ I)
    (hpun : γ t ∈ puncturedCotangent) (hnull : dualEnergy g hn (γ t) = 0)
    (f : M → ℝ) (hf : ContMDiffAt Model 𝓘(ℝ) ∞ f (γ t).1)
    (hS : SpacelikeLevelAt g f (γ t).1) (hcross : f (γ t).1 = 0) :
    f (γ t).1 = 0 ∧ ∀ᶠ s in 𝓝[≠] t, f (γ s).1 ≠ 0 := by
  refine ⟨hcross, ?_⟩
  have hd := hamiltonCurve_level_derivative g c γ I hI hγ t ht f
    (hf.mdifferentiableAt (by simp))
  exact hd.eventually_ne (projectedHamilton_transverse g hn hs c (γ t) (hγ.1 t ht)
    hpun hnull f hS)

end Burnett.Geometry.CotangentCrossingTransversality

namespace Burnett.Geometry.CotangentHamiltonLocalFlow

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem cotangentChart_mem_punctured (c : M) (p : CotangentBundle M)
    (hp : p ∈ cotangentSource c) (hpun : p ∈ puncturedCotangent) :
    cotangentChart c p ∈ puncturedPhaseTarget c := by
  refine ⟨cotangentChart_mapsTo c hp, ?_⟩
  intro hξ
  change cotangentCoords c p = 0 at hξ
  apply hpun
  ext U
  obtain ⟨v,rfl⟩ := ManifoldBilinear.tangentFrame_surjective c p.1 hp U
  rw [← cotangentCoords_eval, hξ]
  simp [covectorCLM]

theorem phase_integralCurveAt_iff (H : Phase → Phase) (η : ℝ → Phase) (t₀ : ℝ) :
    IsMIntegralCurveAt (I := 𝓘(ℝ, Phase)) η (fun z => H z) t₀ ↔
      ∀ᶠ t in 𝓝 t₀, HasDerivAt η (H (η t)) t := by
  simp only [IsMIntegralCurveAt, hasDerivAt_iff_hasFDerivAt, hasMFDerivAt_iff_hasFDerivAt]

/-- Apply the actual manifold local-existence theorem to the smooth canonical chart vector field. -/
theorem exists_phase_hamiltonCurve (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (c : M) (z₀ : Phase) (hz₀ : z₀ ∈ puncturedPhaseTarget c) :
    ∃ δ > (0 : ℝ), ∃ η : ℝ → Phase, η 0 = z₀ ∧
      ∀ t ∈ Ioo (-δ) δ, η t ∈ puncturedPhaseTarget c ∧
        HasDerivAt η (hamiltonVector (chartInverse g c) (η t)) t := by
  let H := hamiltonVector (chartInverse g c)
  have hH : ContDiffAt ℝ 1 H z₀ :=
    ((contDiffOn_hamiltonVector_chartInverse g hg hn c).contDiffAt
      ((isOpen_phaseTarget c).mem_nhds hz₀.1)).of_le (by norm_num)
  have hv : ContMDiffAt 𝓘(ℝ, Phase) 𝓘(ℝ, Phase).tangent 1
      (fun z => (⟨z,H z⟩ : TangentBundle 𝓘(ℝ, Phase) Phase)) z₀ :=
    (contMDiffAt_vectorSpace_iff_contDiffAt (V := fun z => H z)).mpr hH
  obtain ⟨η,hη₀,hη⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := 𝓘(ℝ, Phase)) (v := fun z => H z) (x₀ := z₀) (0 : ℝ) hv
  have hODE := (phase_integralCurveAt_iff H η 0).mp hη
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), η t ∈ puncturedPhaseTarget c :=
    hη.continuousAt.preimage_mem_nhds ((isOpen_puncturedPhaseTarget c).mem_nhds (hη₀.symm ▸ hz₀))
  obtain ⟨δ,hδ,hgood⟩ := Metric.eventually_nhds_iff_ball.mp (hmem.and hODE)
  refine ⟨δ,hδ,η,hη₀,fun t ht => hgood t ?_⟩
  simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using ht

theorem chartInverse_hamiltonCurve (g : ManifoldBilinear.Field (M := M)) (c : M)
    (η : ℝ → Phase) (I : Set ℝ) (hI : IsOpen I)
    (hmem : ∀ t ∈ I, η t ∈ phaseTarget c)
    (hODE : ∀ t ∈ I, HasDerivAt η (hamiltonVector (chartInverse g c) (η t)) t) :
    IsHamiltonCurveInChart g c (cotangentChartInverse c ∘ η) I := by
  refine ⟨fun t ht => cotangentChartInverse_mapsTo c (hmem t ht), ?_⟩
  intro t ht
  have he : (fun s => cotangentChart c ((cotangentChartInverse c ∘ η) s)) =ᶠ[𝓝 t] η := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact cotangentChart_right_inv c (hmem s hs)
  rw [Function.comp_apply, cotangentChart_right_inv c (hmem t ht)]
  exact (hODE t ht).congr_of_eventuallyEq he

/-- No local-flow or global-vector-field existence premise is supplied here. -/
theorem exists_local_actual_hamiltonCurve (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (c : M) (p : CotangentBundle M) (hp : p ∈ cotangentSource c)
    (hpun : p ∈ puncturedCotangent) :
    ∃ δ > (0 : ℝ), ∃ γ : ℝ → CotangentBundle M, γ 0 = p ∧
      IsHamiltonCurveInChart g c γ (Ioo (-δ) δ) ∧
      ∀ t ∈ Ioo (-δ) δ, γ t ∈ puncturedCotangent := by
  obtain ⟨δ,hδ,η,hη₀,hη⟩ := exists_phase_hamiltonCurve g hg hn c
    (cotangentChart c p) (cotangentChart_mem_punctured c p hp hpun)
  refine ⟨δ,hδ,cotangentChartInverse c ∘ η,?_,?_,?_⟩
  · rw [Function.comp_apply, hη₀, cotangentChart_left_inv c hp]
  · exact chartInverse_hamiltonCurve g c η _ isOpen_Ioo
      (fun t ht => (hη t ht).1.1) (fun t ht => (hη t ht).2)
  · exact fun t ht => cotangentChartInverse_mem_punctured (hη t ht).1

end Burnett.Geometry.CotangentHamiltonLocalFlow

namespace Burnett.Geometry.CotangentHamiltonLocalFlow

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem hamiltonCurve_phase_integralAt (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) (t₀ : ℝ) (ht₀ : t₀ ∈ I) :
    IsMIntegralCurveAt (I := 𝓘(ℝ, Phase)) (cotangentChart c ∘ γ)
      (fun z => hamiltonVector (chartInverse g c) z) t₀ := by
  rw [phase_integralCurveAt_iff]
  filter_upwards [hI.mem_nhds ht₀] with t ht
  exact hγ.2 t ht

theorem actual_hamiltonCurve_unique_germ (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (c : M) (γ ζ : ℝ → CotangentBundle M) (I J : Set ℝ)
    (hI : IsOpen I) (hJ : IsOpen J)
    (hγ : IsHamiltonCurveInChart g c γ I) (hζ : IsHamiltonCurveInChart g c ζ J)
    (t₀ : ℝ) (htI : t₀ ∈ I) (htJ : t₀ ∈ J) (hinit : γ t₀ = ζ t₀) :
    γ =ᶠ[𝓝 t₀] ζ := by
  let H := hamiltonVector (chartInverse g c)
  have hH : ContDiffAt ℝ 1 H (cotangentChart c (γ t₀)) :=
    ((contDiffOn_hamiltonVector_chartInverse g hg hn c).contDiffAt
      ((isOpen_phaseTarget c).mem_nhds (cotangentChart_mapsTo c (hγ.1 t₀ htI)))).of_le (by norm_num)
  have hv : ContMDiffAt 𝓘(ℝ, Phase) 𝓘(ℝ, Phase).tangent 1
      (fun z => (⟨z,H z⟩ : TangentBundle 𝓘(ℝ, Phase) Phase)) (cotangentChart c (γ t₀)) :=
    (contMDiffAt_vectorSpace_iff_contDiffAt (V := fun z => H z)).mpr hH
  have hphase := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hv
    (hamiltonCurve_phase_integralAt g c γ I hI hγ t₀ htI)
    (hamiltonCurve_phase_integralAt g c ζ J hJ hζ t₀ htJ)
    (congrArg (cotangentChart c) hinit)
  filter_upwards [hphase,hI.mem_nhds htI,hJ.mem_nhds htJ] with t he htI' htJ'
  calc
    γ t = cotangentChartInverse c (cotangentChart c (γ t)) :=
      (cotangentChart_left_inv c (hγ.1 t htI')).symm
    _ = cotangentChartInverse c (cotangentChart c (ζ t)) := congrArg (cotangentChartInverse c) he
    _ = ζ t := cotangentChart_left_inv c (hζ.1 t htJ')

set_option synthInstance.maxHeartbeats 200000 in
/-- The genuine chart ODE is an actual integral curve equation on the true cotangent bundle. -/
theorem hamiltonCurve_actual_integralOn (g : ManifoldBilinear.Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) :
    IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (fun p => intrinsicHamilton g c p) I := by
  intro t ht
  have hd := hamiltonCurve_actual_derivative g c γ I hI hγ t ht
  refine (hd.congr_mfderiv ?_).hasMFDerivWithinAt
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c)
    (cotangentChart c (γ t)) (a • hamiltonVector (chartInverse g c) (cotangentChart c (γ t))) =
      a • intrinsicHamilton g c (γ t)
  rw [map_smul]
  rfl

end Burnett.Geometry.CotangentHamiltonLocalFlow

namespace Burnett.Geometry.CotangentHamiltonLocalFlow

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem coordinateP_curve_derivative_zero (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (c : M) (γ : ℝ → CotangentBundle M) (I : Set ℝ)
    (hγ : IsHamiltonCurveInChart g c γ I) (t : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => coordinateP (chartInverse g c) (cotangentChart c (γ s))) 0 t := by
  have hP : DifferentiableAt ℝ (coordinateP (chartInverse g c)) (cotangentChart c (γ t)) :=
    ((contDiffOn_coordinateP_chartInverse g hg hn c).contDiffAt
      ((isOpen_phaseTarget c).mem_nhds (cotangentChart_mapsTo c (hγ.1 t ht)))).differentiableAt (by simp)
  have hd := hP.hasFDerivAt.comp_hasDerivAt t (hγ.2 t ht)
  rw [fderiv_coordinateP_apply_hamiltonVector _ hP] at hd
  exact hd

theorem dualEnergy_constant_on_hamiltonCurve (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c : M) (γ : ℝ → CotangentBundle M)
    (I : Set ℝ) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : IsHamiltonCurveInChart g c γ I) (s t : ℝ) (hsI : s ∈ I) (htI : t ∈ I) :
    dualEnergy g hn (γ s) = dualEnergy g hn (γ t) := by
  let F : ℝ → ℝ := fun u => coordinateP (chartInverse g c) (cotangentChart c (γ u))
  have hD (u : ℝ) (hu : u ∈ I) : HasDerivAt F 0 u :=
    coordinateP_curve_derivative_zero g hg hn c γ I hγ u hu
  have hd : DifferentiableOn ℝ F I := fun u hu => (hD u hu).differentiableAt.differentiableWithinAt
  have hz : I.EqOn (deriv F) 0 := fun u hu => (hD u hu).deriv
  have he := hI.is_const_of_deriv_eq_zero hconn hd hz hsI htI
  change coordinateP (chartInverse g c) (cotangentChart c (γ s)) =
    coordinateP (chartInverse g c) (cotangentChart c (γ t)) at he
  rw [coordinateP_cotangentChart g hn hs c (hγ.1 s hsI),
    coordinateP_cotangentChart g hn hs c (hγ.1 t htI)] at he
  linarith

/-- From the original smooth metric and an actual nonzero null point, produce a true local null orbit. -/
theorem exists_local_null_actual_hamiltonCurve (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c : M) (p : CotangentBundle M)
    (hp : p ∈ cotangentSource c) (hpun : p ∈ puncturedCotangent)
    (hnull : dualEnergy g hn p = 0) :
    ∃ δ > (0 : ℝ), ∃ γ : ℝ → CotangentBundle M, γ 0 = p ∧
      IsHamiltonCurveInChart g c γ (Ioo (-δ) δ) ∧
      IsMIntegralCurveOn (I := CotangentModelWithCorners) γ
        (fun q => intrinsicHamilton g c q) (Ioo (-δ) δ) ∧
      ∀ t ∈ Ioo (-δ) δ, γ t ∈ puncturedCotangent ∧ dualEnergy g hn (γ t) = 0 := by
  obtain ⟨δ,hδ,γ,hγ₀,hγ,hpunγ⟩ := exists_local_actual_hamiltonCurve g hg hn c p hp hpun
  refine ⟨δ,hδ,γ,hγ₀,hγ,hamiltonCurve_actual_integralOn g c γ _ isOpen_Ioo hγ,?_
    ⟩
  intro t ht
  refine ⟨hpunγ t ht,?_⟩
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  rw [dualEnergy_constant_on_hamiltonCurve g hg hn hs c γ _ isOpen_Ioo
    isPreconnected_Ioo hγ t 0 ht hzero, hγ₀]
  exact hnull

end Burnett.Geometry.CotangentHamiltonLocalFlow

namespace Burnett.Geometry.CotangentHamiltonLocalFlow

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem exists_hamiltonCurve_chart_overlap (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c d : M) (γ : ℝ → CotangentBundle M)
    (I : Set ℝ) (hI : IsOpen I) (hγ : IsHamiltonCurveInChart g c γ I)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (hd₀ : γ t₀ ∈ cotangentSource d) :
    ∃ K : Set ℝ, IsOpen K ∧ t₀ ∈ K ∧ K ⊆ I ∧ IsHamiltonCurveInChart g d γ K := by
  have hcγ := (hamiltonCurve_actual_derivative g c γ I hI hγ t₀ ht₀).continuousAt
  have hmem : γ ⁻¹' cotangentSource d ∈ 𝓝 t₀ :=
    hcγ.preimage_mem_nhds ((isOpen_cotangentSource d).mem_nhds hd₀)
  let K := I ∩ interior (γ ⁻¹' cotangentSource d)
  have hK : IsOpen K := hI.inter isOpen_interior
  have htK : t₀ ∈ K := ⟨ht₀,mem_interior_iff_mem_nhds.mpr hmem⟩
  have hγK : IsHamiltonCurveInChart g c γ K :=
    ⟨fun t ht => hγ.1 t ht.1, fun t ht => hγ.2 t ht.1⟩
  refine ⟨K,hK,htK,inter_subset_left,?_⟩
  apply hamiltonCurve_chart_change g hg hn hs c d γ K hK hγK
  intro t ht
  have hm : t ∈ γ ⁻¹' cotangentSource d := interior_subset ht.2
  exact hm

set_option synthInstance.maxHeartbeats 200000 in
/-- Genuine manifold derivative uniqueness identifies both chart representatives on a nonzero fiber. -/
theorem intrinsicHamilton_chart_independent (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c d : M) (p : CotangentBundle M)
    (hc : p ∈ cotangentSource c) (hd : p ∈ cotangentSource d)
    (hpun : p ∈ puncturedCotangent) :
    intrinsicHamilton g c p = intrinsicHamilton g d p := by
  obtain ⟨δ,hδ,γ,hγ₀,hγ,_⟩ := exists_local_actual_hamiltonCurve g hg hn c p hc hpun
  have hz : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith,hδ⟩
  obtain ⟨K,hK,hzK,hKI,hγd⟩ := exists_hamiltonCurve_chart_overlap g hg hn hs c d γ _
    isOpen_Ioo hγ 0 hz (hγ₀.symm ▸ hd)
  have hγc : IsHamiltonCurveInChart g c γ K :=
    ⟨fun t ht => hγ.1 t (hKI ht), fun t ht => hγ.2 t (hKI ht)⟩
  have hC := ((hamiltonCurve_actual_integralOn g c γ K hK hγc).isMIntegralCurveAt
    (hK.mem_nhds hzK)).hasMFDerivAt
  have hD := ((hamiltonCurve_actual_integralOn g d γ K hK hγd).isMIntegralCurveAt
    (hK.mem_nhds hzK)).hasMFDerivAt
  have he := hasMFDerivAt_unique hC hD
  have hv := DFunLike.congr_fun he (1 : ℝ)
  change (1 : ℝ) • intrinsicHamilton g c (γ 0) = (1 : ℝ) • intrinsicHamilton g d (γ 0) at hv
  simp only [one_smul] at hv
  cases hγ₀
  exact hv

/-- Actual canonical Hamilton vector, using the preferred chart only to choose its representative. -/
def canonicalHamilton (g : ManifoldBilinear.Field (M := M)) (p : CotangentBundle M) :
    TangentSpace CotangentModelWithCorners p := intrinsicHamilton g p.1 p

theorem hamiltonCurve_canonical_integralOn (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c : M) (γ : ℝ → CotangentBundle M)
    (I : Set ℝ) (hI : IsOpen I) (hγ : IsHamiltonCurveInChart g c γ I)
    (hpun : ∀ t ∈ I, γ t ∈ puncturedCotangent) :
    IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I := by
  intro t ht
  have hd := (hamiltonCurve_actual_integralOn g c γ I hI hγ) t ht
  have he := intrinsicHamilton_chart_independent g hg hn hs c (γ t).1 (γ t)
    (hγ.1 t ht) (mem_chart_source CoordinateSpace _) (hpun t ht)
  change HasMFDerivWithinAt 𝓘(ℝ) CotangentModelWithCorners γ I t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (intrinsicHamilton g c (γ t))) at hd
  rw [he] at hd
  exact hd

theorem exists_local_null_canonicalCurve (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (p : CotangentBundle M)
    (hpun : p ∈ puncturedCotangent)
    (hnull : dualEnergy g hn p = 0) :
    ∃ δ > (0 : ℝ), ∃ γ : ℝ → CotangentBundle M, γ 0 = p ∧
      IsHamiltonCurveInChart g p.1 γ (Ioo (-δ) δ) ∧
      IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) (Ioo (-δ) δ) ∧
      ∀ t ∈ Ioo (-δ) δ, γ t ∈ puncturedCotangent ∧ dualEnergy g hn (γ t) = 0 := by
  obtain ⟨δ,hδ,γ,hγ₀,hγ,_,hnul⟩ := exists_local_null_actual_hamiltonCurve g hg hn hs p.1 p
    (mem_chart_source CoordinateSpace p.1) hpun hnull
  exact ⟨δ,hδ,γ,hγ₀,hγ,hamiltonCurve_canonical_integralOn g hg hn hs p.1 γ _ isOpen_Ioo hγ
    (fun t ht => (hnul t ht).1),hnul⟩

theorem actual_hamiltonCurve_unique_germ_across_charts (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hn : ManifoldBilinear.IsNondegenerate g)
    (hs : ManifoldBilinear.IsSymmetric g) (c d : M) (γ ζ : ℝ → CotangentBundle M)
    (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hγ : IsHamiltonCurveInChart g c γ I) (hζ : IsHamiltonCurveInChart g d ζ J)
    (t₀ : ℝ) (htI : t₀ ∈ I) (htJ : t₀ ∈ J) (hinit : γ t₀ = ζ t₀) :
    γ =ᶠ[𝓝 t₀] ζ := by
  obtain ⟨K,hK,htK,hKI,hγd⟩ := exists_hamiltonCurve_chart_overlap g hg hn hs c d γ I hI hγ
    t₀ htI (hinit.symm ▸ hζ.1 t₀ htJ)
  exact actual_hamiltonCurve_unique_germ g hg hn d γ ζ K J hK hJ hγd hζ t₀ htK htJ hinit

end Burnett.Geometry.CotangentHamiltonLocalFlow

namespace Burnett.Geometry.CotangentHamiltonGeodesic

open Filter Finset
open scoped BigOperators Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InverseField
open Burnett.Geometry.InversePerturbation

/-- Coordinate metric lowering on a vector written as its component array. -/
def lower (G : Tensor2) (v : Covector) : Covector :=
  raiseCovector G v

theorem lower_raise (G : Tensor2) (hG : Matrix.det G ≠ 0) (ξ : Covector) :
    lower G (raiseCovector (matrixInverse G) ξ) = ξ := by
  funext i
  exact inverse_contract (matrixInverse G) G
    (fun a b => congrFun (congrFun (compose_matrixInverse G hG) a) b) ξ i

theorem raise_lower (G : Tensor2) (hG : Matrix.det G ≠ 0) (v : Covector) :
    raiseCovector (matrixInverse G) (lower G v) = v := by
  funext i
  exact inverse_contract G (matrixInverse G)
    (fun a b => congrFun (congrFun (matrixInverse_compose G hG) a) b) v i

private theorem lower_swap (G : Tensor2) (hG : IsSymmetricTensor G) (v w : Covector) :
    (∑ i, v i * lower G w i) = ∑ j, lower G v j * w j := by
  simp only [lower, raiseCovector, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hG i j]
  ring

theorem symbolNorm_eq_pair_raise (A : Tensor2) (ξ : Covector) :
    symbolNorm A ξ = ∑ i, ξ i * raiseCovector A ξ i := by
  simp only [symbolNorm, raiseCovector, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Differentiate the actual dual quadratic form at fixed momentum,
using the lowering identity and avoiding a supplied inverse derivative. -/
theorem hasDerivAt_fixed_momentum_energy {G : ℝ → Tensor2} {v : ℝ → Covector}
    {G' : Tensor2} {v' ξ : Covector} {t₀ : ℝ}
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t₀)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) t₀)
    (hs : IsSymmetricTensor (G t₀))
    (hlow : (fun t => lower (G t) (v t)) =ᶠ[𝓝 t₀] fun _ => ξ) :
    HasDerivAt (fun t => (∑ i, ξ i * v t i) / 2)
      (-(∑ i, v t₀ i * lower G' (v t₀) i) / 2) t₀ := by
  have hd (i : Index) : HasDerivAt (fun t => lower (G t) (v t) i)
      (lower G' (v t₀) i + lower (G t₀) v' i) t₀ := by
    simp only [lower, raiseCovector, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun j _ => (hG i j).mul (hv j)
  have hz (i : Index) : lower G' (v t₀) i + lower (G t₀) v' i = 0 :=
    (hd i).unique ((hasDerivAt_const t₀ (ξ i)).congr_of_eventuallyEq
      (hlow.mono (fun t ht => congrFun ht i)))
  have hvξ : lower (G t₀) (v t₀) = ξ := hlow.eq_of_nhds
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => congrArg (fun a => v t₀ i * a) (hz i))
  simp only [mul_add, Finset.sum_add_distrib, mul_zero, Finset.sum_const_zero] at hsum
  rw [lower_swap (G t₀) hs, hvξ] at hsum
  have heq : (∑ i, ξ i * v' i) / 2 = -(∑ i, v t₀ i * lower G' (v t₀) i) / 2 := by
    linarith
  rw [← heq]
  exact (HasDerivAt.fun_sum fun i _ => (hv i).const_mul (ξ i)).div_const 2

/-- The first-kind connection contracted against two copies of the same velocity. -/
theorem koszul_velocity_contract (J : FirstJet) (v : Covector)
    (hJ : ∀ i, IsSymmetricTensor (J i)) (c : Index) :
    (∑ j, ∑ k, koszul J j k c * (v j * v k)) =
      (∑ j, ∑ k, J j c k * (v j * v k)) - (∑ j, ∑ k, J c j k * (v j * v k)) / 2 := by
  have swap : (∑ j, ∑ k, J k j c * (v j * v k)) = ∑ j, ∑ k, J j c k * (v j * v k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hJ j k c, mul_comm (v k) (v j)]
  have symm : (∑ j, ∑ k, J j k c * (v j * v k)) = ∑ j, ∑ k, J j c k * (v j * v k) := by
    simp only [hJ _ _ c]
  have expand (j k : Index) :
      koszul J j k c * (v j * v k) =
      (J j k c * (v j * v k) + J k j c * (v j * v k) - J c j k * (v j * v k)) / 2 := by
    unfold koszul
    ring
  simp only [expand, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [symm, swap]
  ring

/-- Raising the actual first-kind covariant acceleration equation gives the
second-kind Christoffel contraction. -/
theorem acceleration_eq_neg_christoffel (G : Tensor2) (hG : Matrix.det G ≠ 0)
    (J : FirstJet) (v a : Covector) (hJ : ∀ i, IsSymmetricTensor (J i))
    (ha : ∀ c, lower G a c =
      (∑ j, ∑ k, J c j k * (v j * v k)) / 2 - (∑ j, ∑ k, J j c k * (v j * v k))) :
    ∀ i, a i = -(∑ j, ∑ k, christoffel (matrixInverse G) J i j k * (v j * v k)) := by
  intro i
  have hneg (c : Index) : lower G a c = -(∑ j, ∑ k, koszul J j k c * (v j * v k)) := by
    rw [ha c, koszul_velocity_contract J v hJ c]
    ring
  rw [← congrFun (raise_lower G hG a) i]
  simp only [raiseCovector, hneg, mul_neg, Finset.sum_neg_distrib, christoffel]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  calc
    (∑ c, ∑ j, ∑ k, matrixInverse G i c * (koszul J j k c * (v j * v k))) =
        ∑ j, ∑ c, ∑ k, matrixInverse G i c * (koszul J j k c * (v j * v k)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm

end Burnett.Geometry.CotangentHamiltonGeodesic

namespace Burnett.Geometry.CotangentHamiltonGeodesic

open Filter Finset Set
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference InverseField
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open UnitNullCompactness UnitNullAngular CotangentAngularExtension RadialHamilton

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

private theorem component_differentiable
    (g : Field (M := M)) (hg : IsSmooth g) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) (a b : Index) :
    DifferentiableAt ℝ (fun z => metricComponents (coordinateBilinear g c) z a b) y :=
  ((contDiffOn_metricComponents g hg c a b).contDiffAt
    ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)

private theorem inverse_component_differentiable
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g)
    (c : M) {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) (a b : Index) :
    DifferentiableAt ℝ (fun z => chartInverse g c z a b) y :=
  ((chartInverse_smooth g hg hn c a b).contDiffAt
    ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)

/-- The canonical momentum equation is the Euler–Lagrange momentum equation
for the actual coordinate metric and the actual raised velocity. -/
theorem neg_basePartial_chartInverse (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (c : M)
    (z : Phase) (hz : z ∈ phaseTarget c) (i : Index) :
    -basePartial (coordinateP (chartInverse g c)) z i =
      (∑ a, raiseCovector (chartInverse g c z.1) z.2 a *
        lower (coordinateJet (metricComponents (coordinateBilinear g c)) z.1 i)
          (raiseCovector (chartInverse g c z.1) z.2) a) / 2 := by
  let A := chartInverse g c
  let G := metricComponents (coordinateBilinear g c)
  let x (t : ℝ) := z.1 + t • coordinateBasis i
  let v (t : ℝ) := raiseCovector (A (x t)) z.2
  let U := (chartAt CoordinateSpace c).target
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  have hzU : z.1 ∈ U := hz.1
  have hx₀ : x 0 = z.1 := by simp [x]
  have hx : HasDerivAt x (coordinateBasis i) 0 := by
    simpa only [x, one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateBasis i)).const_add z.1
  have hχ : ∀ᶠ t in 𝓝 (0 : ℝ), x t ∈ U :=
    hx.continuousAt.preimage_mem_nhds (hU.mem_nhds (hx₀.symm ▸ hzU))
  have hlow : (fun t => lower (G (x t)) (v t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => z.2 := by
    filter_upwards [hχ] with t ht
    exact lower_raise _ (ManifoldVolumeRegularity.coordinate_det_ne_zero g hn c ht) z.2
  have hGdiff (a b : Index) : HasDerivAt (fun t => G (x t) a b)
      (coordinateJet G z.1 i a b) 0 := by
    have hd : DifferentiableAt ℝ (fun y => G y a b) (x 0) :=
      hx₀.symm ▸ component_differentiable g hg c hzU a b
    have h := hd.hasFDerivAt.comp_hasDerivAt 0 hx
    have he : coordinateBasis i = EuclideanSpace.single i 1 := by
      change EuclideanSpace.basisFun Index ℝ i = _
      exact EuclideanSpace.basisFun_apply Index ℝ i
    simpa only [hx₀, coordinateJet, he, Function.comp_def] using h
  have hv (a : Index) : HasDerivAt (fun t => v t a)
      (∑ b, fderiv ℝ (fun y => A y a b) (x 0) (coordinateBasis i) * z.2 b) 0 := by
    unfold v raiseCovector
    apply HasDerivAt.fun_sum
    intro b _
    have hd : DifferentiableAt ℝ (fun y => A y a b) (x 0) :=
      hx₀.symm ▸ inverse_component_differentiable g hg hn c hzU a b
    exact (hd.hasFDerivAt.comp_hasDerivAt 0 hx).mul_const (z.2 b)
  have hsym : IsSymmetricTensor (G (x 0)) :=
    FiberMetric.covariant_symmetric _ (coordinateBilinear_symmetric g hs c (x 0)) coordinateBasis
  have hq := hasDerivAt_fixed_momentum_energy hGdiff hv hsym hlow
  have hP : DifferentiableAt ℝ (fun y => coordinateP A (y,z.2)) (x 0) := by
    have he : DifferentiableAt ℝ (fun y => ∑ a, ∑ b, A y a b * z.2 a * z.2 b) (x 0) := by
      apply DifferentiableAt.fun_sum
      intro a _
      apply DifferentiableAt.fun_sum
      intro b _
      have hd : DifferentiableAt ℝ (fun y => A y a b) (x 0) :=
        hx₀.symm ▸ inverse_component_differentiable g hg hn c hzU a b
      exact (hd.mul_const (z.2 a)).mul_const (z.2 b)
    simpa only [coordinateP, symbolNorm, div_eq_mul_inv] using he.mul_const ((2 : ℝ)⁻¹)
  have h := hP.hasFDerivAt.comp_hasDerivAt 0 hx
  have hf : (fun t => coordinateP A (x t,z.2)) = fun t => (∑ a, z.2 a * v t a) / 2 := by
    funext t
    simp only [coordinateP, symbolNorm_eq_pair_raise, v]
  change HasDerivAt (fun t => coordinateP A (x t,z.2))
    (fderiv ℝ (fun y => coordinateP A (y,z.2)) (x 0) (coordinateBasis i)) 0 at h
  rw [hf] at h
  have hz' := h.unique hq
  change fderiv ℝ (fun y => coordinateP A (y,z.2)) (x 0) (coordinateBasis i) =
    -(∑ a, v 0 a * lower (coordinateJet G z.1 i) (v 0) a) / 2 at hz'
  simp only [v, hx₀] at hz'
  change -fderiv ℝ (fun y => coordinateP A (y,z.2)) z.1 (coordinateBasis i) = _
  rw [hz']
  ring

end Burnett.Geometry.CotangentHamiltonGeodesic

namespace Burnett.Geometry.CotangentHamiltonGeodesic

open Filter Finset Set
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference InverseField BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open UnitNullCompactness UnitNullAngular CotangentAngularExtension RadialHamilton
open CotangentCauchyCrossing CotangentCrossingTransversality CotangentHamiltonLocalFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

private theorem derivative_eq_jet_sum (G : CoordinateSpace → Tensor2) (x v : CoordinateSpace)
    (i j : Index) :
    fderiv ℝ (fun y => G y i j) x v = ∑ k, v k * coordinateJet G x k i j := by
  let D := fderiv ℝ (fun y => G y i j) x
  have h := congrArg D (coordinateBasis.sum_repr v)
  have hb (k : Index) : (EuclideanSpace.basisFun Index ℝ).toBasis k = EuclideanSpace.single k 1 :=
    EuclideanSpace.basisFun_apply Index ℝ k
  simpa only [D, map_sum, map_smul, smul_eq_mul, coordinateBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    hb, coordinateJet] using h.symm

private theorem directional_lower (J : FirstJet) (v : Covector) (i : Index) :
    lower (fun a b => ∑ k, v k * J k a b) v i = ∑ k, ∑ b, J k i b * (v k * v b) := by
  simp only [lower, raiseCovector, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem velocity_pair (J : FirstJet) (v : Covector) (i : Index) :
    (∑ a, v a * lower (J i) v a) = ∑ a, ∑ b, J i a b * (v a * v b) := by
  simp only [lower, raiseCovector, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The projection of the actual Hamilton curve obeys the affinely
parametrized geodesic equation in its actual chart and connection. -/
theorem hamiltonCurve_projected_geodesic (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (c : M) (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsHamiltonCurveInChart g c γ I) (t : ℝ) (ht : t ∈ I) :
    let x : ℝ → CoordinateSpace := fun s => (cotangentChart c (γ s)).1
    ∃ v a : CoordinateSpace, HasDerivAt x v t ∧ HasDerivAt (deriv x) a t ∧
      ∀ i, a i + (∑ j, ∑ k,
        computedConnection (coordinateBilinear g c) (x t) i j k * (v j * v k)) = 0 := by
  let z : ℝ → Phase := cotangentChart c ∘ γ
  let x : ℝ → CoordinateSpace := fun s => (z s).1
  let ξ : ℝ → Covector := fun s => (z s).2
  let A := chartInverse g c
  let G := metricComponents (coordinateBilinear g c)
  let J := coordinateJet G (x t)
  let H := hamiltonVector A
  let V : Phase → CoordinateSpace := fun p => (H p).1
  let v : ℝ → CoordinateSpace := V ∘ z
  have htphase : z t ∈ phaseTarget c := cotangentChart_mapsTo c (hγ.1 t ht)
  have htchart : x t ∈ (chartAt CoordinateSpace c).target := htphase.1
  have hx (s : ℝ) (hsI : s ∈ I) : HasDerivAt x (v s) s := by
    exact (ContinuousLinearMap.fst ℝ CoordinateSpace Covector).hasFDerivAt.comp_hasDerivAt s (hγ.2 s hsI)
  have hξ : HasDerivAt ξ ((H (z t)).2) t :=
    (ContinuousLinearMap.snd ℝ CoordinateSpace Covector).hasFDerivAt.comp_hasDerivAt t (hγ.2 t ht)
  have hV : DifferentiableAt ℝ V (z t) := by
    have hdiff : DifferentiableAt ℝ H (z t) :=
      ((contDiffOn_hamiltonVector_chartInverse g hg hn c).contDiffAt
        ((isOpen_phaseTarget c).mem_nhds htphase)).differentiableAt (by simp)
    exact (ContinuousLinearMap.fst ℝ CoordinateSpace Covector).differentiableAt.comp _ hdiff
  let a := fderiv ℝ V (z t) (H (z t))
  have ha : HasDerivAt v a t := hV.hasFDerivAt.comp_hasDerivAt t (hγ.2 t ht)
  have hderiv : deriv x =ᶠ[𝓝 t] v := by
    filter_upwards [hI.mem_nhds ht] with s hsI
    exact (hx s hsI).deriv
  refine ⟨v t, a, hx t ht, ha.congr_of_eventuallyEq hderiv, ?_⟩
  let vc (s : ℝ) : Covector := fun i => v s i
  let ac : Covector := fun i => a i
  let dG : Tensor2 := fun i j => ∑ k, vc t k * J k i j
  have hLower : (fun s => lower (G (x s)) (vc s)) =ᶠ[𝓝 t] ξ := by
    filter_upwards [hI.mem_nhds ht] with s hsI
    have hphase : z s ∈ phaseTarget c := cotangentChart_mapsTo c (hγ.1 s hsI)
    have he := hamiltonVector_fst_eq_raise A (z s) (chartInverse_symm g hs c (x s))
    change v s = WithLp.toLp 2 (raiseCovector (A (x s)) (ξ s)) at he
    have hvc : vc s = raiseCovector (A (x s)) (ξ s) := by
      exact congrArg (fun w : CoordinateSpace => fun i => w i) he
    rw [hvc]
    exact lower_raise _ (ManifoldVolumeRegularity.coordinate_det_ne_zero g hn c hphase.1) (ξ s)
  have hG (i j : Index) : HasDerivAt (fun s => G (x s) i j) (dG i j) t := by
    have hD : DifferentiableAt ℝ (fun y => G y i j) (x t) :=
      component_differentiable g hg c htchart i j
    have h := hD.hasFDerivAt.comp_hasDerivAt t (hx t ht)
    change HasDerivAt (fun s => G (x s) i j)
      (fderiv ℝ (fun y => G y i j) (x t) (v t)) t at h
    rwa [derivative_eq_jet_sum] at h
  have hvc (j : Index) : HasDerivAt (fun s => vc s j) (ac j) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt t ha
  have hlowered (i : Index) : HasDerivAt (fun s => lower (G (x s)) (vc s) i)
      (lower dG (vc t) i + lower (G (x t)) ac i) t := by
    simp only [lower, raiseCovector, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun j _ => (hG i j).mul (hvc j)
  have hmom (i : Index) : HasDerivAt (fun s => ξ s i)
      ((∑ j, ∑ k, J i j k * (vc t j * vc t k)) / 2) t := by
    have hd := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index => ℝ) i).hasFDerivAt.comp_hasDerivAt t hξ
    change HasDerivAt (fun s => ξ s i) (-basePartial (coordinateP A) (z t) i) t at hd
    rw [neg_basePartial_chartInverse g hg hn hs c (z t) htphase i] at hd
    have he := hamiltonVector_fst_eq_raise A (z t) (chartInverse_symm g hs c (x t))
    have hevc : vc t = raiseCovector (A (x t)) (ξ t) :=
      congrArg (fun w : CoordinateSpace => fun i => w i) he
    change HasDerivAt (fun s => ξ s i)
      ((∑ j, raiseCovector (A (x t)) (ξ t) j *
        lower (J i) (raiseCovector (A (x t)) (ξ t)) j) / 2) t at hd
    rwa [← hevc, velocity_pair J (vc t) i] at hd
  have hlaw (i : Index) : lower (G (x t)) ac i =
      (∑ j, ∑ k, J i j k * (vc t j * vc t k)) / 2 - (∑ j, ∑ k, J j i k * (vc t j * vc t k)) := by
    have he := ((hlowered i).congr_of_eventuallyEq (hLower.mono (fun s hs' => congrFun hs'.symm i))).unique
      (hmom i)
    rw [directional_lower J (vc t) i] at he
    linarith
  have hsJ : ∀ k, IsSymmetricTensor (J k) :=
    coordinateJet_symmetric G (x t) (Eventually.of_forall (fun y =>
      FiberMetric.covariant_symmetric _ (coordinateBilinear_symmetric g hs c y) coordinateBasis))
  have hEq := acceleration_eq_neg_christoffel (G (x t))
    (ManifoldVolumeRegularity.coordinate_det_ne_zero g hn c htchart) J (vc t) ac hsJ hlaw
  intro i
  change ac i + (∑ j, ∑ k,
    computedConnection (coordinateBilinear g c) (x t) i j k * (vc t j * vc t k)) = 0
  rw [hEq i]
  exact neg_add_cancel _

end Burnett.Geometry.CotangentHamiltonGeodesic

namespace Burnett.Geometry.CotangentHamiltonGeodesic

open Set
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference InverseField BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open UnitNullCompactness UnitNullAngular CotangentAngularExtension RadialHamilton
open CotangentCauchyCrossing CotangentCrossingTransversality CotangentHamiltonLocalFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The same genuine local canonical trajectory has a nonzero null,
affinely parametrized geodesic projection. -/
theorem exists_local_null_geodesic_projection (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (p : CotangentBundle M)
    (hpun : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0) :
    ∃ δ > (0 : ℝ), ∃ γ : ℝ → CotangentBundle M, γ 0 = p ∧
      IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) (Ioo (-δ) δ) ∧
      ∀ t ∈ Ioo (-δ) δ,
        let x : ℝ → CoordinateSpace := fun s => (cotangentChart p.1 (γ s)).1
        ∃ v a : CoordinateSpace, HasDerivAt x v t ∧ HasDerivAt (deriv x) a t ∧ v ≠ 0 ∧
          coordinateBilinear g p.1 (x t) v v = 0 ∧
          ∀ i, a i + (∑ j, ∑ k, computedConnection (coordinateBilinear g p.1) (x t) i j k *
            (v j * v k)) = 0 := by
  obtain ⟨δ, hδ, γ, hp, hchart, hcanonical, hnullcurve⟩ :=
    exists_local_null_canonicalCurve g hg hn hs p hpun hnull
  refine ⟨δ, hδ, γ, hp, hcanonical, ?_⟩
  intro t ht x
  obtain ⟨v, a, hDeriv, hAccel, hGeo⟩ :=
    hamiltonCurve_projected_geodesic g hg hn hs p.1 γ _ isOpen_Ioo hchart t ht
  let q := γ t
  let z := cotangentChart p.1 q
  let B := coordinateBilinear g p.1 z.1
  have hsB : B.IsSymm := coordinateBilinear_symmetric g hs p.1 z.1
  have hchartTarget : z ∈ phaseTarget p.1 := cotangentChart_mapsTo p.1 (hchart.1 t ht)
  have hnB : B.Nondegenerate := coordinateBilinear_nondegenerate g hn p.1 hchartTarget.1
  have hV : HasDerivAt x (hamiltonVector (chartInverse g p.1) z).1 t :=
    (ContinuousLinearMap.fst ℝ CoordinateSpace Covector).hasFDerivAt.comp_hasDerivAt t (hchart.2 t ht)
  have hvRaise : v = WithLp.toLp 2 (raiseCovector (chartInverse g p.1 z.1) z.2) := by
    rw [hDeriv.unique hV, hamiltonVector_fst_eq_raise _ _ (chartInverse_symm g hs p.1 z.1)]
  have hlower : ∀ w, B v w = covectorCLM z.2 w := by
    intro w
    rw [hvRaise]
    exact inverse_raise_lower B hnB hsB z.2 w
  have hnonzero : v ≠ 0 := by
    intro hv
    have hz := cotangentChart_mem_punctured p.1 q (hchart.1 t ht) (hnullcurve t ht).1
    apply hz.2
    funext i
    have h := hlower (coordinateBasis i)
    rw [hv, map_zero, LinearMap.zero_apply, covectorCLM_apply_basis] at h
    exact h.symm
  have henergy : symbolNorm (chartInverse g p.1 z.1) z.2 = 0 :=
    (dualEnergy_chart g hn hs p.1 q (hchart.1 t ht)).symm.trans (hnullcurve t ht).2
  have hB : B v v = 0 := by
    rw [hlower v, covectorCLM_eval]
    rw [symbolNorm_eq_pair_raise] at henergy
    simpa only [hvRaise] using henergy
  exact ⟨v, a, hDeriv, hAccel, hnonzero, hB, hGeo⟩

end Burnett.Geometry.CotangentHamiltonGeodesic

namespace Burnett.Geometry.CotangentHamiltonMaximalCurve

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentHamiltonNaturality Burnett.Geometry.CotangentSymplecticTransition
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

private theorem cotangentChart_differentiable (c : M) {p : CotangentBundle M}
    (hp : p ∈ cotangentSource c) :
    MDifferentiableAt CotangentModelWithCorners CoordinatePhaseModel (cotangentChart c) p :=
  ((contMDiffOn_cotangentChart c).contMDiffAt
    ((isOpen_cotangentSource c).mem_nhds hp)).mdifferentiableAt (by simp)

private theorem cotangentChartInverse_differentiable (c : M) {z : Phase}
    (hz : z ∈ phaseTarget c) :
    MDifferentiableAt CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c) z :=
  ((contMDiffOn_cotangentChartInverse c).contMDiffAt
    ((isOpen_phaseTarget c).mem_nhds hz)).mdifferentiableAt (by simp)

private theorem transition_mfderiv_eq_fderiv (c d : M) (z : Phase) :
    mfderiv CoordinatePhaseModel CoordinatePhaseModel (cotangentTransition c d) z =
      fderiv ℝ (cotangentTransition c d) z := by
  rw [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact mfderiv_eq_fderiv

/-- The canonical vector is independent of the chart, also at the zero section. -/
theorem intrinsicHamilton_chart_independent_all (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (c d : M) (p : CotangentBundle M)
    (hc : p ∈ cotangentSource c) (hd : p ∈ cotangentSource d) :
    intrinsicHamilton g c p = intrinsicHamilton g d p := by
  let z := cotangentChart c p
  let H := hamiltonVector (chartInverse g c) z
  have hz : z ∈ transitionSource c d := chart_mem_transitionSource c d p hc hd
  have hd₁ : MDifferentiableAt CoordinatePhaseModel CoordinatePhaseModel (cotangentTransition c d) z := by
    have h := ((cotangentTransition_contDiffOn c d).contDiffAt
      ((transitionSource_isOpen c d).mem_nhds hz)).differentiableAt (by simp)
    have h' := h.mdifferentiableAt
    simpa only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] using h'
  have hΦ : cotangentTransition c d z = cotangentChart d p :=
    cotangentTransition_chart c d p hc
  have hd₂ := cotangentChartInverse_differentiable d (cotangentChart_mapsTo d hd)
  have hcomp := mfderiv_comp_apply_of_eq z hd₂ hd₁ hΦ H
  have he : (cotangentChartInverse d ∘ cotangentTransition c d) =ᶠ[𝓝 z] cotangentChartInverse c := by
    filter_upwards [(transitionSource_isOpen c d).mem_nhds hz] with w hw
    change cotangentChartInverse d (cotangentChart d (cotangentChartInverse c w)) = _
    exact cotangentChart_left_inv d hw.2
  rw [he.mfderiv_eq, transition_mfderiv_eq_fderiv] at hcomp
  have hv : fderiv ℝ (cotangentTransition c d) z H =
      hamiltonVector (chartInverse g d) (cotangentChart d p) :=
    actual_hamiltonVector_chart_compatible g hg hn hs c d p hc hd
  exact hcomp.trans (congrArg (fun w : Phase =>
    mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse d)
      (cotangentChart d p) w) hv)

private theorem mfderiv_cotangentChart_inverse_apply (c : M) {p : CotangentBundle M}
    (hp : p ∈ cotangentSource c) (v : Phase) :
    mfderiv CotangentModelWithCorners CoordinatePhaseModel (cotangentChart c) p
      (mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c)
        (cotangentChart c p) v) = v := by
  have hz := cotangentChart_mapsTo c hp
  have h := mfderiv_comp_apply_of_eq (cotangentChart c p) (cotangentChart_differentiable c hp)
    (cotangentChartInverse_differentiable c hz) (cotangentChart_left_inv c hp) v
  have he : (cotangentChart c ∘ cotangentChartInverse c) =ᶠ[𝓝 (cotangentChart c p)] id := by
    filter_upwards [(isOpen_phaseTarget c).mem_nhds hz] with z hz'
    exact cotangentChart_right_inv c hz'
  rw [he.mfderiv_eq, mfderiv_id] at h
  exact h.symm

set_option synthInstance.maxHeartbeats 200000 in
/-- An actual manifold integral curve satisfies the canonical ODE in every open chart interval it visits. -/
theorem canonicalCurve_in_chart (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g)
    (hs : IsSymmetric g) (c : M) (γ : ℝ → CotangentBundle M) (I : Set ℝ)
    (hI : IsOpen I)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I)
    (hchart : MapsTo γ I (cotangentSource c)) :
    IsHamiltonCurveInChart g c γ I := by
  refine ⟨hchart, ?_⟩
  intro t ht
  have hp := hchart ht
  have hd := (hγ t ht).hasMFDerivAt (hI.mem_nhds ht)
  have he := (cotangentChart_differentiable c hp).hasMFDerivAt.comp t hd
  have he' : HasMFDerivAt 𝓘(ℝ) CoordinatePhaseModel (cotangentChart c ∘ γ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (hamiltonVector (chartInverse g c) (cotangentChart c (γ t)))) := by
    apply he.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change mfderiv CotangentModelWithCorners CoordinatePhaseModel (cotangentChart c) (γ t)
      (a • canonicalHamilton g (γ t)) =
      a • hamiltonVector (chartInverse g c) (cotangentChart c (γ t))
    have hchart' : γ t ∈ cotangentSource (γ t).1 := mem_chart_source CoordinateSpace _
    rw [map_smul, show canonicalHamilton g (γ t) = intrinsicHamilton g c (γ t) from
      intrinsicHamilton_chart_independent_all g hg hn hs (γ t).1 c (γ t) hchart' hp]
    rw [intrinsicHamilton, mfderiv_cotangentChart_inverse_apply c hp]
  have hf : HasFDerivAt (cotangentChart c ∘ γ)
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (hamiltonVector (chartInverse g c) (cotangentChart c (γ t)))) t := by
    rw [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at he'
    exact he'.hasFDerivAt
  simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    one_smul, Function.comp_def] using hf.hasDerivAt

/-- Every point of a true canonical trajectory admits one open interval for its chart ODE. -/
theorem canonicalCurve_chart_near (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g)
    (hs : IsSymmetric g) (c : M) (γ : ℝ → CotangentBundle M) (I : Set ℝ)
    (hI : IsOpen I)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I)
    (t : ℝ) (ht : t ∈ I) (hc : γ t ∈ cotangentSource c) :
    ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ J ⊆ I ∧ IsHamiltonCurveInChart g c γ J := by
  have hnbr : γ ⁻¹' cotangentSource c ∈ 𝓝 t :=
    ((hγ.continuousWithinAt ht).continuousAt (hI.mem_nhds ht)).preimage_mem_nhds
      ((isOpen_cotangentSource c).mem_nhds hc)
  obtain ⟨J, hJ, hJo, htJ⟩ := mem_nhds_iff.mp (inter_mem (hI.mem_nhds ht) hnbr)
  have hJI : J ⊆ I := hJ.trans inter_subset_left
  exact ⟨J, hJo, htJ, hJI,
    canonicalCurve_in_chart g hg hn hs c γ J hJo (hγ.mono hJI) (hJ.trans inter_subset_right)⟩

/-- Genuine canonical integral curves through the same phase point have equal time germs. -/
theorem canonicalCurve_unique_germ (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (γ ζ : ℝ → CotangentBundle M)
    (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I)
    (hζ : IsMIntegralCurveOn (I := CotangentModelWithCorners) ζ (canonicalHamilton g) J)
    (t : ℝ) (htI : t ∈ I) (htJ : t ∈ J) (he : γ t = ζ t) :
    γ =ᶠ[𝓝 t] ζ := by
  let c := (γ t).1
  have hc : γ t ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨U, hU, htU, _, hγU⟩ := canonicalCurve_chart_near g hg hn hs c γ I hI hγ t htI hc
  obtain ⟨V, hV, htV, _, hζV⟩ :=
    canonicalCurve_chart_near g hg hn hs c ζ J hJ hζ t htJ (he ▸ hc)
  exact actual_hamiltonCurve_unique_germ g hg hn c γ ζ U V hU hV hγU hζV t htU htV he

end Burnett.Geometry.CotangentHamiltonMaximalCurve

namespace Burnett.Geometry.CotangentHamiltonMaximalCurve

open Set Filter
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentHamiltonLocalFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

private theorem eqOn_of_open_equal_germs {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set ℝ} (hU : IsPreconnected U) {f k : ℝ → X}
    (hf : ContinuousOn f U) (hk : ContinuousOn k U)
    (hgerm : ∀ t ∈ U, f t = k t → f =ᶠ[𝓝 t] k)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) (h₀ : f t₀ = k t₀) :
    EqOn f k U := by
  let W : Set U := {t | f t = k t}
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hc : IsClosed W :=
    isClosed_eq (continuousOn_iff_continuous_restrict.mp hf)
      (continuousOn_iff_continuous_restrict.mp hk)
  have ho : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change Subtype.val ⁻¹' {r : ℝ | f r = k r} ∈ 𝓝 t
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds (hgerm t t.2 ht)
  have hnonempty : W.Nonempty := ⟨⟨t₀, ht₀⟩, h₀⟩
  have hall : W = univ := (isClopen_iff.mp ⟨hc, ho⟩).resolve_left hnonempty.ne_empty
  intro t ht
  have he : (⟨t, ht⟩ : U) ∈ W := hall.symm ▸ mem_univ _
  exact he

/-- Two true canonical integral curves with the same value at one time agree on their
entire common open interval. The interval can be unbounded. -/
theorem canonicalCurve_eqOn_overlap [T2Space M] (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (γ ζ : ℝ → CotangentBundle M) (I J : Set ℝ)
    (hI : IsOpen I) (hJ : IsOpen J) (hIconn : OrdConnected I) (hJconn : OrdConnected J)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I)
    (hζ : IsMIntegralCurveOn (I := CotangentModelWithCorners) ζ (canonicalHamilton g) J)
    (t₀ : ℝ) (htI : t₀ ∈ I) (htJ : t₀ ∈ J) (h₀ : γ t₀ = ζ t₀) :
    EqOn γ ζ (I ∩ J) := by
  letI : T2Space (CotangentBundle M) := cotangentBundle_t2Space
  refine eqOn_of_open_equal_germs (hIconn.inter hJconn).isPreconnected
    (hγ.continuousOn.mono inter_subset_left) (hζ.continuousOn.mono inter_subset_right)
    ?_ ⟨htI, htJ⟩ h₀
  intro t ht he
  exact canonicalCurve_unique_germ g hg hn hs γ ζ I J hI hJ hγ hζ t ht.1 ht.2 he

/-- A true canonical integral curve through p at time zero on an open time interval. -/
structure CanonicalTrajectory (g : Field (M := M)) (p : CotangentBundle M) where
  domain : Set ℝ
  curve : ℝ → CotangentBundle M
  domain_open : IsOpen domain
  domain_interval : OrdConnected domain
  zero_mem : 0 ∈ domain
  initial : curve 0 = p
  integral : IsMIntegralCurveOn (I := CotangentModelWithCorners) curve (canonicalHamilton g) domain

/-- Gluing every true solution through the same initial point gives the largest open
time interval, with agreement on every constituent domain. -/
theorem exists_maximal_canonicalTrajectory [T2Space M] (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (p : CotangentBundle M) (A₀ : CanonicalTrajectory g p) :
    ∃ A : CanonicalTrajectory g p, ∀ B : CanonicalTrajectory g p,
      B.domain ⊆ A.domain ∧ EqOn A.curve B.curve B.domain := by
  classical
  let U : Set ℝ := ⋃ B : CanonicalTrajectory g p, B.domain
  have hU : IsOpen U := isOpen_iUnion fun B : CanonicalTrajectory g p => B.domain_open
  have hUconn : OrdConnected U := isPreconnected_iff_ordConnected.mp
    (isPreconnected_iUnion ⟨0, mem_iInter.mpr (fun B : CanonicalTrajectory g p => B.zero_mem)⟩
      fun B : CanonicalTrajectory g p => B.domain_interval.isPreconnected)
  have hsubset (B : CanonicalTrajectory g p) : B.domain ⊆ U := subset_iUnion _ B
  let γ (t : ℝ) : CotangentBundle M :=
    if ht : t ∈ U then (Classical.choose (mem_iUnion.mp ht)).curve t else p
  have hrestrict (B : CanonicalTrajectory g p) : EqOn γ B.curve B.domain := by
    intro t ht
    have htU := hsubset B ht
    let C : CanonicalTrajectory g p := Classical.choose (mem_iUnion.mp htU)
    have htC : t ∈ C.domain := Classical.choose_spec (mem_iUnion.mp htU)
    have he := canonicalCurve_eqOn_overlap g hg hn hs C.curve B.curve C.domain B.domain
      C.domain_open B.domain_open C.domain_interval B.domain_interval C.integral B.integral
      0 C.zero_mem B.zero_mem (C.initial.trans B.initial.symm)
    change (if ht' : t ∈ U then (Classical.choose (mem_iUnion.mp ht')).curve t else p) = B.curve t
    rw [dif_pos htU]
    exact he ⟨htC, ht⟩
  have hinit : γ 0 = p := (hrestrict A₀ A₀.zero_mem).trans A₀.initial
  have hintegral : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) U := by
    intro t ht
    obtain ⟨B, htB⟩ := mem_iUnion.mp ht
    have he : γ =ᶠ[𝓝 t] B.curve := by
      filter_upwards [B.domain_open.mem_nhds htB] with s hs'
      exact hrestrict B hs'
    have hd := ((B.integral t htB).hasMFDerivAt (B.domain_open.mem_nhds htB)).congr_of_eventuallyEq he
    rw [hrestrict B htB]
    exact hd.hasMFDerivWithinAt
  exact ⟨⟨U, γ, hU, hUconn, hsubset A₀ A₀.zero_mem, hinit, hintegral⟩,
    fun B => ⟨hsubset B, hrestrict B⟩⟩

end Burnett.Geometry.CotangentHamiltonMaximalCurve

namespace Burnett.Geometry.CotangentHamiltonMaximalCurve

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonGeodesic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- Along any true Hamilton trajectory, the dual quadratic energy is locally constant. -/
theorem canonicalCurve_dualEnergy_germ (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I)
    (t : ℝ) (ht : t ∈ I) :
    (fun s => dualEnergy g hn (γ s)) =ᶠ[𝓝 t] (fun _ => dualEnergy g hn (γ t)) := by
  let c := (γ t).1
  have hc : γ t ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨J, hJ, htJ, _, hchart⟩ := canonicalCurve_chart_near g hg hn hs c γ I hI hγ t ht hc
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds htJ)
  let K := Metric.ball t ε
  have hKt : t ∈ K := Metric.mem_ball_self hε
  have hK : IsOpen K := Metric.isOpen_ball
  have hKconn : IsPreconnected K := by
    change IsPreconnected (Metric.ball t ε)
    rw [Real.ball_eq_Ioo]
    exact isPreconnected_Ioo
  have hcurve : IsHamiltonCurveInChart g c γ K :=
    ⟨fun s h => hchart.1 s (hsub h), fun s h => hchart.2 s (hsub h)⟩
  filter_upwards [hK.mem_nhds hKt] with s hs'
  exact dualEnergy_constant_on_hamiltonCurve g hg hn hs c γ K hK hKconn hcurve s t hs' hKt

/-- The dual quadratic energy is constant on the whole time interval of a true trajectory. -/
theorem CanonicalTrajectory.dualEnergy_constant (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) {t : ℝ} (ht : t ∈ A.domain) :
    dualEnergy g hn (A.curve t) = dualEnergy g hn p := by
  let E (s : ℝ) := dualEnergy g hn (A.curve s)
  have hEgerm (s : ℝ) (hs' : s ∈ A.domain) : E =ᶠ[𝓝 s] (fun _ => E s) :=
    canonicalCurve_dualEnergy_germ g hg hn hs A.curve A.domain A.domain_open A.integral s hs'
  have hE : ContinuousOn E A.domain := by
    intro s hs'
    exact (continuousAt_const.congr_of_eventuallyEq (hEgerm s hs')).continuousWithinAt
  have he : EqOn E (fun _ => E 0) A.domain := by
    refine eqOn_of_open_equal_germs A.domain_interval.isPreconnected hE continuousOn_const
      ?_ A.zero_mem rfl
    intro s hs' hval
    exact (hEgerm s hs').trans (Filter.Eventually.of_forall fun _ => hval)
  exact (he ht).trans (congrArg (dualEnergy g hn) A.initial)

/-- The canonical vector field vanishes on the zero section. -/
theorem canonicalHamilton_eq_zero_of_zero_covector (g : Field (M := M))
    (hs : IsSymmetric g) (p : CotangentBundle M) (hp : p.2 = 0) :
    canonicalHamilton g p = 0 := by
  let c := p.1
  let z := cotangentChart c p
  have hξ : z.2 = 0 := by
    funext i
    change cotangentCoords c p i = 0
    calc
      cotangentCoords c p i = covectorCLM (cotangentCoords c p) (coordinateBasis i) :=
        (covectorCLM_apply_basis (cotangentCoords c p) i).symm
      _ = 0 := by rw [cotangentCoords_eval, hp]; rfl
  have hH : hamiltonVector (chartInverse g c) z = 0 := by
    apply Prod.ext
    · rw [hamiltonVector_fst_eq_raise _ _ (chartInverse_symm g hs c z.1)]
      rw [hξ]
      have hz : raiseCovector (chartInverse g c z.1) (0 : Covector) = 0 := by
        funext i
        simp [raiseCovector]
      rw [hz]
      rfl
    · have hscale : phaseScale 0 z = z := by
        apply Prod.ext
        · rfl
        · simpa only [phaseScale_apply, zero_smul] using hξ.symm
      have hm := hamiltonVector_momentum_scale (chartInverse g c) z 0
      simpa only [hscale, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_smul] using hm
  change mfderiv CoordinatePhaseModel CotangentModelWithCorners (cotangentChartInverse c) z
    (hamiltonVector (chartInverse g c) z) = 0
  rw [hH, map_zero]

/-- A true canonical trajectory from a nonzero covector stays in the punctured bundle. -/
theorem CanonicalTrajectory.punctured [T2Space M] (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (hp : p ∈ puncturedCotangent)
    {t : ℝ} (ht : t ∈ A.domain) : A.curve t ∈ puncturedCotangent := by
  intro hz
  let q := A.curve t
  let k : ℝ → CotangentBundle M := fun _ => q
  have hq := canonicalHamilton_eq_zero_of_zero_covector g hs q hz
  have hk : IsMIntegralCurveOn (I := CotangentModelWithCorners) k (canonicalHamilton g) A.domain := by
    intro s hs'
    change HasMFDerivWithinAt 𝓘(ℝ) CotangentModelWithCorners (fun _ => q) A.domain s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (canonicalHamilton g q))
    rw [hq]
    have he : (1 : ℝ →L[ℝ] ℝ).smulRight (0 : TangentSpace CotangentModelWithCorners q) = 0 := by
      apply ContinuousLinearMap.ext
      intro r
      simp only [ContinuousLinearMap.smulRight_apply, smul_zero, ContinuousLinearMap.zero_apply]
    rw [he]
    exact hasMFDerivWithinAt_const q A.domain s
  have he := canonicalCurve_eqOn_overlap g hg hn hs A.curve k A.domain A.domain
    A.domain_open A.domain_open A.domain_interval A.domain_interval A.integral hk t ht ht rfl
  have hpq : p = q := A.initial.symm.trans (he ⟨A.zero_mem, A.zero_mem⟩)
  exact hp (hpq.symm ▸ hz)

/-- A nonzero null covector starts a genuine maximal orbit. Its domain contains the
domain of every true canonical trajectory through the same phase point. -/
theorem exists_maximal_null_canonicalTrajectory [T2Space M] (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hnp : dualEnergy g hn p = 0) :
    ∃ A : CanonicalTrajectory g p,
      (∀ B : CanonicalTrajectory g p, B.domain ⊆ A.domain ∧ EqOn A.curve B.curve B.domain) ∧
      ∀ t ∈ A.domain, A.curve t ∈ puncturedCotangent ∧ dualEnergy g hn (A.curve t) = 0 := by
  obtain ⟨δ, hδ, γ, hγ, _, hC, _⟩ := exists_local_null_canonicalCurve g hg hn hs p hp hnp
  let A₀ : CanonicalTrajectory g p :=
    ⟨Ioo (-δ) δ, γ, isOpen_Ioo, ordConnected_Ioo, ⟨by linarith, hδ⟩, hγ, hC⟩
  obtain ⟨A, hmax⟩ := exists_maximal_canonicalTrajectory g hg hn hs p A₀
  exact ⟨A, hmax, fun t ht =>
    ⟨A.punctured g hg hn hs hp ht, (A.dualEnergy_constant g hg hn hs ht).trans hnp⟩⟩

/-- A chart statement for the base projection of the same maximal orbit at any time. -/
theorem CanonicalTrajectory.projected_null_geodesic [T2Space M] (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnp : dualEnergy g hn p = 0)
    (c : M) (t : ℝ) (ht : t ∈ A.domain) (hc : A.curve t ∈ cotangentSource c) :
    let x : ℝ → CoordinateSpace := fun s => (cotangentChart c (A.curve s)).1
    ∃ v a : CoordinateSpace, HasDerivAt x v t ∧ HasDerivAt (deriv x) a t ∧ v ≠ 0 ∧
      coordinateBilinear g c (x t) v v = 0 ∧
      ∀ i, a i + (∑ j, ∑ k, computedConnection (coordinateBilinear g c) (x t) i j k *
        (v j * v k)) = 0 := by
  intro x
  obtain ⟨J, hJ, htJ, _, hchart⟩ := canonicalCurve_chart_near g hg hn hs c A.curve A.domain
    A.domain_open A.integral t ht hc
  obtain ⟨v, a, hD, hA, hGeo⟩ :=
    hamiltonCurve_projected_geodesic g hg hn hs c A.curve J hJ hchart t htJ
  let z := cotangentChart c (A.curve t)
  let B := coordinateBilinear g c z.1
  have hD' : HasDerivAt x (hamiltonVector (chartInverse g c) z).1 t :=
    (ContinuousLinearMap.fst ℝ CoordinateSpace Covector).hasFDerivAt.comp_hasDerivAt t (hchart.2 t htJ)
  have hv : v = WithLp.toLp 2 (raiseCovector (chartInverse g c z.1) z.2) :=
    (hD.unique hD').trans (hamiltonVector_fst_eq_raise _ _ (chartInverse_symm g hs c z.1))
  have hlower (w : CoordinateSpace) : B v w = covectorCLM z.2 w := by
    rw [hv]
    exact inverse_raise_lower B (coordinateBilinear_nondegenerate g hn c (cotangentChart_mapsTo c hc).1)
      (coordinateBilinear_symmetric g hs c z.1) z.2 w
  have hv₀ : v ≠ 0 := by
    intro he
    apply (cotangentChart_mem_punctured c (A.curve t) hc (A.punctured g hg hn hs hp ht)).2
    funext i
    have hl := hlower (coordinateBasis i)
    rw [he, map_zero, LinearMap.zero_apply, covectorCLM_apply_basis] at hl
    exact hl.symm
  have hE : symbolNorm (chartInverse g c z.1) z.2 = 0 :=
    (dualEnergy_chart g hn hs c (A.curve t) hc).symm.trans
      ((A.dualEnergy_constant g hg hn hs ht).trans hnp)
  have hnull : B v v = 0 := by
    rw [hlower v, covectorCLM_eval]
    rw [symbolNorm_eq_pair_raise] at hE
    simpa only [hv] using hE
  exact ⟨v, a, hD, hA, hv₀, hnull, hGeo⟩

end Burnett.Geometry.CotangentHamiltonMaximalCurve
