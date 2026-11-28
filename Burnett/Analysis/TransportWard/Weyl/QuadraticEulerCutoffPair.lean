import Burnett.Analysis.TransportWard.Weyl.QuadraticEulerAction
import Burnett.Analysis.TransportWard.Weyl.RealEnergyFieldJets

set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option maxRecDepth 3800

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.Analysis.TransportWardSymbol Burnett.A02.FrequencySplit
open scoped BigOperators ComplexConjugate ContDiff Topology

private theorem coordinateDensityEuler_congr_germ {J : Type*} [Fintype J]
    (S : J → Mat) {f g : E → J → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (i : J) :
    coordinateDensityEuler S f x i = coordinateDensityEuler S g x i := by
  have hJet {y : E} (hy : f =ᶠ[𝓝 y] g) (s : ActionSlot J) :
      coordinateMetricFirstJet f y s = coordinateMetricFirstJet g y s := by
    unfold coordinateMetricFirstJet
    rw [hy.fderiv_eq]
  have hFlux (a : Fin 4) (t : ActionSlot J) :
      (fun y => metricActionCoefficient S (a,i) t (assembleMetricComponents S (f y)) *
        coordinateMetricFirstJet f y t) =ᶠ[𝓝 x]
      (fun y => metricActionCoefficient S (a,i) t (assembleMetricComponents S (g y)) *
        coordinateMetricFirstJet g y t) := by
    filter_upwards [h.eventually_nhds] with y hy
    have he : f =ᶠ[𝓝 y] g := hy
    rw [he.eq_of_nhds, hJet he]
  have hD (a : Fin 4) (t : ActionSlot J) := (hFlux a t).fderiv_eq (𝕜 := ℝ)
  simp only [coordinateDensityEuler, h.eq_of_nhds, hJet h, hD]

/-- The compact Weyl output tests the original Euler variation on the chart.
Only the germ of the perturbation on the test's support enters, so its
chart cutoff can be used in the third variation. -/
theorem setIntegral_quadraticEuler_pair_eq_thirdVariation_of_germ
    {J : Type} [Fintype J] (S : J → Mat) (g h₀ : E → J → ℝ) (z w : RealEnergyField J)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hn : ∀ x ∈ U, (assembleMetricComponents S (g x)).det ≠ 0)
    (hW : ∀ i, tsupport (w.val i : E → ℂ) ⊆ K)
    (hCut : ∀ x ∈ K, h₀ =ᶠ[𝓝 x] fun y i => (z.val i y).re) :
    (∫ x in U, ∑ i, conj (w.val i x) *
      Complex.ofReal (deriv (deriv (fun t : ℝ =>
        coordinateDensityEuler S (fun y => g y + t • h₀ y) x i)) 0)).re =
      ∫ x in K, coordinateActionThirdVariationDensity S g
        (fun y i => (z.val i y).re) (fun y i => (w.val i y).re) x := by
  let h (y : E) (i : J) := (z.val i y).re
  let k (y : E) (i : J) := (w.val i y).re
  let Q (f : E → J → ℝ) (x : E) (i : J) := deriv (deriv (fun t : ℝ =>
    coordinateDensityEuler S (fun y => g y + t • f y) x i)) 0
  let D (x : E) := ∑ i, k x i * Q h x i
  have hh : ContDiff ℝ ∞ h := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (z.val i).smooth'
  have hk : ContDiff ℝ ∞ k := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (w.val i).smooth'
  have hWzero {x : E} (hx : x ∉ K) (i : J) : w.val i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hW i hs))
  have hKzero (x : E) (hx : x ∈ U \ K) : k x = 0 := by
    funext i
    change (w.val i x).re = 0
    rw [hWzero hx.2 i, Complex.zero_re]
  have hQ (x : E) (hx : x ∈ K) (i : J) : Q h₀ x i = Q h x i := by
    have hPath (t : ℝ) : coordinateDensityEuler S (fun y => g y + t • h₀ y) x i =
        coordinateDensityEuler S (fun y => g y + t • h y) x i :=
      coordinateDensityEuler_congr_germ S
        ((hCut x hx).mono (fun y hy => congrArg (fun a => g y + t • a) hy)) i
    unfold Q
    rw [funext hPath]
  have hPair (x : E) (hx : x ∈ K) :
      (∑ i, conj (w.val i x) * Complex.ofReal (Q h₀ x i)) = Complex.ofReal (D x) := by
    simp only [D, Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hQ x hx i, w.property i x, ← coe_re_eq_of_conj_eq _ (w.property i x)]
  have hInt : (∫ x in U, ∑ i, conj (w.val i x) * Complex.ofReal (Q h₀ x i)) =
      ∫ x in K, Complex.ofReal (D x) := by
    rw [← integral_indicator hU.measurableSet, ← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact .of_forall fun x => by
      by_cases hx : x ∈ K
      · rw [indicator_of_mem (hKU hx), indicator_of_mem hx, hPair x hx]
      · rw [indicator_of_notMem hx]
        have hz : (∑ i, conj (w.val i x) * Complex.ofReal (Q h₀ x i)) = 0 := by
          simp only [hWzero hx, map_zero, zero_mul, Finset.sum_const_zero]
        by_cases hu : x ∈ U
        · rw [indicator_of_mem hu, hz]
        · rw [indicator_of_notMem hu]
  change (∫ x in U, ∑ i, conj (w.val i x) * Complex.ofReal (Q h₀ x i)).re = _
  have hRealIntegral : (∫ x in K, Complex.ofReal (D x)) = Complex.ofReal (∫ x in K, D x) :=
    integral_ofReal (𝕜 := ℂ) (f := D)
  rw [hInt, hRealIntegral, Complex.ofReal_re]
  exact integral_quadraticCoordinateDensityEuler_pair_eq_thirdVariation
    S g h k hU hK hKU hg hh.contDiffOn hk.contDiffOn hn hKzero

end Burnett.V03.Palatini
