import Burnett.Geometry.OriginalAdmissibleLocalControl
import Burnett.Analysis.LocalWeakDerivative
import Burnett.Geometry.CurvatureDifference

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.LocalWeakRicci

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open LocalWeakDerivative

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem computedError_component_smoothOn
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (a b d : Index) :
    ContDiffOn ℝ ∞ (fun y => ConnectionErrorLInfinity.computedError
      (coordinateBilinear g0 c) (coordinateBilinear g1 c) y a b d)
      (chartAt CoordinateSpace c).target := by
  let U := (chartAt CoordinateSpace c).target
  have hG0 := ManifoldBilinear.contDiffOn_metricComponents g0 h0 c
  have hG1 := ManifoldBilinear.contDiffOn_metricComponents g1 h1 c
  have hH (i j : Index) : ContDiffOn ℝ ∞ (fun y =>
      (metricComponents (coordinateBilinear g1 c) y -
        metricComponents (coordinateBilinear g0 c) y) i j) U :=
    (hG1 i j).sub (hG0 i j)
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓ1 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g1 h1 hn1 c
  have hΓ0c (i j k : Index) :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 i) j) k
  have hΓ1c (i j k : Index) :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ1 i) j) k
  have hJ (i j k : Index) : ContDiffOn ℝ ∞ (fun y =>
      auxiliaryPerturbationJet (coordinateBilinear g0 c) (coordinateBilinear g0 c)
        (coordinateBilinear g1 c) y i j k) U := by
    exact ((SmoothMetricConnection.contDiffOn_coordinateJet _ U
      (chartAt CoordinateSpace c).open_target hH i j k).sub
      (ContDiffOn.sum (fun e _ => (hΓ0c e i j).mul (hH e k)))).sub
      (ContDiffOn.sum (fun e _ => (hΓ0c e i k).mul (hH j e)))
  have hi (i j : Index) := SmoothMetricConnection.contDiffOn_matrixInverse
    (metricComponents (coordinateBilinear g0 c)) U hG0
    (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g0 hn0 c hy) i j
  have hL : ContDiffOn ℝ ∞ (fun y =>
      christoffel (matrixInverse (metricComponents (coordinateBilinear g0 c) y))
        (auxiliaryPerturbationJet (coordinateBilinear g0 c) (coordinateBilinear g0 c)
          (coordinateBilinear g1 c) y) a b d) U :=
    ContDiffOn.sum (fun e _ => (hi a e).mul
      ((((hJ b d e).add (hJ d b e)).sub (hJ e b d)).div_const 2))
  exact ((hΓ1c a b d).sub (hΓ0c a b d)).sub hL

theorem connection_difference_eq_linear_plus_error
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (y : CoordinateSpace) :
    computedConnection g1 y - computedConnection g0 y =
      christoffel (matrixInverse (metricComponents g0 y)) (auxiliaryPerturbationJet g0 g0 g1 y) +
        ConnectionErrorLInfinity.computedError g0 g1 y := by
  unfold ConnectionErrorLInfinity.computedError
  abel

section OriginalData

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
variable (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
  (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
  (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
  (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n))
  (hconv : LocallyUniformlyConverges r g g0)
  (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
    eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g0 m)) ∞
      ((ManifoldVolume.geometricMeasure g0).restrict S) ≤ ENNReal.ofReal D)
  (c : M)

include r h0 hg hs0 hs hn0 hn hconv hb

theorem error_component_uniform_of_original (a b d : Index)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n y => ConnectionErrorLInfinity.computedError
      (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d)
      (fun _ => 0) atTop K := by
  have ht := OriginalAdmissibleLocalControl.computedError_uniform_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c K hK hKt
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hnE
  intro y hy
  have hc := ConnectionError.abs_firstJet_entry_le_norm
    (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
      (coordinateBilinear (g n) c) y) a b d
  have hsmall : ‖ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
      (coordinateBilinear (g n) c) y‖ < ε := by
    simpa only [dist_zero_left] using hnE y hy
  simpa only [dist_zero_left, Real.norm_eq_abs] using hc.trans_lt hsmall

theorem error_value_test_of_original (a b d : Index) {ψ A : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (hA : ContDiffOn ℝ ∞ A (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, (ψ y * A y) * ConnectionErrorLInfinity.computedError
      (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d) atTop (𝓝 0) :=
  integral_test_local_tendsto_zero (chartAt CoordinateSpace c).open_target
    (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hψ hsψ hA)
    hcψ.mul_right (tsupport_mul_subset_left.trans hsψ)
    (fun n => computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c a b d)
    (error_component_uniform_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d)

theorem error_derivative_test_of_original (a b d : Index) {ψ A : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (hA : ContDiffOn ℝ ∞ A (chartAt CoordinateSpace c).target) (v : CoordinateSpace) :
    Tendsto (fun n => ∫ y, ψ y * A y * fderiv ℝ (fun x =>
      ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) x a b d) y v) atTop (𝓝 0) :=
  integral_test_coefficient_directional_tendsto_zero (chartAt CoordinateSpace c).open_target
    hψ hcψ hsψ hA
    (fun n => computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c a b d)
    (error_component_uniform_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d) v

theorem density_error_derivative_test_of_original (a b d : Index) {ψ A : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target)
    (hA : ContDiffOn ℝ ∞ A (chartAt CoordinateSpace c).target) (v : CoordinateSpace) :
    Tendsto (fun n => ∫ y, ψ y *
      (Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)| * A y) *
      fderiv ℝ (fun x => ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) x a b d) y v) atTop (𝓝 0) :=
  error_derivative_test_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d
    hψ hcψ hsψ ((smooth_coordinate_volume_factor g0 h0 hn0 c).mul hA) v

theorem density_connection_error_test_of_original (a b d i j k : Index)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, (ψ y *
      (Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)| *
        computedConnection (coordinateBilinear g0 c) y i j k)) *
      ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y a b d) atTop (𝓝 0) := by
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓijk := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ i) j) k
  exact error_value_test_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d
    hψ hcψ hsψ ((smooth_coordinate_volume_factor g0 h0 hn0 c).mul hΓijk)

theorem density_covariant_error_derivative_test_of_original (q a b d : Index)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, (ψ y *
      Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
      CurvatureDifference.covariantDerivative (computedConnection (coordinateBilinear g0 c) y)
        (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
          (coordinateBilinear (g n) c) y)
        (CurvatureDifference.coordinateConnectionJet
          (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
            (coordinateBilinear (g n) c)) y) q a b d) atTop (𝓝 0) := by
  let U := (chartAt CoordinateSpace c).target
  let Φ := fun y => ψ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|
  let Γ := computedConnection (coordinateBilinear g0 c)
  let E := fun n => ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c)
    (coordinateBilinear (g n) c)
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_test_mul_local (chartAt CoordinateSpace c).open_target
    hψ hsψ (smooth_coordinate_volume_factor g0 h0 hn0 c)
  have hcΦ : HasCompactSupport Φ := hcψ.mul_right
  have hsΦ : tsupport Φ ⊆ U := tsupport_mul_subset_left.trans hsψ
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓc (i j k : Index) : ContDiffOn ℝ ∞ (fun y => Γ y i j k) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ i) j) k
  have hEc (n : ℕ) (i j k : Index) : ContDiffOn ℝ ∞ (fun y => E n y i j k) U :=
    computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c i j k
  have hi (n : ℕ) (u v w i j k : Index) :
      Integrable (fun y => (Φ y * Γ y u v w) * E n y i j k) := by
    simpa only [mul_assoc] using
      (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hΦ hsΦ
        ((hΓc u v w).mul (hEc n i j k))).continuous.integrable_of_hasCompactSupport
          hcΦ.mul_right
  have hl (u v w i j k : Index) : Tendsto
      (fun n => ∫ y, (Φ y * Γ y u v w) * E n y i j k) atTop (𝓝 0) :=
    error_value_test_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c i j k
      hΦ hcΦ hsΦ (hΓc u v w)
  let D := fun n y => Φ y * fderiv ℝ (fun x => E n x a b d) y (EuclideanSpace.single q 1)
  let A := fun n e y => (Φ y * Γ y a q e) * E n y e b d -
    (Φ y * Γ y e q b) * E n y a e d - (Φ y * Γ y e q d) * E n y a b e
  have hiD (n : ℕ) : Integrable (D n) :=
    (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hΦ hsΦ
      (((hEc n a b d).fderiv_of_isOpen (chartAt CoordinateSpace c).open_target (by simp)).clm_apply
        contDiffOn_const)).continuous.integrable_of_hasCompactSupport hcΦ.mul_right
  have hiA (n : ℕ) (e : Index) : Integrable (A n e) :=
    ((hi n a q e e b d).sub (hi n e q b a e d)).sub (hi n e q d a b e)
  have hD : Tendsto (fun n => ∫ y, D n y) atTop (𝓝 0) :=
    error_derivative_test_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d
      hψ hcψ hsψ (smooth_coordinate_volume_factor g0 h0 hn0 c) (EuclideanSpace.single q 1)
  have hA (e : Index) : Tendsto (fun n => ∫ y, A n e y) atTop (𝓝 0) := by
    have h := ((hl a q e e b d).sub (hl e q b a e d)).sub (hl e q d a b e)
    simp only [sub_zero] at h
    apply h.congr
    intro n
    dsimp only [A]
    have hOuter := integral_sub ((hi n a q e e b d).sub (hi n e q b a e d)) (hi n e q d a b e)
    have hInner := integral_sub (hi n a q e e b d) (hi n e q b a e d)
    simp only [Pi.sub_apply] at hOuter hInner
    rw [hInner] at hOuter
    exact hOuter.symm
  have hsum : Tendsto (fun n => ∑ e : Index, ∫ y, A n e y) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun e _ => hA e)
  have heq (n : ℕ) :
      (∫ y, Φ y * CurvatureDifference.covariantDerivative (Γ y) (E n y)
        (CurvatureDifference.coordinateConnectionJet (E n) y) q a b d) =
        (∫ y, D n y) + ∑ e : Index, ∫ y, A n e y := by
    have hp (y : CoordinateSpace) :
        Φ y * CurvatureDifference.covariantDerivative (Γ y) (E n y)
          (CurvatureDifference.coordinateConnectionJet (E n) y) q a b d =
          D n y + ∑ e : Index, A n e y := by
      simp only [CurvatureDifference.covariantDerivative, CurvatureDifference.coordinateConnectionJet,
        mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [A]
      ring
    simp_rw [hp]
    rw [integral_add (hiD n) (integrable_finset_sum _ (fun e _ => hiA n e)),
      integral_finset_sum _ (fun e _ => hiA n e)]
  have h := hD.add hsum
  simp only [add_zero] at h
  exact h.congr (fun n => (heq n).symm)

end OriginalData
end Burnett.Analysis.LocalWeakRicci
