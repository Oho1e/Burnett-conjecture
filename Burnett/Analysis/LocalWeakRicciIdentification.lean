import Burnett.Analysis.LocalWeakRicci

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.LocalWeakRicciIdentification

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative LocalWeakRicci

def linearConnection
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) : Connection :=
  christoffel (matrixInverse (metricComponents g0 y)) (auxiliaryPerturbationJet g0 g0 g1 y)

def connectionDifference
    (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) : Connection := computedConnection g1 y - computedConnection g0 y

theorem abs_product_difference_le (C L : Connection) (a b c d e f : Index) :
    |C a b c * C d e f - L a b c * L d e f| ≤ (‖C‖ + ‖L‖) * ‖C - L‖ := by
  have hc := ConnectionError.abs_firstJet_entry_le_norm C d e f
  have hl := ConnectionError.abs_firstJet_entry_le_norm L a b c
  have hd1 := ConnectionError.abs_firstJet_entry_le_norm (C-L) a b c
  have hd2 := ConnectionError.abs_firstJet_entry_le_norm (C-L) d e f
  calc
    _ = |(C-L) a b c * C d e f + L a b c * (C-L) d e f| := by
      congr 1
      simp only [Pi.sub_apply]
      ring
    _ ≤ |(C-L) a b c * C d e f| + |L a b c * (C-L) d e f| := abs_add_le _ _
    _ ≤ ‖C-L‖ * ‖C‖ + ‖L‖ * ‖C-L‖ := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul hd1 hc (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hl hd2 (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem abs_quadratic_difference_le (C L : Connection) (b c : Index) :
    |quadraticDifference C b c - quadraticDifference L b c| ≤
      32 * (‖C‖ + ‖L‖) * ‖C-L‖ := by
  unfold quadraticDifference
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Index, |(∑ e, (C a a e * C e b c - C a c e * C e b a)) -
        ∑ e, (L a a e * L e b c - L a c e * L e b a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Index, ∑ _ : Index, 2 * ((‖C‖ + ‖L‖) * ‖C-L‖) := by
      apply Finset.sum_le_sum
      intro a _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro e _
      have he : C a a e * C e b c - C a c e * C e b a -
          (L a a e * L e b c - L a c e * L e b a) =
          (C a a e * C e b c - L a a e * L e b c) -
            (C a c e * C e b a - L a c e * L e b a) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by
        have h1 := abs_product_difference_le C L a a e e b c
        have h2 := abs_product_difference_le C L a c e e b a
        linarith)
    _ = _ := by simp; ring

theorem quadratic_replacement_uniform {K : Set CoordinateSpace}
    {C L E : ℕ → CoordinateSpace → Connection}
    (hCE : ∀ n y, C n y = L n y + E n y)
    (hE : TendstoUniformlyOn E (fun _ => 0) atTop K)
    {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ᶠ n in atTop, ∀ y ∈ K, ‖L n y‖ ≤ B) (b c : Index) :
    TendstoUniformlyOn (fun n y => quadraticDifference (C n y) b c -
      quadraticDifference (L n y) b c) (fun _ => 0) atTop K := by
  apply ConnectionError.tendstoUniformlyOn_zero_of_eventually_norm_le_dist
    hE (C := 32 * (2*B+1)) (by positivity)
  filter_upwards [hL, Metric.tendstoUniformlyOn_iff.mp hE 1 zero_lt_one] with n hnL hnE
  intro y hy
  have he : ‖E n y‖ ≤ 1 := by simpa only [dist_zero_left] using (hnE y hy).le
  have hc : ‖C n y‖ ≤ B+1 := by rw [hCE n y]; exact (norm_add_le _ _).trans (add_le_add (hnL y hy) he)
  have hdiff : C n y - L n y = E n y := by rw [hCE n y]; abel
  rw [dist_zero_right, Real.norm_eq_abs]
  calc
    _ ≤ 32 * (‖C n y‖+‖L n y‖) * ‖C n y-L n y‖ := abs_quadratic_difference_le _ _ b c
    _ ≤ 32 * (2*B+1) * ‖E n y‖ := by
      rw [hdiff]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith [hnL y hy]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem linearConnection_component_smoothOn
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (a b d : Index) :
    ContDiffOn ℝ ∞ (fun y => linearConnection (coordinateBilinear g0 c)
      (coordinateBilinear g1 c) y a b d) (chartAt CoordinateSpace c).target := by
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓ1 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g1 h1 hn1 c
  have hΓ0c := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 a) b) d
  have hΓ1c := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ1 a) b) d
  apply ((hΓ1c.sub hΓ0c).sub
    (computedError_component_smoothOn g0 g1 h0 h1 hn0 hn1 c a b d)).congr
  intro y _
  simp only [linearConnection, ConnectionErrorLInfinity.computedError, Pi.sub_apply]
  ring

theorem smoothOn_quadraticDifference {U : Set CoordinateSpace} {C : CoordinateSpace → Connection}
    (hC : ∀ a b d, ContDiffOn ℝ ∞ (fun y => C y a b d) U) (b c : Index) :
    ContDiffOn ℝ ∞ (fun y => quadraticDifference (C y) b c) U :=
  ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun e _ =>
    ((hC a a e).mul (hC e b c)).sub ((hC a c e).mul (hC e b a))))

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

omit hs0 hs hn in
theorem eventual_bound_linearConnection_of_original
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ y ∈ K,
      ‖linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y‖ ≤ B := by
  obtain ⟨D, hD, hraw⟩ := OriginalAdmissibleLocalControl.exists_eventual_rawJet_bound_of_original
    r g0 g h0 hg hn0 hconv hb c K hK hKt
  have hC0 := ManifoldBilinear.contDiffOn_metricComponents_one g0 h0 c
  have hcomp := (BackgroundConnection.continuousOn_components_of_contDiffOn
    (metricComponents (coordinateBilinear g0 c)) _ hC0).mono hKt
  obtain ⟨B, hB, hInv⟩ := InverseField.exists_pos_bound_matrixInverse
    (metricComponents (coordinateBilinear g0 c)) K hK hcomp
    (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g0 hn0 c (hKt hy))
  have hΓ := (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c).continuousOn.mono hKt
  obtain ⟨G, hG, hΓb⟩ := (hK.image_of_continuousOn hΓ).isBounded.exists_pos_norm_le
  have hu := components_uniform_of_physical_C0loc r g g0 hconv c K hK hKt
  refine ⟨6*B*(D+8*G), by positivity, ?_⟩
  filter_upwards [hraw, Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with n hnraw hnsmall
  intro y hy
  have hh : ‖metricComponents (coordinateBilinear (g n) c) y -
      metricComponents (coordinateBilinear g0 c) y‖ ≤ 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hnsmall y hy).le
  have hΓy : ‖computedConnection (coordinateBilinear g0 c) y‖ ≤ G :=
    hΓb _ (mem_image_of_mem _ hy)
  have hJ : ‖auxiliaryPerturbationJet (coordinateBilinear g0 c) (coordinateBilinear g0 c)
      (coordinateBilinear (g n) c) y‖ ≤ D+8*G := by
    have h := PerturbationJet.norm_covariantJet_le
      (computedConnection (coordinateBilinear g0 c) y)
      (metricComponents (coordinateBilinear (g n) c) y - metricComponents (coordinateBilinear g0 c) y)
      (coordinateJet (fun x => metricComponents (coordinateBilinear (g n) c) x -
        metricComponents (coordinateBilinear g0 c) x) y)
    have hm := mul_le_mul hΓy hh (norm_nonneg _) hG.le
    change ‖auxiliaryPerturbationJet (coordinateBilinear g0 c) (coordinateBilinear g0 c)
      (coordinateBilinear (g n) c) y‖ ≤ _ at h
    nlinarith [hnraw y hy]
  apply (ConnectionError.norm_christoffel_le _ _).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hInv y hy) (by norm_num)) hJ
    (norm_nonneg _) (by positivity)

theorem quadratic_replacement_uniform_of_original (b d : Index)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    TendstoUniformlyOn (fun n y =>
      quadraticDifference (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d -
      quadraticDifference (linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d)
      (fun _ => 0) atTop K := by
  obtain ⟨B, hB, hL⟩ := eventual_bound_linearConnection_of_original
    r g0 g h0 hg hn0 hconv hb c K hK hKt
  exact quadratic_replacement_uniform
    (fun n y => connection_difference_eq_linear_plus_error _ _ y)
    (OriginalAdmissibleLocalControl.computedError_uniform_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c K hK hKt) hB hL b d

theorem density_quadratic_replacement_test_of_original (b d : Index)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, (ψ y *
      Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
      (quadraticDifference (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d -
      quadraticDifference (linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y) b d))
      atTop (𝓝 0) := by
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓ0c (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 i) j) k
  have hC (n : ℕ) (i j k : Index) : ContDiffOn ℝ ∞
      (fun y => connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y i j k)
      (chartAt CoordinateSpace c).target := by
    have hΓn := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) c
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓn i) j) k).sub (hΓ0c i j k)
  exact integral_test_local_tendsto_zero (chartAt CoordinateSpace c).open_target
    (contDiff_test_mul_local (chartAt CoordinateSpace c).open_target hψ hsψ
      (smooth_coordinate_volume_factor g0 h0 hn0 c)) hcψ.mul_right
    (tsupport_mul_subset_left.trans hsψ)
    (fun n => (smoothOn_quadraticDifference (hC n) b d).sub
      (smoothOn_quadraticDifference (linearConnection_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c) b d))
    (quadratic_replacement_uniform_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d)

end OriginalData
end Burnett.Analysis.LocalWeakRicciIdentification
