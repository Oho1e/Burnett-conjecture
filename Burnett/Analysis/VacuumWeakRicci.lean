import Burnett.Analysis.LocalWeakRicciIdentification
import Burnett.Analysis.WeakTestCalculus

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.LocalWeakRicciIdentification

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative LocalWeakRicci WeakTestCalculus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem perturbation_component_smoothWeakZero
    (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hconv : LocallyUniformlyConverges r g g0) (c : M) (i j : Index) :
    SmoothWeakZero (chartAt CoordinateSpace c).target (fun n y =>
      metricComponents (coordinateBilinear (g n) c) y i j -
      metricComponents (coordinateBilinear g0 c) y i j) :=
  SmoothWeakZero.of_uniform (chartAt CoordinateSpace c).open_target
    (component_difference_smoothOn g g0 h0 hg c i j)
    (component_difference_uniform_of_physical_C0loc r g g0 hconv c i j)

theorem auxiliary_g0_jet_component_smoothWeakZero
    (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hconv : LocallyUniformlyConverges r g g0) (c : M) (q i j : Index) :
    SmoothWeakZero (chartAt CoordinateSpace c).target (fun n y =>
      auxiliaryPerturbationJet (coordinateBilinear g0 c) (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y q i j) := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hH := perturbation_component_smoothWeakZero r g0 g h0 hg hconv c
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓc (a b d : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) d
  exact SmoothWeakZero.sub hU
    (SmoothWeakZero.sub hU (SmoothWeakZero.directional hU (hH i j) (EuclideanSpace.single q 1))
      (SmoothWeakZero.finset_sum hU Finset.univ (fun e _ =>
        SmoothWeakZero.mul_fixed hU (hH e j) (hΓc e q i))))
    (SmoothWeakZero.finset_sum hU Finset.univ (fun e _ =>
      SmoothWeakZero.mul_fixed hU (hH i e) (hΓc e q j)))

theorem linearConnection_component_smoothWeakZero
    (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n)) (hn0 : IsNondegenerate g0)
    (hconv : LocallyUniformlyConverges r g g0) (c : M) (a b d : Index) :
    SmoothWeakZero (chartAt CoordinateSpace c).target (fun n y =>
      linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d) := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hJ := auxiliary_g0_jet_component_smoothWeakZero r g0 g h0 hg hn0 hconv c
  have hi (i j : Index) := SmoothMetricConnection.contDiffOn_matrixInverse
    (metricComponents (coordinateBilinear g0 c)) (chartAt CoordinateSpace c).target
    (ManifoldBilinear.contDiffOn_metricComponents g0 h0 c)
    (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g0 hn0 c hy) i j
  have h := SmoothWeakZero.finset_sum hU Finset.univ (fun e _ =>
    SmoothWeakZero.mul_fixed hU
      (SmoothWeakZero.sub hU (SmoothWeakZero.add hU (hJ b d e) (hJ d b e)) (hJ e b d))
      ((hi a e).div_const 2))
  apply SmoothWeakZero.congr h
  intro n y
  simp only [linearConnection, christoffel, koszul]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem computedConnection_torsion_free_of_symmetric
    (B : Field (M := M)) (hs : IsSymmetric B) (c : M) (y : CoordinateSpace) (a b d : Index) :
    computedConnection (coordinateBilinear B c) y a b d =
      computedConnection (coordinateBilinear B c) y a d b :=
  christoffel_torsion_free _ _ (coordinateJet_symmetric _ y (Eventually.of_forall (fun x =>
    FiberMetric.covariant_symmetric _ (coordinateBilinear_symmetric B hs c x) coordinateBasis))) a b d

theorem coordinateRicci_component_smoothOn
    (B : Field (M := M)) (hB : IsSmooth B) (hnB : IsNondegenerate B) (c : M) (b d : Index) :
    ContDiffOn ℝ ∞ (fun y => coordinateRicci (computedConnection (coordinateBilinear B c)) y b d)
      (chartAt CoordinateSpace c).target := by
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection B hB hnB c
  have hΓc (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ i) j) k
  have hdΓ (q i j k : Index) : ContDiffOn ℝ ∞ (fun y =>
      fderiv ℝ (fun x => computedConnection (coordinateBilinear B c) x i j k) y
        (EuclideanSpace.single q 1)) (chartAt CoordinateSpace c).target :=
    ((hΓc i j k).fderiv_of_isOpen (chartAt CoordinateSpace c).open_target (by simp)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single q 1))
  unfold coordinateRicci ricci coordinateConnectionJet
  exact ContDiffOn.sum (fun a _ => ((hdΓ a a b d).sub (hdΓ d a b a)).add
    (ContDiffOn.sum (fun e _ => ((hΓc a a e).mul (hΓc e b d)).sub
      ((hΓc a d e).mul (hΓc e b a)))))

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

theorem connectionDifference_component_smoothWeakZero_of_original (a b d : Index) :
    SmoothWeakZero (chartAt CoordinateSpace c).target (fun n y =>
      connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y a b d) := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hE := SmoothWeakZero.of_uniform hU
    (fun n => computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c a b d)
    (error_component_uniform_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d)
  have hL := linearConnection_component_smoothWeakZero r g0 g h0 hg hn0 hconv c a b d
  apply SmoothWeakZero.congr (SmoothWeakZero.add hU hL hE)
  intro n y
  exact congrArg (fun C => C a b d) (connection_difference_eq_linear_plus_error
    (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)

theorem covariant_connectionDifference_component_smoothWeakZero_of_original (q a b d : Index) :
    SmoothWeakZero (chartAt CoordinateSpace c).target (fun n y =>
      covariantDerivative (computedConnection (coordinateBilinear g0 c) y)
        (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
        (coordinateConnectionJet (connectionDifference (coordinateBilinear g0 c)
          (coordinateBilinear (g n) c)) y) q a b d) := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hC := connectionDifference_component_smoothWeakZero_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓc (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ i) j) k
  exact SmoothWeakZero.add hU (SmoothWeakZero.directional hU (hC a b d) (EuclideanSpace.single q 1))
    (SmoothWeakZero.finset_sum hU Finset.univ (fun e _ =>
      SmoothWeakZero.sub hU (SmoothWeakZero.sub hU
        (SmoothWeakZero.mul_fixed hU (hC e b d) (hΓc a q e))
        (SmoothWeakZero.mul_fixed hU (hC a e d) (hΓc e q b)))
        (SmoothWeakZero.mul_fixed hU (hC a b e) (hΓc e q d))))

theorem Ricci_divergence_difference_smoothWeakZero_of_original (b d : Index) :
    SmoothWeakZero (chartAt CoordinateSpace c).target (fun n y =>
      covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
        (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
        (coordinateConnectionJet (connectionDifference (coordinateBilinear g0 c)
          (coordinateBilinear (g n) c)) y) b d) := by
  have hU := (chartAt CoordinateSpace c).open_target
  have hD := covariant_connectionDifference_component_smoothWeakZero_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c
  exact SmoothWeakZero.finset_sum hU Finset.univ (fun a _ =>
    SmoothWeakZero.sub hU (hD a a b d) (hD d a b a))

theorem vacuum_Ricci_quadratic_test_limit_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) {ψ : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, (ψ y *
      Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
      quadraticDifference (linearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d) atTop
      (𝓝 (-(∫ y, (ψ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
        coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d))) := by
  let U := (chartAt CoordinateSpace c).target
  let Φ := fun y => ψ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|
  let Γ0 := computedConnection (coordinateBilinear g0 c)
  let Γn := fun n => computedConnection (coordinateBilinear (g n) c)
  let C := fun n => connectionDifference (coordinateBilinear g0 c) (coordinateBilinear (g n) c)
  let L := fun n => linearConnection (coordinateBilinear g0 c) (coordinateBilinear (g n) c)
  let Div := fun n y => covariantDivergenceDifference (Γ0 y) (C n y) (coordinateConnectionJet (C n) y) b d
  let R := fun y => coordinateRicci Γ0 y b d
  let I0 : ℝ := ∫ y, Φ y * R y
  have hU := (chartAt CoordinateSpace c).open_target
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_test_mul_local hU hψ hsψ
    (smooth_coordinate_volume_factor g0 h0 hn0 c)
  have hcΦ : HasCompactSupport Φ := hcψ.mul_right
  have hsΦ : tsupport Φ ⊆ U := tsupport_mul_subset_left.trans hsψ
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓ0c (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 i) j) k
  have hΓn (n : ℕ) := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) c
  have hΓnc (n : ℕ) (i j k : Index) :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp (hΓn n) i) j) k
  have hC := connectionDifference_component_smoothWeakZero_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c
  have hDiv := Ricci_divergence_difference_smoothWeakZero_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d
  have hiR : Integrable (fun y => Φ y * R y) (volume : Measure CoordinateSpace) :=
    (contDiff_test_mul_local hU hΦ hsΦ (coordinateRicci_component_smoothOn g0 h0 hn0 c b d)).continuous
      |>.integrable_of_hasCompactSupport hcΦ.mul_right
  have hiDiv (n : ℕ) : Integrable (fun y => Φ y * Div n y) :=
    (contDiff_test_mul_local hU hΦ hsΦ (hDiv.1 n)).continuous.integrable_of_hasCompactSupport hcΦ.mul_right
  have hiQC (n : ℕ) : Integrable (fun y => Φ y * quadraticDifference (C n y) b d) :=
    (contDiff_test_mul_local hU hΦ hsΦ (smoothOn_quadraticDifference
      (fun i j k => (hC i j k).1 n) b d)).continuous.integrable_of_hasCompactSupport hcΦ.mul_right
  have hiQL (n : ℕ) : Integrable (fun y => Φ y * quadraticDifference (L n y) b d) :=
    (contDiff_test_mul_local hU hΦ hsΦ (smoothOn_quadraticDifference
      (linearConnection_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c) b d)).continuous
        |>.integrable_of_hasCompactSupport hcΦ.mul_right
  have hv (n : ℕ) (y : CoordinateSpace) (hy : y ∈ U) :
      0 = R y + Div n y + quadraticDifference (C n y) b d := by
    exact coordinateRicci_vacuum_identity Γ0 (Γn n) y
      (computedConnection_torsion_free_of_symmetric g0 hs0 c y)
      (computedConnection_torsion_free_of_symmetric (g n) (hs n) c y)
      (fun i j k => ((hΓ0c i j k).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (fun i j k => ((hΓnc n i j k).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (hVac n y hy) b d
  have hIntegral (n : ℕ) : I0 + (∫ y, Φ y * Div n y) +
      (∫ y, Φ y * quadraticDifference (C n y) b d) = 0 := by
    have hPoint (y : CoordinateSpace) : Φ y * R y + Φ y * Div n y +
        Φ y * quadraticDifference (C n y) b d = 0 := by
      by_cases hy : y ∈ U
      · calc
          _ = Φ y * (R y + Div n y + quadraticDifference (C n y) b d) := by ring
          _ = 0 := by rw [← hv n y hy, mul_zero]
      · have hψ0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hsψ h))
        simp only [Φ, hψ0, zero_mul, add_zero]
    have hOuter := integral_add (hiR.add (hiDiv n)) (hiQC n)
    have hInner := integral_add hiR (hiDiv n)
    simp only [Pi.add_apply] at hOuter hInner
    rw [hInner] at hOuter
    have hz : (∫ y, Φ y * R y + Φ y * Div n y +
        Φ y * quadraticDifference (C n y) b d) = 0 := by
      simp_rw [hPoint]
      exact integral_zero _ _
    exact hOuter.symm.trans hz
  have hDiv0 : Tendsto (fun n => ∫ y, Φ y * Div n y) atTop (𝓝 0) := hDiv.2 Φ hΦ hcΦ hsΦ
  have hQC : Tendsto (fun n => ∫ y, Φ y * quadraticDifference (C n y) b d) atTop (𝓝 (-I0)) := by
    have hConst : Tendsto (fun _ : ℕ => -I0) atTop (𝓝 (-I0)) := tendsto_const_nhds
    have h := hConst.sub hDiv0
    simp only [sub_zero] at h
    apply h.congr
    intro n
    linarith [hIntegral n]
  have hReplacement := density_quadratic_replacement_test_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d hψ hcψ hsψ
  have h := hQC.sub hReplacement
  simp only [sub_zero] at h
  apply h.congr
  intro n
  have hi := integral_sub (hiQC n) (hiQL n)
  simp only [← mul_sub] at hi
  linarith [hi]

theorem vacuum_Ricci_negative_quadratic_test_limit_of_original
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0)
    (b d : Index) {ψ : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ y, (ψ y *
      Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
      (-quadraticDifference (linearConnection (coordinateBilinear g0 c)
        (coordinateBilinear (g n) c) y) b d)) atTop
      (𝓝 (∫ y, (ψ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
        coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d)) := by
  have h := (vacuum_Ricci_quadratic_test_limit_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c hVac b d hψ hcψ hsψ).neg
  simp only [neg_neg] at h
  apply h.congr
  intro n
  rw [← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

end OriginalData
end Burnett.Analysis.LocalWeakRicciIdentification
