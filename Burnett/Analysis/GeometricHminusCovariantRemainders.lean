import Burnett.Analysis.GeometricHminusRemainders

set_option autoImplicit false

noncomputable section
set_option synthInstance.maxHeartbeats 200000

namespace Burnett.Analysis.GeometricHminusRemainders

open MeasureTheory Filter Set
open scoped ContDiff Manifold Topology ENNReal BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open CurvatureDifference LocalWeakDerivative

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem covariant_error_component_smoothOn
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M) (q a b d : Index) :
    ContDiffOn ℝ ∞ (fun y => covariantDerivative
      (computedConnection (coordinateBilinear g0 c) y)
      (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear g1 c) y)
      (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
        (coordinateBilinear g0 c) (coordinateBilinear g1 c)) y) q a b d)
      (chartAt CoordinateSpace c).target := by
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓc (i j k : Index) := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ i) j) k
  have hE := LocalWeakRicci.computedError_component_smoothOn g0 g1 h0 h1 hn0 hn1 c
  have hDE : ContDiffOn ℝ ∞ (fun y => fderiv ℝ (fun x =>
      ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear g1 c) x a b d) y
      (EuclideanSpace.single q 1)) (chartAt CoordinateSpace c).target :=
    ((hE a b d).fderiv_of_isOpen (chartAt CoordinateSpace c).open_target (by simp)).clm_apply contDiffOn_const
  unfold covariantDerivative coordinateConnectionJet
  exact hDE.add (ContDiffOn.sum (fun e _ =>
    (((hΓc a q e).mul (hE e b d)).sub ((hΓc e q b).mul (hE a e d))).sub
      ((hΓc e q d).mul (hE a b e))))

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

theorem coefficient_covariant_error_has_strong_realization_of_original (q a b d : Index)
    {χ A : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target)
    (hA : ContDiffOn ℝ ∞ A (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          ((χ y * A y) *
            covariantDerivative (computedConnection (coordinateBilinear g0 c) y)
              (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
              (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
                (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) q a b d)) ∧
      Tendsto F atTop (𝓝 0) := by
  let U := (chartAt CoordinateSpace c).target
  let ρ := A
  let Φ := fun y => χ y * ρ y
  let Γ := computedConnection (coordinateBilinear g0 c)
  let E := fun n => ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c)
  have hU := (chartAt CoordinateSpace c).open_target
  have hρ : ContDiffOn ℝ ∞ ρ U := hA
  have hΦ : ContDiff ℝ ∞ Φ := localized_contDiff hU hχ hsχ hρ
  have hcΦ : HasCompactSupport Φ := hcχ.mul_right
  have hsΦ : tsupport Φ ⊆ U := tsupport_mul_subset_left.trans hsχ
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓc (i j k : Index) : ContDiffOn ℝ ∞ (fun y => Γ y i j k) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ i) j) k
  have hEc (n : ℕ) (i j k : Index) : ContDiffOn ℝ ∞ (fun y => E n y i j k) U :=
    LocalWeakRicci.computedError_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c i j k
  obtain ⟨P, hP, hP0⟩ := error_localized_partial_has_strong_realization_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c a b d hΦ hcΦ hsΦ (EuclideanSpace.single q 1)
  have hVal (u v w i j k : Index) : ∃ V : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), V n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          (Φ y * (Γ y u v w * E n y i j k))) ∧ Tendsto V atTop (𝓝 0) := by
    obtain ⟨V, hV, hV0⟩ := coefficient_error_localized_value_has_strong_realization_of_original
      r g0 g h0 hg hs0 hs hn0 hn hconv hb c i j k hχ hcχ hsχ (hρ.mul (hΓc u v w))
    refine ⟨V, ?_, hV0⟩
    intro n φ
    apply (hV n φ).trans
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [Φ]
    ring
  choose V hV hV0 using hVal
  let F : ℕ → HminusStrongL2.Hminus := fun n => P n + ∑ e : Index,
    (V a q e e b d n - V e q b a e d n - V e q d a b e n)
  refine ⟨F, ?_, ?_⟩
  · intro n φ
    have hI {p : CoordinateSpace → ℝ} (hp : ContDiffOn ℝ ∞ p U) :
        Integrable (fun y => (φ : CoordinateSpace → ℝ) y * (Φ y * p y)) := by
      simpa only [mul_assoc] using (contDiff_test_mul_local hU
        ((Burnett.X02.SobolevTestJet.test_smooth φ).mul hΦ)
        (tsupport_mul_subset_right.trans hsΦ) hp).continuous.integrable_of_hasCompactSupport hcΦ.mul_left.mul_right
    have hDp : ContDiffOn ℝ ∞ (fun y => fderiv ℝ (fun x => E n x a b d) y (EuclideanSpace.single q 1)) U :=
      ((hEc n a b d).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    let A := fun e y => (φ : CoordinateSpace → ℝ) y * (Φ y * (Γ y a q e * E n y e b d))
    let B := fun e y => (φ : CoordinateSpace → ℝ) y * (Φ y * (Γ y e q b * E n y a e d))
    let C := fun e y => (φ : CoordinateSpace → ℝ) y * (Φ y * (Γ y e q d * E n y a b e))
    let D := fun y => (φ : CoordinateSpace → ℝ) y *
      (Φ y * fderiv ℝ (fun x => E n x a b d) y (EuclideanSpace.single q 1))
    have hiA (e : Index) : Integrable (A e) := hI ((hΓc a q e).mul (hEc n e b d))
    have hiB (e : Index) : Integrable (B e) := hI ((hΓc e q b).mul (hEc n a e d))
    have hiC (e : Index) : Integrable (C e) := hI ((hΓc e q d).mul (hEc n a b e))
    have hiD : Integrable D := hI hDp
    have split (e : Index) : (∫ y, A e y - B e y - C e y) =
        (∫ y, A e y) - (∫ y, B e y) - (∫ y, C e y) := by
      have ho := integral_sub ((hiA e).sub (hiB e)) (hiC e)
      have hi := integral_sub (hiA e) (hiB e)
      change (∫ y, A e y - B e y - C e y) = (∫ y, A e y - B e y) - (∫ y, C e y) at ho
      change (∫ y, A e y - B e y) = (∫ y, A e y) - (∫ y, B e y) at hi
      rw [hi] at ho
      exact ho
    have hp (y : CoordinateSpace) : (φ : CoordinateSpace → ℝ) y *
        (Φ y * covariantDerivative (Γ y) (E n y) (coordinateConnectionJet (E n) y) q a b d) =
        D y + ∑ e : Index, (A e y - B e y - C e y) := by
      simp only [covariantDerivative, coordinateConnectionJet, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [A, B, C]
      ring
    have hInt : (∫ y, (φ : CoordinateSpace → ℝ) y *
        (Φ y * covariantDerivative (Γ y) (E n y) (coordinateConnectionJet (E n) y) q a b d)) =
        (∫ y, D y) + ∑ e : Index, ((∫ y, A e y) - (∫ y, B e y) - (∫ y, C e y)) := by
      simp_rw [hp]
      have hiT (e : Index) : Integrable (fun y => A e y - B e y - C e y) :=
        ((hiA e).sub (hiB e)).sub (hiC e)
      have hiSum : Integrable (fun y => ∑ e : Index, (A e y - B e y - C e y)) :=
        integrable_finset_sum Finset.univ (fun e _ => hiT e)
      rw [integral_add hiD hiSum, integral_finset_sum Finset.univ (fun e _ => hiT e)]
      simp_rw [split]
    calc
      F n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) =
          P n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) + ∑ e : Index,
          (V a q e e b d n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) -
            V e q b a e d n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) -
            V e q d a b e n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ)) := by
        simp only [F, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply]
      _ = (∫ y, D y) + ∑ e : Index, ((∫ y, A e y) - (∫ y, B e y) - (∫ y, C e y)) := by
        rw [hP n φ]
        simp_rw [hV]
        rfl
      _ = _ := hInt.symm
  · have he (e : Index) := ((hV0 a q e e b d).sub (hV0 e q b a e d)).sub (hV0 e q d a b e)
    have hsum := tendsto_finset_sum Finset.univ (fun e _ => he e)
    simpa only [sub_zero, Finset.sum_const_zero, add_zero] using hP0.add hsum

theorem coefficient_Ricci_error_divergence_has_strong_realization_of_original (b d : Index)
    {χ A : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target)
    (hA : ContDiffOn ℝ ∞ A (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          ((χ y * A y) *
            covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
              (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
              (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
                (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) b d)) ∧
      Tendsto F atTop (𝓝 0) := by
  have hCov := fun (q a e f : Index) => coefficient_covariant_error_has_strong_realization_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c q a e f hχ hcχ hsχ hA
  choose F hF hF0 using hCov
  let G : ℕ → HminusStrongL2.Hminus := fun n => ∑ a : Index, (F a a b d n - F d a b a n)
  refine ⟨G, ?_, ?_⟩
  · intro n φ
    let U := (chartAt CoordinateSpace c).target
    let Φ := fun y => χ y * A y
    let Γ := computedConnection (coordinateBilinear g0 c)
    let E := ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c)
    have hU := (chartAt CoordinateSpace c).open_target
    have hΦ : ContDiff ℝ ∞ Φ := localized_contDiff hU hχ hsχ hA
    have hcΦ : HasCompactSupport Φ := hcχ.mul_right
    have hsΦ : tsupport Φ ⊆ U := tsupport_mul_subset_left.trans hsχ
    have hI (q a e f : Index) : Integrable (fun y => (φ : CoordinateSpace → ℝ) y *
        (Φ y * covariantDerivative (Γ y) (E y) (coordinateConnectionJet E y) q a e f)) := by
      simpa only [mul_assoc] using (contDiff_test_mul_local hU
        ((Burnett.X02.SobolevTestJet.test_smooth φ).mul hΦ) (tsupport_mul_subset_right.trans hsΦ)
        (covariant_error_component_smoothOn g0 (g n) h0 (hg n) hn0 (hn n) c q a e f)).continuous
          |>.integrable_of_hasCompactSupport hcΦ.mul_left.mul_right
    let A := fun a y => (φ : CoordinateSpace → ℝ) y *
      (Φ y * covariantDerivative (Γ y) (E y) (coordinateConnectionJet E y) a a b d)
    let B := fun a y => (φ : CoordinateSpace → ℝ) y *
      (Φ y * covariantDerivative (Γ y) (E y) (coordinateConnectionJet E y) d a b a)
    have hiD (a : Index) : Integrable (fun y => A a y - B a y) := (hI a a b d).sub (hI d a b a)
    have split (a : Index) : (∫ y, A a y - B a y) = (∫ y, A a y) - (∫ y, B a y) := by
      have h := integral_sub (hI a a b d) (hI d a b a)
      change (∫ y, A a y - B a y) = (∫ y, A a y) - (∫ y, B a y) at h
      exact h
    have hp (y : CoordinateSpace) : (φ : CoordinateSpace → ℝ) y *
        (Φ y * covariantDivergenceDifference (Γ y) (E y) (coordinateConnectionJet E y) b d) =
        ∑ a : Index, (A a y - B a y) := by
      simp only [covariantDivergenceDifference, Finset.mul_sum, mul_sub]
      rfl
    calc
      G n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) = ∑ a : Index,
          (F a a b d n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ) -
            F d a b a n (Burnett.X02.GraphDual.testMap Burnett.X02.SobolevTestJet.J φ)) := by
        simp only [G, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply]
      _ = ∑ a : Index, ((∫ y, A a y) - (∫ y, B a y)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hF a a b d n φ, hF d a b a n φ]
      _ = ∑ a : Index, ∫ y, A a y - B a y := by
        apply Finset.sum_congr rfl
        intro a _
        exact (split a).symm
      _ = ∫ y, ∑ a : Index, (A a y - B a y) :=
        (integral_finset_sum Finset.univ (fun a _ => hiD a)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun y => (hp y).symm))
  · have h := tendsto_finset_sum Finset.univ (fun a _ => (hF0 a a b d).sub (hF0 d a b a))
    simpa only [sub_zero, Finset.sum_const_zero] using h

theorem covariant_error_has_strong_realization_of_original (q a b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          (χ y * covariantDerivative (computedConnection (coordinateBilinear g0 c) y)
            (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
            (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
              (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) q a b d)) ∧
      Tendsto F atTop (𝓝 0) := by
  simpa only [mul_one] using coefficient_covariant_error_has_strong_realization_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c q a b d (A := fun _ => 1) hχ hcχ hsχ contDiffOn_const

theorem density_covariant_error_has_strong_realization_of_original (q a b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          ((χ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
            covariantDerivative (computedConnection (coordinateBilinear g0 c) y)
              (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
              (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
                (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) q a b d)) ∧
      Tendsto F atTop (𝓝 0) :=
  coefficient_covariant_error_has_strong_realization_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c q a b d
    hχ hcχ hsχ (smooth_coordinate_volume_factor g0 h0 hn0 c)

theorem Ricci_error_divergence_has_strong_realization_of_original (b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          (χ y * covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
            (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
            (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
              (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) b d)) ∧
      Tendsto F atTop (𝓝 0) := by
  simpa only [mul_one] using coefficient_Ricci_error_divergence_has_strong_realization_of_original
    r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d (A := fun _ => 1) hχ hcχ hsχ contDiffOn_const

theorem density_Ricci_error_divergence_has_strong_realization_of_original (b d : Index)
    {χ : CoordinateSpace → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    ∃ F : ℕ → HminusStrongL2.Hminus,
      (∀ n (φ : Burnett.X02.SobolevTestJet.D), F n (Burnett.X02.GraphDual.testMap
        Burnett.X02.SobolevTestJet.J φ) = ∫ y, (φ : CoordinateSpace → ℝ) y *
          ((χ y * Real.sqrt |Matrix.det (metricComponents (coordinateBilinear g0 c) y)|) *
            covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
              (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
              (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
                (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) b d)) ∧
      Tendsto F atTop (𝓝 0) :=
  coefficient_Ricci_error_divergence_has_strong_realization_of_original r g0 g h0 hg hs0 hs hn0 hn hconv hb c b d
    hχ hcχ hsχ (smooth_coordinate_volume_factor g0 h0 hn0 c)

end OriginalData
end Burnett.Analysis.GeometricHminusRemainders
