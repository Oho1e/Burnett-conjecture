import Burnett.Geometry.FlatRigidity.WeakCurvature
import Burnett.Analysis.LocalWeakRicciIdentification

set_option autoImplicit false

noncomputable section

namespace Burnett.FlatRigidity

open MeasureTheory Filter Set Burnett.RicciSymbol Burnett.Geometry
open Burnett.Analysis.LocalWeakRicciIdentification Burnett.Analysis.LocalWeakRicci
open ConnectionDifference BackgroundConnection InverseField AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology ENNReal BigOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Uniform local control of every actual Christoffel field, including the early indices. -/
theorem computedConnection_uniform_bound_of_original
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n y, y ∈ K → ‖computedConnection (coordinateBilinear (g n) c) y‖ ≤ C := by
  let G₀ := coordinateBilinear g₀ c
  let G (n : ℕ) := coordinateBilinear (g n) c
  obtain ⟨B, hB, hlin⟩ := eventual_bound_linearConnection_of_original r g₀ g h₀ hg hn₀ hconv hb c K hK hKU
  have hE := OriginalAdmissibleLocalControl.computedError_uniform_of_original
    r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb c K hK hKU
  have hΓ₀ := (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g₀ h₀ hn₀ c).continuousOn.mono hKU
  obtain ⟨A, hA, hbA⟩ := (hK.image_of_continuousOn hΓ₀).isBounded.exists_pos_norm_le
  have hlate : ∀ᶠ n in atTop, ∀ y ∈ K, ‖computedConnection (G n) y‖ ≤ B + 1 + A := by
    filter_upwards [hlin, Metric.tendstoUniformlyOn_iff.mp hE 1 zero_lt_one] with n hBn hEn
    intro y hy
    have hEy : ‖ConnectionErrorLInfinity.computedError G₀ (G n) y‖ ≤ 1 := by
      simpa only [dist_zero_left] using (hEn y hy).le
    have hAy : ‖computedConnection G₀ y‖ ≤ A := hbA _ (mem_image_of_mem _ hy)
    have hsplit : computedConnection (G n) y - computedConnection G₀ y =
        linearConnection G₀ (G n) y + ConnectionErrorLInfinity.computedError G₀ (G n) y :=
      connection_difference_eq_linear_plus_error G₀ (G n) y
    rw [sub_eq_iff_eq_add.mp hsplit]
    have hL : ‖linearConnection G₀ (G n) y‖ ≤ B := hBn y hy
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hL hEy)) hAy)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlate
  have hcompact (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ‖computedConnection (G n) y‖ ≤ C := by
    have hΓ := (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) c).continuousOn.mono hKU
    obtain ⟨C, hC, hc⟩ := (hK.image_of_continuousOn hΓ).isBounded.exists_pos_norm_le
    exact ⟨C, hC, fun y hy => hc _ (mem_image_of_mem _ hy)⟩
  choose C hC hbound using hcompact
  have hsum : 0 ≤ ∑ j : Fin N, C j := Finset.sum_nonneg fun _ _ => (hC _).le
  have hbase : 0 ≤ B + 1 + A := by positivity
  refine ⟨B + 1 + A + ∑ j : Fin N, C j, add_nonneg hbase hsum, ?_⟩
  intro n y hy
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge y hy).trans (le_add_of_nonneg_right hsum)
  · let j : Fin N := ⟨n, Nat.lt_of_not_ge hlarge⟩
    have hj : C n ≤ ∑ k : Fin N, C k :=
      Finset.single_le_sum (f := fun k : Fin N => C k) (fun k _ => (hC k).le) (Finset.mem_univ j)
    exact (hbound n y hy).trans (hj.trans (le_add_of_nonneg_left hbase))

end Burnett.FlatRigidity

namespace Burnett.FlatRigidity

open MeasureTheory Filter Set Burnett.RicciSymbol Burnett.Geometry
open Burnett.Analysis.LocalWeakDerivative
open ConnectionDifference BackgroundConnection AuxiliaryConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology BigOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Testing the actual background covariant first derivative of the metric difference. -/
theorem auxiliaryPerturbationJet_test_of_original
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hn₀ : IsNondegenerate g₀)
    (hconv : LocallyUniformlyConverges r g g₀) (c : M) (d i j : Index)
    {ψ : CoordinateSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (chartAt CoordinateSpace c).target) :
    Tendsto (fun n => ∫ x, ψ x * auxiliaryPerturbationJet (coordinateBilinear g₀ c)
      (coordinateBilinear g₀ c) (coordinateBilinear (g n) c) x d i j) atTop (𝓝 0) := by
  let U := (chartAt CoordinateSpace c).target
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  let G₀ := coordinateBilinear g₀ c
  let G (n : ℕ) := coordinateBilinear (g n) c
  let H (n : ℕ) (x : CoordinateSpace) := metricComponents (G n) x - metricComponents G₀ x
  let Γ := computedConnection G₀
  let J (n : ℕ) (x : CoordinateSpace) : ℝ := ψ x * coordinateJet (H n) x d i j
  let L (n : ℕ) (e : Index) (x : CoordinateSpace) : ℝ := (ψ x * Γ x e d i) * H n x e j
  let R (n : ℕ) (e : Index) (x : CoordinateSpace) : ℝ := (ψ x * Γ x e d j) * H n x i e
  have hH (n : ℕ) (a b : Index) : ContDiffOn ℝ ∞ (fun x => H n x a b) U :=
    component_difference_smoothOn g g₀ h₀ hg c a b n
  have hsmall (a b : Index) (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ U) :
      TendstoUniformlyOn (fun n x => H n x a b) (fun _ => 0) atTop K :=
    component_difference_uniform_of_physical_C0loc r g g₀ hconv c a b K hK hKU
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g₀ h₀ hn₀ c
  have hΓc (e a b : Index) : ContDiffOn ℝ ∞ (fun x => Γ x e a b) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ e) a) b
  have hJ (n : ℕ) : ContDiffOn ℝ ∞ (fun x => coordinateJet (H n) x d i j) U :=
    SmoothMetricConnection.contDiffOn_coordinateJet (H n) U hU (hH n) d i j
  have intJ (n : ℕ) : Integrable (J n) :=
    (contDiff_test_mul_local hU hψ hsψ (hJ n)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  have intL (n : ℕ) (e : Index) : Integrable (L n e) :=
    (contDiff_test_mul_local hU (contDiff_test_mul_local hU hψ hsψ (hΓc e d i))
      (tsupport_mul_subset_left.trans hsψ) (hH n e j)).continuous.integrable_of_hasCompactSupport
      hcψ.mul_right.mul_right
  have intR (n : ℕ) (e : Index) : Integrable (R n e) :=
    (contDiff_test_mul_local hU (contDiff_test_mul_local hU hψ hsψ (hΓc e d j))
      (tsupport_mul_subset_left.trans hsψ) (hH n i e)).continuous.integrable_of_hasCompactSupport
      hcψ.mul_right.mul_right
  have limJ : Tendsto (fun n => ∫ x, J n x) atTop (𝓝 0) := by
    have h := original_component_first_derivative_test r g g₀ h₀ hg hconv c i j hψ hcψ hsψ
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : CoordinateSpace => (1 : ℝ)) U) (EuclideanSpace.single d 1)
    simpa only [J, coordinateJet, H, G, G₀, Pi.sub_apply, mul_one] using h
  have limL (e : Index) : Tendsto (fun n => ∫ x, L n e x) atTop (𝓝 0) :=
    integral_test_local_tendsto_zero hU (contDiff_test_mul_local hU hψ hsψ (hΓc e d i))
      hcψ.mul_right (tsupport_mul_subset_left.trans hsψ) (fun n => hH n e j) (hsmall e j)
  have limR (e : Index) : Tendsto (fun n => ∫ x, R n e x) atTop (𝓝 0) :=
    integral_test_local_tendsto_zero hU (contDiff_test_mul_local hU hψ hsψ (hΓc e d j))
      hcψ.mul_right (tsupport_mul_subset_left.trans hsψ) (fun n => hH n i e) (hsmall i e)
  have limsumL : Tendsto (fun n => ∑ e, ∫ x, L n e x) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun e _ => limL e)
  have limsumR : Tendsto (fun n => ∑ e, ∫ x, R n e x) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun e _ => limR e)
  have expand (n : ℕ) : (∫ x, ψ x * auxiliaryPerturbationJet G₀ G₀ (G n) x d i j) =
      (∫ x, J n x) - (∑ e, ∫ x, L n e x) - ∑ e, ∫ x, R n e x := by
    have hpoint : (fun x => ψ x * auxiliaryPerturbationJet G₀ G₀ (G n) x d i j) =
        fun x => J n x - (∑ e, L n e x) - ∑ e, R n e x := by
      funext x
      simp only [auxiliaryPerturbationJet, covariantJet, J, L, R, Γ, H, mul_sub, Finset.mul_sum, mul_assoc]
    rw [hpoint]
    have hIntL := integrable_finset_sum Finset.univ (fun e _ => intL n e)
    have hIntR := integrable_finset_sum Finset.univ (fun e _ => intR n e)
    calc
      _ = (∫ x, J n x - ∑ e, L n e x) - (∫ x, ∑ e, R n e x) :=
        integral_sub ((intJ n).sub hIntL) hIntR
      _ = _ := by
        have hl : (∫ x, J n x - ∑ e, L n e x) = (∫ x, J n x) - (∫ x, ∑ e, L n e x) :=
          integral_sub (intJ n) hIntL
        rw [hl, integral_finset_sum Finset.univ (fun e _ => intL n e),
          integral_finset_sum Finset.univ (fun e _ => intR n e)]
  change Tendsto (fun n => ∫ x, ψ x * auxiliaryPerturbationJet G₀ G₀ (G n) x d i j) atTop (𝓝 0)
  simp_rw [expand]
  simpa only [sub_zero] using (limJ.sub limsumL).sub limsumR

end Burnett.FlatRigidity

namespace Burnett.FlatRigidity

open MeasureTheory Filter Set Burnett.RicciSymbol Burnett.Geometry
open Burnett.Analysis.LocalWeakDerivative Burnett.Analysis.LocalWeakRicci
open Burnett.Analysis.LocalWeakRicciIdentification
open ConnectionDifference BackgroundConnection AuxiliaryConnection InverseField
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology ENNReal BigOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Under the original physical conditions, the computed Christoffel coefficients
    converge against every compactly supported smooth coordinate test. -/
theorem computedConnection_smooth_test_tendsto_of_original
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (p : M) (a b c : Index) {ψ : CoordinateSpace → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ (chartAt CoordinateSpace p).target) :
    Tendsto (fun n => ∫ x, ψ x * computedConnection (coordinateBilinear (g n) p) x a b c)
      atTop (𝓝 (∫ x, ψ x * computedConnection (coordinateBilinear g₀ p) x a b c)) := by
  let U := (chartAt CoordinateSpace p).target
  have hU : IsOpen U := (chartAt CoordinateSpace p).open_target
  let G₀ := coordinateBilinear g₀ p
  let G (n : ℕ) := coordinateBilinear (g n) p
  let J (n : ℕ) := auxiliaryPerturbationJet G₀ G₀ (G n)
  let E (n : ℕ) := ConnectionErrorLInfinity.computedError G₀ (G n)
  let A (e : Index) (x : CoordinateSpace) := matrixInverse (metricComponents G₀ x) a e / 2
  let F (n : ℕ) (e i j k : Index) (x : CoordinateSpace) := (ψ x * A e x) * J n x i j k
  have hG₀ := ManifoldBilinear.contDiffOn_metricComponents g₀ h₀ p
  have hAi (e : Index) : ContDiffOn ℝ ∞ (A e) U := by
    apply (SmoothMetricConnection.contDiffOn_matrixInverse (metricComponents G₀) U hG₀
      (fun y hy => ManifoldVolumeRegularity.coordinate_det_ne_zero g₀ hn₀ p hy) a e).div_const
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g₀ h₀ hn₀ p
  have hΓc (e i j : Index) : ContDiffOn ℝ ∞ (fun x => computedConnection G₀ x e i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ e) i) j
  have hJ (n : ℕ) (i j k : Index) : ContDiffOn ℝ ∞ (fun x => J n x i j k) U := by
    let H := fun x => metricComponents (G n) x - metricComponents G₀ x
    have hH (a b : Index) : ContDiffOn ℝ ∞ (fun x => H x a b) U :=
      component_difference_smoothOn g g₀ h₀ hg p a b n
    exact ((SmoothMetricConnection.contDiffOn_coordinateJet H U hU hH i j k).sub
      (ContDiffOn.sum fun e _ => (hΓc e i j).mul (hH e k))).sub
      (ContDiffOn.sum fun e _ => (hΓc e i k).mul (hH j e))
  have hF (n : ℕ) (e i j k : Index) : Integrable (F n e i j k) :=
    (contDiff_test_mul_local hU (contDiff_test_mul_local hU hψ hψU (hAi e))
      (tsupport_mul_subset_left.trans hψU) (hJ n i j k)).continuous.integrable_of_hasCompactSupport
      hcψ.mul_right.mul_right
  have hF0 (e i j k : Index) : Tendsto (fun n => ∫ x, F n e i j k x) atTop (𝓝 0) :=
    auxiliaryPerturbationJet_test_of_original r g₀ g h₀ hg hn₀ hconv p i j k
      (contDiff_test_mul_local hU hψ hψU (hAi e)) hcψ.mul_right (tsupport_mul_subset_left.trans hψU)
  let L (n : ℕ) (e : Index) (x : CoordinateSpace) := F n e b c e x + F n e c b e x - F n e e b c x
  have hL (n : ℕ) (e : Index) : Integrable (L n e) := ((hF n e b c e).add (hF n e c b e)).sub (hF n e e b c)
  have hLim (e : Index) : Tendsto (fun n => ∫ x, L n e x) atTop (𝓝 0) := by
    have hsplit (n : ℕ) : (∫ x, L n e x) =
        (∫ x, F n e b c e x) + (∫ x, F n e c b e x) - ∫ x, F n e e b c x := by
      calc
        _ = (∫ x, F n e b c e x + F n e c b e x) - ∫ x, F n e e b c x :=
          integral_sub ((hF n e b c e).add (hF n e c b e)) (hF n e e b c)
        _ = _ := by
          have ha : (∫ x, F n e b c e x + F n e c b e x) =
              (∫ x, F n e b c e x) + ∫ x, F n e c b e x := integral_add (hF n e b c e) (hF n e c b e)
          rw [ha]
    simp_rw [hsplit]
    simpa only [add_zero, sub_zero] using ((hF0 e b c e).add (hF0 e c b e)).sub (hF0 e e b c)
  have hLimSum : Tendsto (fun n => ∑ e, ∫ x, L n e x) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun e _ => hLim e)
  have hIntΓ : Integrable (fun x => ψ x * computedConnection G₀ x a b c) :=
    (contDiff_test_mul_local hU hψ hψU (hΓc a b c)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  have hIntE (n : ℕ) : Integrable (fun x => ψ x * E n x a b c) :=
    (contDiff_test_mul_local hU hψ hψU (computedError_component_smoothOn g₀ (g n) h₀ (hg n) hn₀ (hn n) p a b c)).continuous.integrable_of_hasCompactSupport
      hcψ.mul_right
  have hLimE : Tendsto (fun n => ∫ x, ψ x * E n x a b c) atTop (𝓝 0) := by
    simpa only [mul_one] using error_value_test_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb p a b c
      hψ hcψ hψU (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : CoordinateSpace => (1 : ℝ)) U)
  have decomp (n : ℕ) : (∫ x, ψ x * computedConnection (G n) x a b c) =
      (∫ x, ψ x * computedConnection G₀ x a b c) + (∑ e, ∫ x, L n e x) + ∫ x, ψ x * E n x a b c := by
    have hpoint : (fun x => ψ x * computedConnection (G n) x a b c) =
        fun x => (ψ x * computedConnection G₀ x a b c + ∑ e, L n e x) + ψ x * E n x a b c := by
      funext x
      have hsplit := congrArg (fun A : Connection => A a b c) (connection_difference_eq_linear_plus_error G₀ (G n) x)
      change computedConnection (G n) x a b c - computedConnection G₀ x a b c =
        christoffel (matrixInverse (metricComponents G₀ x)) (J n x) a b c + E n x a b c at hsplit
      rw [sub_eq_iff_eq_add.mp hsplit, mul_add, mul_add]
      have hsum : ψ x * christoffel (matrixInverse (metricComponents G₀ x)) (J n x) a b c = ∑ e, L n e x := by
        simp only [christoffel, koszul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        unfold L F A
        ring
      rw [hsum]
      ring
    rw [hpoint]
    have hsum := integrable_finset_sum Finset.univ (fun e _ => hL n e)
    calc
      _ = (∫ x, ψ x * computedConnection G₀ x a b c + ∑ e, L n e x) + ∫ x, ψ x * E n x a b c :=
        integral_add (hIntΓ.add hsum) (hIntE n)
      _ = _ := by
        have ha : (∫ x, ψ x * computedConnection G₀ x a b c + ∑ e, L n e x) =
            (∫ x, ψ x * computedConnection G₀ x a b c) + ∫ x, ∑ e, L n e x := integral_add hIntΓ hsum
        rw [ha, integral_finset_sum Finset.univ (fun e _ => hL n e)]
  change Tendsto (fun n => ∫ x, ψ x * computedConnection (G n) x a b c)
    atTop (𝓝 (∫ x, ψ x * computedConnection G₀ x a b c))
  simp_rw [decomp]
  simpa only [add_zero] using ((tendsto_const_nhds.add hLimSum).add hLimE)

end Burnett.FlatRigidity

namespace Burnett.FlatRigidity

open MeasureTheory Filter Set Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.FlatRigidity
open ConnectionDifference BackgroundConnection
open ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence
open scoped ContDiff Manifold Topology ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- All fixed local L¹ tests of the original metric sequence's actual Christoffel fields. -/
theorem computedConnection_localWeakStarOn_of_original
    (r : Metric (M := M)) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n))
    (hs₀ : IsSymmetric g₀) (hs : ∀ n, IsSymmetric (g n))
    (hn₀ : IsNondegenerate g₀) (hn : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g g₀)
    (hb : ∀ S : Set M, IsCompact S → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      eLpNorm (IntrinsicDhMeasure.normScalar r (fun m => g n m - g₀ m)) ⊤
        ((ManifoldVolume.geometricMeasure g₀).restrict S) ≤ ENNReal.ofReal D)
    (p : M) (a b c : Index) :
    LocalWeakStarOn (chartAt CoordinateSpace p).target
      (fun n x => computedConnection (coordinateBilinear (g n) p) x a b c)
      (fun x => computedConnection (coordinateBilinear g₀ p) x a b c) := by
  have hU := (chartAt CoordinateSpace p).open_target
  have hgSmooth (n : ℕ) :=
    SmoothMetricConnection.contDiffOn_coordinateBilinear_connection (g n) (hg n) (hn n) p
  have h₀Smooth := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g₀ h₀ hn₀ p
  have hgCont (n : ℕ) := (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp (hgSmooth n) a) b) c).continuousOn
  have h₀Cont := (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp h₀Smooth a) b) c).continuousOn
  apply LocalWeakStarOn.of_compact_smooth_tests hU hgCont h₀Cont
  · intro K hK hKU
    obtain ⟨C, hC, hbC⟩ := computedConnection_uniform_bound_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb p K hK hKU
    refine ⟨C, hC, ?_⟩
    intro n y hy
    rw [Real.norm_eq_abs]
    exact (ConnectionError.abs_firstJet_entry_le_norm (computedConnection (coordinateBilinear (g n) p) y) a b c).trans
      (hbC n y hy)
  · intro ψ hψ hcψ hψU
    exact computedConnection_smooth_test_tendsto_of_original r g₀ g h₀ hg hs₀ hs hn₀ hn hconv hb p a b c hψ hcψ hψU

end Burnett.FlatRigidity
