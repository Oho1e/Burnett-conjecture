import Burnett.Geometry.MaximalChart.MetricJet
import Burnett.Geometry.MaximalChart.UniformMetric
import Burnett.Analysis.Microlocal.Overlap.TransportedGradientL2

/-! The actual ordered coordinate jet and its Hessian error in compatible smooth charts. -/

set_option autoImplicit false
set_option maxRecDepth 3100
set_option maxHeartbeats 2300000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Fourier
open Burnett.Geometry ConnectionDifference ConnectionCoordinateChange ManifoldMetric ManifoldMetricSequence
open ManifoldBilinear ChartVolume ManifoldMetricTransition MetricJetNaturality TensorCoordinateChange MaximalChart
open Burnett.F05.CoordinateCurl Burnett.F05.ChartVolumeBridge Burnett.F05.OverlapCovariantGradient
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet
open scoped Manifold ContDiff Topology BigOperators InnerProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem pullback3_eq_directional_matrix (A : Matrix Index Index ℝ)
    (J : FirstJet) (b i j : Index) :
    pullback3 A J b i j =
      (A.transpose * (∑ p, A p b • (J p : Matrix Index Index ℝ) : Matrix Index Index ℝ) * A) i j := by
  rw [pullback3_apply, matrix_triple_entry]
  simp only [Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  symm
  calc
    _ = ∑ a : Index, ∑ p : Index, ∑ e : Index, A a i * (A p b * J p a e) * A e j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Pi.smul_apply, smul_eq_mul]
    _ = ∑ p : Index, ∑ a : Index, ∑ e : Index, A a i * (A p b * J p a e) * A e j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro e _
      ring

theorem transformedJet_eq_pullback3_add_metric_remainder
    (A G : Matrix Index Index ℝ) (J : FirstJet) (H : Connection) :
    transformedJet A G J H = pullback3 A J + transformedJet A G 0 H := by
  funext b i j
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, pullback3_eq_directional_matrix]
  simp only [transformedJet, transformedMetricDerivative, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.add_apply]
  ring

def fixedPerturbation (g0 g1 : Field (M := M)) (c : AtlasChart M) (x : CoordinateSpace) : Tensor2 :=
  metricComponents (fixedForm g1 c) x - metricComponents (fixedForm g0 c) x

variable [SecondCountableTopology M]

private theorem transformedJet_sub (A G₁ G₀ : Matrix Index Index ℝ)
    (J₁ J₀ : FirstJet) (H : Connection) :
    transformedJet A G₁ J₁ H - transformedJet A G₀ J₀ H =
      transformedJet A (G₁ - G₀) (J₁ - J₀) H := by
  funext b
  change transformedMetricDerivative A G₁ (∑ p, A p b • (J₁ p : Matrix Index Index ℝ))
    (connectionMatrix H b) -
    transformedMetricDerivative A G₀ (∑ p, A p b • (J₀ p : Matrix Index Index ℝ)) (connectionMatrix H b) = _
  simp only [transformedJet, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib,
    transformedMetricDerivative, Matrix.mul_sub, Matrix.sub_mul]
  abel

private theorem fixed_components_differentiable (B : Field (M := M)) (hB : IsSmooth B)
    (c : AtlasChart M) (x : CoordinateSpace) (hx : x ∈ c.chart.target) :
    DifferentiableComponentsAt (metricComponents (fixedForm B c)) x := by
  intro a b
  exact ((fixedForm_components_smooth B hB c a b).contDiffAt
    (c.chart.open_target.mem_nhds hx)).differentiableAt (by simp)

/-- The two actual raw perturbation gradients on the overlap differ from
tensorial pullback by the exact two Hessian terms, linear in the perturbation
itself. The transition is between compatible smooth atlas charts. -/
theorem fixedPerturbation_jet_change (g0 g1 : Field (M := M))
    (h0 : IsSmooth g0) (h1 : IsSmooth g1) (c d : AtlasChart M)
    (x : CoordinateSpace) (hx : x ∈ (c.transition d).source) :
    let e := c.transition d
    let A := derivativeMatrix (fderiv ℝ e x)
    let H := fixedPerturbation g0 g1 d (e x)
    coordinateJet (fixedPerturbation g0 g1 c) x =
      pullback3 A (coordinateJet (fixedPerturbation g0 g1 d) (e x)) +
        transformedJet A H 0 (fixedHessian c d x) := by
  dsimp only
  let e := c.transition d
  have hy : e x ∈ d.chart.target := (e.mapsTo hx).1
  have hc : x ∈ c.chart.target := hx.1
  unfold fixedPerturbation
  rw [coordinateJet_sub _ _ x (fixed_components_differentiable g1 h1 c x hc) (fixed_components_differentiable g0 h0 c x hc),
    coordinateJet_sub _ _ (e x) (fixed_components_differentiable g1 h1 d (e x) hy)
      (fixed_components_differentiable g0 h0 d (e x) hy),
    fixedForm_jet_change g1 h1 c d x hx, fixedForm_jet_change g0 h0 c d x hx,
    transformedJet_sub, transformedJet_eq_pullback3_add_metric_remainder]


def overlapRemainder (c d : AtlasChart M) (x : CoordinateSpace) (G : Matrix Index Index ℝ) : FirstJet :=
  transformedJet (derivativeMatrix (fderiv ℝ (c.transition d) x)) G 0 (fixedHessian c d x)


omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
theorem overlapRemainder_zero (c d : AtlasChart M) (x : CoordinateSpace) :
    overlapRemainder c d x 0 = 0 := by
  funext b i j
  simp [overlapRemainder, transformedJet, transformedMetricDerivative]

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
private theorem fixedJacobian_continuousOn (c d : AtlasChart M) :
    ContinuousOn (fun x => derivativeMatrix (fderiv ℝ (c.transition d) x))
      (c.transition d).source := by
  have hF : ContDiffOn ℝ ∞ (fderiv ℝ (c.transition d)) (c.transition d).source :=
    (c.smooth_transition d).fderiv_of_isOpen (c.transition d).open_source (by simp)
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  simp only [derivativeMatrix_apply]
  exact (PiLp.continuous_apply 2 (fun _ : Index => ℝ) a).comp_continuousOn
    (hF.continuousOn.clm_apply continuousOn_const)

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
private theorem actualHessian_continuousOn (c d : AtlasChart M) (b : Index) :
    ContinuousOn (fun x => connectionMatrix (fixedHessian c d x) b)
      (c.transition d).source := by
  have hF : ContDiffOn ℝ ∞ (fderiv ℝ (c.transition d)) (c.transition d).source :=
    (c.smooth_transition d).fderiv_of_isOpen (c.transition d).open_source (by simp)
  have hFF : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (c.transition d))) (c.transition d).source :=
    hF.fderiv_of_isOpen (c.transition d).open_source (by simp)
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro e
  exact (PiLp.continuous_apply 2 (fun _ : Index => ℝ) a).comp_continuousOn
    ((hFF.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const)

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
theorem overlapRemainder_continuousOn (c d : AtlasChart M) :
    ContinuousOn
      (fun z : CoordinateSpace × Tensor2 => overlapRemainder c d z.1 z.2)
      ((c.transition d).source ×ˢ (univ : Set Tensor2)) := by
  let U := (c.transition d).source ×ˢ (univ : Set Tensor2)
  let A (z : CoordinateSpace × Tensor2) :=
    derivativeMatrix (fderiv ℝ (c.transition d) z.1)
  let H (b : Index) (z : CoordinateSpace × Tensor2) :=
    connectionMatrix (fixedHessian c d z.1) b
  have hA : ContinuousOn A U := (fixedJacobian_continuousOn c d).comp
    continuous_fst.continuousOn (fun _ hz => hz.1)
  have hH (b : Index) : ContinuousOn (H b) U := (actualHessian_continuousOn c d b).comp
    continuous_fst.continuousOn (fun _ hz => hz.1)
  have hG : ContinuousOn (fun z : CoordinateSpace × Tensor2 => (z.2 : Matrix Index Index ℝ)) U :=
    continuous_snd.continuousOn
  have hT : Continuous (Matrix.transpose : Matrix Index Index ℝ → Matrix Index Index ℝ) :=
    continuous_id.matrix_transpose
  apply continuousOn_pi.mpr
  intro b
  have hr := (((hT.comp_continuousOn (hH b)).mul hG).mul hA).add
    (((hT.comp_continuousOn hA).mul hG).mul (hH b))
  simpa only [overlapRemainder, transformedJet, transformedMetricDerivative, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, A, H] using hr

private theorem mem_matrixIcc_of_norm_le_one (G : Tensor2) (hG : ‖G‖ ≤ 1) :
    G ∈ (Icc (-1 : ℝ) 1).matrix := by
  intro i j
  have hh : ‖G i j‖ ≤ 1 := (norm_le_pi_norm (G i) j).trans ((norm_le_pi_norm G i).trans hG)
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)


theorem bothCharts_remainder_uniform
    (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (hconv : LocallyUniformlyConverges r g g0) (c d : AtlasChart M) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source) :
    TendstoUniformlyOn
      (fun n x => overlapRemainder c d x (fixedPerturbation g0 (g n) d (c.transition d x)))
      (fun _ => 0) atTop K := by
  let e := c.transition d
  let C : Set Tensor2 := (Icc (-1 : ℝ) 1).matrix
  have hC : IsCompact C := isCompact_Icc.matrix
  have hC0 : (0 : Tensor2) ∈ C :=
    mem_matrixIcc_of_norm_le_one _ (by simp)
  have hI : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hIU : e '' K ⊆ d.chart.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.mapsTo (hKU hx)).1
  have hu := fixed_components_uniform_of_physical_C0loc r g g0 hconv d (e '' K) hI hIU
  let R (z : CoordinateSpace × Tensor2) := overlapRemainder c d z.1 z.2
  have hR : ContinuousOn R (K ×ˢ C) := (overlapRemainder_continuousOn c d).mono
    (fun _ hz => ⟨hKU hz.1, mem_univ _⟩)
  have hU := (hK.prod hC).uniformContinuousOn_of_continuous hR
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hlim⟩ := Metric.uniformContinuousOn_iff.mp hU ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (min δ 1) (lt_min hδ zero_lt_one)] with n hn
  intro x hx
  let F := fixedPerturbation g0 (g n) d (e x)
  have hsmall : ‖F‖ < min δ 1 := by
    have hh := hn (e x) (mem_image_of_mem e hx)
    rw [dist_comm, dist_eq_norm] at hh
    exact hh
  have hF : F ∈ C := mem_matrixIcc_of_norm_le_one _
    ((hsmall.trans_le (min_le_right δ 1)).le)
  have hdist : dist (x, (0 : Tensor2)) (x, F) < δ := by
    rw [Prod.dist_eq, dist_self, dist_zero_left, max_eq_right (norm_nonneg _)]
    exact hsmall.trans_le (min_le_left δ 1)
  have hh := hlim (x, 0) ⟨hx, hC0⟩ (x, F) ⟨hx, hF⟩ hdist
  simpa only [R, overlapRemainder_zero] using hh

theorem bothCharts_rawJet_error_uniform
    (r : Metric (M := M)) (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hconv : LocallyUniformlyConverges r g g0) (c d : AtlasChart M) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source) :
    TendstoUniformlyOn
      (fun n x => coordinateJet (fixedPerturbation g0 (g n) c) x -
        pullback3 (derivativeMatrix (fderiv ℝ (c.transition d) x))
          (coordinateJet (fixedPerturbation g0 (g n) d) (c.transition d x)))
      (fun _ => 0) atTop K := by
  apply (bothCharts_remainder_uniform r g0 g hconv c d hK hKU).congr
  exact Eventually.of_forall (fun n x hx => by
    dsimp only
    rw [fixedPerturbation_jet_change g0 (g n) h0 (hg n) c d x (hKU hx)]
    simp only [add_sub_cancel_left, overlapRemainder])

end Burnett.Microlocal.AtlasVolumeGradient
