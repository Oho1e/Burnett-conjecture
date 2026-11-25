import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicKernelRotation
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A06

open Filter Set Metric MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))

/-- The degree-zero radial projection, with a fixed value at the origin. -/
def roundSphereRadialNormalize (x : RotationSpace) : RotationSpace :=
  ‖x‖⁻¹ • x

theorem roundSphereRadialNormalize_norm {x : RotationSpace} (hx : x ≠ 0) :
    ‖roundSphereRadialNormalize x‖ = 1 :=
  norm_smul_inv_norm (𝕜 := ℝ) hx

theorem roundSphereRadialNormalize_contDiffAt {n : WithTop ℕ∞} {x : RotationSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ n roundSphereRadialNormalize x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem roundSphereRadialNormalize_self (x : RoundSphere3) :
    roundSphereRadialNormalize (x : RotationSpace) = x := by
  simp [roundSphereRadialNormalize,mem_sphere_zero_iff_norm.mp x.property]

private theorem roundSphereRadialNormalize_fderiv_tangent {x : RotationSpace} (hx : x ≠ 0)
    (v : RotationSpace) :
    inner ℝ (roundSphereRadialNormalize x) (fderiv ℝ roundSphereRadialNormalize x v) = 0 := by
  have hf : DifferentiableAt ℝ roundSphereRadialNormalize x :=
    (roundSphereRadialNormalize_contDiffAt (n := 1) hx).differentiableAt le_rfl
  have eq : (fun y : RotationSpace => ‖roundSphereRadialNormalize y‖^2) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [show {y : RotationSpace | y ≠ 0} ∈ 𝓝 x from isOpen_ne.mem_nhds hx] with y hy
    rw [roundSphereRadialNormalize_norm hy, one_pow]
  have hzero := ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).congr_of_eventuallyEq eq).fderiv
  have h := hf.hasFDerivAt.norm_sq.fderiv
  rw [hzero] at h
  have eval := congrArg (fun L : RotationSpace →L[ℝ] ℝ => L v) h
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply, two_nsmul] at eval
  linarith only [eval]

private theorem linear_tangent_zero (u v : RotationSpace) (hu : u ≠ 0)
    (L : RotationSpace →L[ℝ] ℝ) (hL : ∀ i j : Fin 4, L (planeRotationGenerator i j u) = 0)
    (horth : inner ℝ u v = 0) : L v = 0 := by
  let e (i : Fin 4) : RotationSpace := EuclideanSpace.single i 1
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, u i ≠ 0 := by
    by_contra! all
    exact hu (PiLp.ext all)
  have eq (j : Fin 4) : u i * L (e j) = u j * L (e i) := by
    apply sub_eq_zero.mp
    simpa only [planeRotationGenerator_eq, map_sub, map_smul, smul_eq_mul, e] using hL i j
  have ve : (∑ j : Fin 4, v j • e j) = v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  have lv : L v = ∑ j : Fin 4, v j * L (e j) := by
    simpa only [map_sum,map_smul,smul_eq_mul] using (congrArg L ve).symm
  have hsum : (∑ j : Fin 4, u j * v j) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using horth
  have hz : u i * L v = 0 := by
    calc
      _ = ∑ j : Fin 4, v j * (u i * L (e j)) := by
        rw [lv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j : Fin 4, (u j * v j) * L (e i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [eq]
        ring
      _ = _ := by rw [← Finset.sum_mul, hsum, zero_mul]
  exact (mul_eq_zero.mp hz).resolve_left hi

private theorem roundSphereKernel_normalized_fderiv_zero (d : ℕ) {x : RotationSpace} (hx : x ≠ 0) :
    fderiv ℝ (sphereHarmonicKernelDiagonal d ∘ roundSphereRadialNormalize) x = 0 := by
  let u := roundSphereRadialNormalize x
  have hu : u ≠ 0 := by
    intro h
    have ht : ‖u‖ = 1 := roundSphereRadialNormalize_norm hx
    rw [h,norm_zero] at ht
    exact zero_ne_one ht
  have hf := (contDiff_infty.mp (sphereHarmonicKernelDiagonal_contDiff d) 1).differentiable_one
  have hg := (roundSphereRadialNormalize_contDiffAt (n := 1) hx).differentiableAt le_rfl
  rw [fderiv_comp x (hf u) hg]
  ext v
  let L := fderiv ℝ (sphereHarmonicKernelDiagonal d) u
  apply linear_tangent_zero u (fderiv ℝ roundSphereRadialNormalize x v) hu L
  · exact fun i j => planeRotationDerivative_sphereHarmonicKernelDiagonal d i j u
  · exact roundSphereRadialNormalize_fderiv_tangent hx v

private theorem roundSphereKernelDiagonal_constant (d : ℕ) (x y : RoundSphere3) :
    sphereHarmonicKernelDiagonal d x = sphereHarmonicKernelDiagonal d y := by
  let U : Set RotationSpace := {(0 : RotationSpace)}ᶜ
  let F := sphereHarmonicKernelDiagonal d ∘ roundSphereRadialNormalize
  have hopen : IsOpen U := isOpen_compl_singleton
  have hdim : 1 < Module.rank ℝ RotationSpace := by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    decide
  have hpre : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank hdim (0 : RotationSpace)).isPreconnected
  have hF : DifferentiableOn ℝ F U := by
    intro z hz
    have hρ := (roundSphereRadialNormalize_contDiffAt (n := 1) hz).differentiableAt le_rfl
    exact (((contDiff_infty.mp (sphereHarmonicKernelDiagonal_contDiff d) 1).differentiable_one
      (roundSphereRadialNormalize z)).comp z hρ).differentiableWithinAt
  have hy : (y : RotationSpace) ∈ U :=
    ne_of_mem_sphere y.property (by norm_num)
  have hx : (x : RotationSpace) ∈ U :=
    ne_of_mem_sphere x.property (by norm_num)
  have heq := hopen.eqOn_of_fderiv_eq (𝕜 := ℝ) hpre hF
    (differentiableOn_const (c := F y))
    (fun z hz => by rw [fderiv_fun_const, Pi.zero_apply]; exact roundSphereKernel_normalized_fderiv_zero d hz)
    hy rfl
  simpa only [F, Function.comp_apply, roundSphereRadialNormalize_self] using heq hx

private theorem roundSphere3Measure_real_univ_pos : 0 < roundSphere3Measure.real univ := by
  let x : RoundSphere3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have h : roundSphere3Measure univ ≠ 0 := isOpen_univ.measure_ne_zero _ ⟨x,mem_univ x⟩
  exact ENNReal.toReal_pos h (measure_ne_top roundSphere3Measure univ)

/-- The diagonal equals the multiplicity divided by the actual sphere area:
integrate the invariant sum of squared normalized harmonics. -/
theorem sphereHarmonicKernelDiagonal_on_sphere (d : ℕ) (x : RoundSphere3) :
    sphereHarmonicKernelDiagonal d x = (((d + 1)^2 : ℕ) : ℝ) / roundSphere3Measure.real univ := by
  have hs : (fun y : RoundSphere3 => sphereHarmonicKernelDiagonal d y) =
      fun _ : RoundSphere3 => sphereHarmonicKernelDiagonal d x :=
    funext fun y => roundSphereKernelDiagonal_constant d y x
  have hY (k : Fin ((d + 1)^2)) :
      Integrable (fun y : RoundSphere3 => sphereHarmonicBasisFunction d k y ^ 2) roundSphere3Measure :=
    ((sphereHarmonicBasisFunction d k).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : (∫ y : RoundSphere3, sphereHarmonicKernelDiagonal d y ∂roundSphere3Measure) =
      (((d + 1)^2 : ℕ) : ℝ) := by
    change (∫ y : RoundSphere3, ∑ k : Fin ((d + 1)^2), sphereHarmonicBasisFunction d k y ^ 2
      ∂roundSphere3Measure) = _
    rw [integral_finset_sum _ (fun k _ => hY k)]
    simp only [pow_two, sphereHarmonicBasisFunction_integral_mul, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hs, integral_const, smul_eq_mul] at hi
  apply (eq_div_iff roundSphere3Measure_real_univ_pos.ne').2
  exact (mul_comm _ _).trans hi

/-- The evaluation functional on the actual degree-d harmonic L² space
has pointwise bound √(multiplicity / actual sphere area). -/
theorem norm_sphereHarmonicValue_le (d : ℕ) (H : sphereHarmonicSubmodule d) (x : RoundSphere3) :
    ‖spherePolynomialValue H.val.val x‖ ≤
      Real.sqrt ((((d + 1)^2 : ℕ) : ℝ) / roundSphere3Measure.real univ) * ‖sphereHarmonicToLp d H‖ := by
  let K := sphereHarmonicToLp d (sphereHarmonicReproducingPolynomial d x)
  have hK : ‖K‖ = Real.sqrt ((((d + 1)^2 : ℕ) : ℝ) / roundSphere3Measure.real univ) := by
    have h := sphereHarmonicKernelDiagonal_eq_L2_sq d x
    change sphereHarmonicKernelDiagonal d x = ‖K‖^2 at h
    rw [← sphereHarmonicKernelDiagonal_on_sphere d x, h, Real.sqrt_sq (norm_nonneg _)]
  rw [sphereHarmonicValue_eq_reproducing_inner]
  exact (norm_inner_le_norm (𝕜 := ℝ) K (sphereHarmonicToLp d H)).trans_eq (by rw [hK])

end Burnett.A06
