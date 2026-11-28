import Burnett.Analysis.TransportWard.Weyl.LebesgueGradientInput
import Burnett.Analysis.GaugeProjection.ProjectedDefectLocalizationError
import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2300

noncomputable section

namespace Burnett.V03

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference
open ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart Burnett.Fourier
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold Topology

local notation "E₀" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M]

/-- Multiplying the original receiving perturbation by the outer
Weyl plateau gives the compactly supported Schwartz input. -/
def fixedWeylPerturbationSchwartz (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (n : ℕ) (k : Pair) :
    SchwartzMap E₀ ℂ := by
  let f (x : E₀) := (χ : E₀ → ℝ) x * fixedComponent B g c n k x
  have hS : ContDiff ℝ ∞ f := Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local c.chart.open_target
    (test_smooth χ) hχ (fixedComponent_smooth B g hB hg c n k)
  have hC : HasCompactSupport f := (test_compactSupport χ).mul_right
  exact (hC.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hS)

private theorem fixedWeylPerturbationSchwartz_partial_apply (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (n : ℕ) (i : JetSlot) (x : E₀) :
    let F := fixedWeylPerturbationSchwartz B g hB hg c χ hχ n i.2
    let w := fderiv ℝ (χ : E₀ → ℝ) x (coordinateDirection i.1)
    SchwartzMap.pderivCLM ℂ (coordinateDirection i.1) F x =
      fixedGradientSchwartz B g hB hg c χ hχ n i x + ((w * fixedComponent B g c n i.2 x : ℝ) : ℂ) := by
  intro F w
  let e := coordinateDirection i.1
  let f := fixedComponent B g c n i.2
  let G (y : E₀) := (χ : E₀ → ℝ) y * f y
  rw [SchwartzMap.pderivCLM_apply, fixedGradientSchwartz_apply]
  change fderiv ℝ (fun y => (G y : ℂ)) x e = _
  by_cases hx : x ∈ tsupport (χ : E₀ → ℝ)
  · have hd : DifferentiableAt ℝ f x :=
      ((fixedComponent_smooth B g hB hg c n i.2).contDiffAt
        (c.chart.open_target.mem_nhds (hχ hx))).differentiableAt (by simp)
    have hχd := (test_smooth χ).differentiable (by simp) x
    have hG : DifferentiableAt ℝ G x := hχd.mul hd
    have hD := (Complex.ofRealCLM.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
    change fderiv ℝ (fun y => (G y : ℂ)) x = _ at hD
    rw [hD, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hJ : fderiv ℝ f x e = coordinateJet (fixedPerturbation B (g n) c) x i.1 i.2.1 i.2.2 := rfl
    change ((fderiv ℝ (fun y => (χ : E₀ → ℝ) y * f y) x e : ℝ) : ℂ) = _
    rw [fderiv_fun_mul hχd hd,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply,hJ]
    simp only [f,w,e,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  · have hWin := (isClosed_tsupport (χ : E₀ → ℝ)).isOpen_compl.mem_nhds hx
    have hZ : (fun y => (χ : E₀ → ℝ) y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hWin] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hF : (fun y => (G y : ℂ)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hZ] with y hy
      simp only [G,hy,zero_mul,Complex.ofReal_zero]
    have hw : w = 0 := by
      simp only [w,hZ.fderiv_eq,fderiv_const_apply,ContinuousLinearMap.zero_apply]
    rw [hF.fderiv_eq,fderiv_const_apply,ContinuousLinearMap.zero_apply,hw]
    simp only [image_eq_zero_of_notMem_tsupport hx,zero_mul,Complex.ofReal_zero,zero_add]

/-- Differentiating the actual compact input and taking the actual raw
cutoff gradient differ by a strongly vanishing L² localization error. -/
theorem tendsto_fixedWeylPerturbationSchwartz_partial_sub_rawGradient
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hconv : LocallyUniformlyConverges r g B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (i : JetSlot) :
    let F := fun n => fixedWeylPerturbationSchwartz B g hB hg c χ hχ n i.2
    let U := fun n => fixedGradientSchwartz B g hB hg c χ hχ n i
    Tendsto (fun n => (SchwartzMap.pderivCLM ℂ (coordinateDirection i.1) (F n)).toLp 2 volume -
        (U n).toLp 2 volume) atTop (𝓝 0) := by
  intro F U
  let w (x : E₀) := fderiv ℝ (χ : E₀ → ℝ) x (coordinateDirection i.1)
  let K := tsupport (χ : E₀ → ℝ)
  have hK : IsCompact K := test_compactSupport χ
  have hwCont : Continuous w :=
    ((test_smooth χ).fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
  have hW (x : E₀) (hx : x ∉ K) : w x = 0 := by
    by_contra hn
    apply hx
    apply support_fderiv_subset ℝ
    intro hz
    exact hn (by simp only [w,hz,ContinuousLinearMap.zero_apply])
  have hwS : HasCompactSupport w := hK.of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx => by by_contra h; exact hx (hW x h)) hK.isClosed)
  have hFsmall := fixedComponent_localUniform r B g hconv c i.2 K hK hχ
  refine Burnett.P01.tendsto_weighted_localizationError_L2_zero K w
    (hwCont.memLp_of_hasCompactSupport hwS) hW (fun n => fixedComponent B g c n i.2) hFsmall _ ?_
  intro n
  let D := SchwartzMap.pderivCLM ℂ (coordinateDirection i.1) (F n)
  filter_upwards [Lp.coeFn_sub (D.toLp 2 volume) ((U n).toLp 2 volume),
    D.coeFn_toLp 2 volume, (U n).coeFn_toLp 2 volume] with x hx hD hU
  rw [hx, Pi.sub_apply, hD, hU]
  rw [fixedWeylPerturbationSchwartz_partial_apply B g hB hg c χ hχ n i x]
  exact add_sub_cancel_left _ _

end Burnett.V03
