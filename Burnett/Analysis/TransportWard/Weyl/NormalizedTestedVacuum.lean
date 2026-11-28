import Burnett.Analysis.TransportWard.Weyl.EulerAffineRegularity
import Burnett.Analysis.TransportWard.Weyl.PointwiseVacuum
import Burnett.Analysis.TransportWard.Weyl.LinearizedEulerSymmetry
import Burnett.Analysis.TransportWard.Weyl.SymmetricFieldNormalization
import Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput
import Burnett.Analysis.TransportWard.Weyl.EulerRemainderPairing

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V03.Palatini

open Set MeasureTheory Function Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear MaximalChart
open Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.SymmetricEnergy (Op)
open Burnett.Microlocal.AtlasVolumeGradient (fixedComponent fixedPerturbation)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold Matrix.Norms.Elementwise InnerProductSpace ComplexConjugate

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

def normalizedChartMetric (B : Field (M := M)) (c : M) : E₀ → I → ℝ :=
  normalizeMetricComponents ∘ symmetricChartMetricComponents B c

def normalizedChartPerturbation (B G : Field (M := M)) (c : M) (x : E₀) : I → ℝ :=
  normalizedChartMetric G c x - normalizedChartMetric B c x

theorem contDiffOn_normalizedChartMetric (B : Field (M := M)) (hB : IsSmooth B) (c : M) :
    ContDiffOn ℝ ∞ (normalizedChartMetric B c) (chartAt E₀ c).target := by
  apply contDiffOn_pi.mpr
  intro i
  change ContDiffOn ℝ ∞ (fun x => symmetricMetricScale i *
    metricComponents (coordinateBilinear B c) x i.val.1 i.val.2) (chartAt E₀ c).target
  exact contDiffOn_const.mul (ManifoldBilinear.contDiffOn_metricComponents B hB c i.val.1 i.val.2)

theorem normalizedChartPerturbation_eq_fixedComponent
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (c : M)
    (n : ℕ) (x : E₀) (hx : x ∈ (chartAt E₀ c).target) (i : I) :
    normalizedChartPerturbation B (g n) c x i =
      symmetricMetricScale i * fixedComponent B g (AtlasChart.atPoint c) n i.val x := by
  unfold normalizedChartPerturbation normalizedChartMetric fixedComponent fixedPerturbation
  rw [fixedForm_eq_preferred_components (g n) c hx, fixedForm_eq_preferred_components B c hx]
  change symmetricMetricScale i * metricComponents (coordinateBilinear (g n) c) x i.val.1 i.val.2 -
      symmetricMetricScale i * metricComponents (coordinateBilinear B c) x i.val.1 i.val.2 = _
  rw [Matrix.sub_apply, mul_sub]

/-- The component identification uses the actual outer-cutoff field, including
its zero extension outside the preferred chart. -/
theorem normalizedChartCutoffTest_eq_weylPerturbation
    [SecondCountableTopology M]
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : M) (ρ : D) (hρ : tsupport (ρ : E₀ → ℝ) ⊆ (chartAt E₀ c).target)
    (n : ℕ) (i : I)
    (hh : ContDiffOn ℝ ∞ (normalizedChartPerturbation B (g n) c) (chartAt E₀ c).target) :
    (chartMetricCutoffTest (chartAt E₀ c).open_target _ hh (ρ : E₀ → ℝ)
      (test_smooth ρ) hρ (test_compactSupport ρ)).val i =
        (symmetricMetricScale i : ℂ) •
          fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) ρ hρ n i.val := by
  ext x
  change ((ρ : E₀ → ℝ) x * normalizedChartPerturbation B (g n) c x i : ℝ) =
    (symmetricMetricScale i : ℂ) * ((ρ : E₀ → ℝ) x *
      fixedComponent B g (AtlasChart.atPoint c) n i.val x : ℝ)
  by_cases hx : x ∈ (chartAt E₀ c).target
  · rw [normalizedChartPerturbation_eq_fixedComponent B g c n x hx i]
    push_cast
    ring
  · rw [image_eq_zero_of_notMem_tsupport (fun hy => hx (hρ hy)), zero_mul,
      Complex.ofReal_zero, zero_mul, Complex.ofReal_zero, mul_zero]

variable [T2Space M]

/-- The exact vacuum expansion in the same orthonormal lower-metric fields
used by the genuine Weyl commutator. -/
theorem exists_normalizedChart_tested_vacuum
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hSigG : ∀ n, HasLorentzSignature (g n))
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (c : M) (ρ : D) (hρ : tsupport (ρ : E₀ → ℝ) ⊆ (chartAt E₀ c).target) :
    let S := orthonormalMetricDirection
    let b := normalizedChartMetric B c
    let h (n : ℕ) := normalizedChartPerturbation B (g n) c
    let f (n : ℕ) (t : ℝ) (x : E₀) (i : I) :=
      coordinateDensityEuler S (fun y => b y + t • h n y) x i
    ∃ (source : CompactSchwartzComponents I) (input linear quadratic rem : ℕ → CompactSchwartzComponents I),
      (∀ x i, source.val i x = ((ρ : E₀ → ℝ) x * f 0 0 x i : ℝ)) ∧
      (∀ n x i, (input n).val i x = ((ρ : E₀ → ℝ) x * h n x i : ℝ)) ∧
      (∀ n x i, (linear n).val i x = ((ρ : E₀ → ℝ) x * linearizedCoordinateDensityEuler S b (h n) x i : ℝ)) ∧
      (∀ n x i, (quadratic n).val i x = ((ρ : E₀ → ℝ) x * deriv (deriv (fun t => f n t x i)) 0 : ℝ)) ∧
      (∀ n x i, (rem n).val i x = ((ρ : E₀ → ℝ) x * quadraticPathRemainder (fun t => f n t x i) : ℝ)) ∧
      ∀ n, source + linear n + ((1 / 2 : ℝ) : ℂ) • quadratic n + rem n = 0 := by
  intro S b h f
  let U := (chartAt E₀ c).target
  have hU : IsOpen U := (chartAt E₀ c).open_target
  have hbs : ContDiffOn ℝ ∞ b U := contDiffOn_normalizedChartMetric B hB c
  have hgS (n : ℕ) : ContDiffOn ℝ ∞ (normalizedChartMetric (g n) c) U :=
    contDiffOn_normalizedChartMetric (g n) (hg n) c
  have hhs (n : ℕ) : ContDiffOn ℝ ∞ (h n) U := (hgS n).sub hbs
  have hdet (y : E₀) (hy : y ∈ U) : Matrix.det (assembleMetricComponents S (b y)) ≠ 0 := by
    change Matrix.det (assembledCoordinateMetric S b y) ≠ 0
    rw [show assembledCoordinateMetric S b = metricComponents (coordinateBilinear B c) from
      assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric c]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c hy
  let e (x : E₀) (i : I) := coordinateDensityEuler S b x i
  let l (n : ℕ) (x : E₀) (i : I) := linearizedCoordinateDensityEuler S b (h n) x i
  let q (n : ℕ) (x : E₀) (i : I) := deriv (deriv (fun t => f n t x i)) 0
  let r (n : ℕ) (x : E₀) (i : I) := quadraticPathRemainder (fun t => f n t x i)
  have he : ContDiffOn ℝ ∞ e U :=
    contDiffOn_pi.mpr (contDiffOn_coordinateDensityEuler S b hU hbs hdet)
  have hvary (n : ℕ) : ContDiffOn ℝ ∞ (l n) U ∧ ContDiffOn ℝ ∞ (q n) U :=
    coordinateDensityEuler_affine_variations_contDiffOn S hU b (h n) hbs (hhs n) hdet
  have hzero (n : ℕ) (x : E₀) (i : I) : f n 0 x i = e x i := by
    simp only [f, zero_smul, add_zero, e]
  have hEnd (n : ℕ) (x : E₀) (hx : x ∈ U) (i : I) : f n 1 x i = 0 := by
    have hPath : (fun y => b y + (1 : ℝ) • h n y) = normalizedChartMetric (g n) c := by
      funext y
      change b y + (1 : ℝ) • (normalizedChartMetric (g n) c y - b y) = _
      simp only [one_smul]
      abel
    have hMatch : EqOn (assembledCoordinateMetric S (normalizedChartMetric (g n) c))
        (metricComponents (coordinateBilinear (g n) c)) U := fun y _ =>
      congrFun (assembledCoordinateMetric_orthonormalMetricComponents (g n) (hSigG n).isSymmetric c) y
    change coordinateDensityEuler S (fun y => b y + (1 : ℝ) • h n y) x i = 0
    rw [hPath]
    exact coordinateDensityEuler_eq_zero_of_intrinsicVacuum S orthonormalMetricDirection_isSymmetric
      (g n) (hg n) (hSigG n) (hv n) c _ (hgS n) hMatch x hx i
  have hRem (n : ℕ) (x : E₀) (hx : x ∈ U) (i : I) :
      r n x i = 0 - e x i - l n x i - (1 / 2 : ℝ) * q n x i := by
    simp only [r, quadraticPathRemainder, hEnd n x hx i, hzero, l, q,
      linearizedCoordinateDensityEuler, f]
  have hr (n : ℕ) : ContDiffOn ℝ ∞ (r n) U := by
    have hSmooth : ContDiffOn ℝ ∞ (fun x => (0 : I → ℝ) - e x - l n x - (1 / 2 : ℝ) • q n x) U :=
      ((contDiffOn_const.sub he).sub (hvary n).1).sub ((hvary n).2.const_smul (1 / 2 : ℝ))
    exact hSmooth.congr (fun x hx => funext (hRem n x hx))
  let make (v : E₀ → I → ℝ) (hs : ContDiffOn ℝ ∞ v U) :=
    chartMetricCutoffTest hU v hs (ρ : E₀ → ℝ) (test_smooth ρ) hρ (test_compactSupport ρ)
  refine ⟨make e he, fun n => make (h n) (hhs n), fun n => make (l n) (hvary n).1,
    fun n => make (q n) (hvary n).2, fun n => make (r n) (hr n),
    fun x i => ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun n => ?_⟩
  · change Complex.ofReal ((ρ : E₀ → ℝ) x * e x i) = Complex.ofReal ((ρ : E₀ → ℝ) x * f 0 0 x i)
    rw [hzero]
  · apply Subtype.ext
    funext i
    ext x
    change ((ρ : E₀ → ℝ) x * e x i : ℝ) + ((ρ : E₀ → ℝ) x * l n x i : ℝ) +
      ((1 / 2 : ℝ) : ℂ) * ((ρ : E₀ → ℝ) x * q n x i : ℝ) +
      ((ρ : E₀ → ℝ) x * r n x i : ℝ) = (0 : ℂ)
    by_cases hx : x ∈ U
    · rw [hRem n x hx i]
      push_cast
      ring
    · simp only [image_eq_zero_of_notMem_tsupport (fun hy => hx (hρ hy)), zero_mul,
        Complex.ofReal_zero, mul_zero, add_zero]

end Burnett.V03.Palatini
