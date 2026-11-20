import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace

/-- The frequency density of the physical trilinear pairing, with no
conjugation and with the test evaluated at negative sum frequency. -/
def triDensity (a : Joint → ℂ) (s : ℝ) (f g h : SchwartzMap E ℂ) (p : Joint) : ℂ :=
  a (s • p)*(𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2)*𝓕 (h : E → ℂ) (-(p.1+p.2))

theorem integrable_triDensity (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (s : ℝ) (f g h : SchwartzMap E ℂ) : Integrable (triDensity a s f g h) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  let H := SchwartzMap.fourierTransformCLM ℂ h
  obtain ⟨u,hu⟩ := hs.continuous.norm.exists_forall_ge_of_hasCompactSupport ha.norm
  have base : Integrable (fun p : Joint => F p.1*G p.2) := F.integrable.mul_prod G.integrable
  have hw : Integrable (fun p : Joint => a (s • p)*(F p.1*G p.2)) := base.bdd_mul
    ((hs.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable) ⟨_,fun p => hu (s • p)⟩
  have hc : Continuous (fun p : Joint => H (-(p.1+p.2))) := H.continuous.comp (continuous_fst.add continuous_snd).neg
  have last := hw.bdd_mul hc.aestronglyMeasurable ⟨_,fun p => H.norm_le_seminorm ℂ _⟩
  exact last.congr (.of_forall fun p => mul_comm _ _)

def testedBlock (a : Joint → ℂ) (s : ℝ) (f g h : SchwartzMap E ℂ) : ℂ :=
  ∫ x, (∫ y : Joint, blockKernel a y*(f (x-s • y.1)*g (x-s • y.2)))*h x

theorem testedBlock_density (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (s : ℝ) (f g h : SchwartzMap E ℂ) : testedBlock a s f g h = ∫ p, triDensity a s f g h p :=
  block_trilinear_fourier a ha hs s f g h

/-- Three independently dilated window factors are exactly the physical block
applied to the three filtered tests. -/
theorem windowed_density (a : Joint → ℂ) (s : ℝ) (f g h u v w : SchwartzMap E ℂ)
    (t r z : ℝ) (p : Joint) :
    triDensity a s (windowTest u f t) (windowTest v g r) (windowTest w h z) p =
    triDensity a s f g h p * (u (t • p.1)*v (r • p.2)*w (z • (-(p.1+p.2)))) := by
  simp only [triDensity,windowTest_fourier]
  ring

end Burnett.A02.FrequencySplit
