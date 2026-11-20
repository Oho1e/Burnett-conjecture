import Burnett.Analysis.CubicEnergy.JointMultiplier.KernelHolder
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped ENNReal FourierTransform ContDiff

abbrev Freq8 := EuclideanSpace ℝ (Fin 4 ⊕ Fin 4)

/-- Splitting the eight frequency coordinates into the two four-dimensional inputs. -/
def splitFreq : Freq8 ≃L[ℝ] Joint :=
  ((WithLp.linearEquiv 2 ℝ ((Fin 4 ⊕ Fin 4) → ℝ)).trans
    ((LinearEquiv.sumPiEquivProdPi ℝ (Fin 4) (Fin 4) (fun _ => ℝ)).trans
     (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm
       (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm))).toContinuousLinearEquiv

theorem splitFreq_preserves_volume : MeasurePreserving splitFreq volume volume := by
  have single := PiLp.volume_preserving_toLp (Fin 4)
  exact (single.prod single).comp ((volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin 4 ⊕ Fin 4 => ℝ)).comp (PiLp.volume_preserving_ofLp _))

/-- The physical kernel is the genuine inverse Fourier integral of the reference symbol. -/
def blockKernel (a : Joint → ℂ) (y : Joint) : ℂ :=
  𝓕⁻ (fun ξ : Freq8 => a (splitFreq ξ)) (splitFreq.symm y)

theorem blockKernel_integrable (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a) :
    Integrable (blockKernel a) ∧ Continuous (blockKernel a) := by
  let A : SchwartzMap Freq8 ℂ :=
    (ha.comp_homeomorph splitFreq.toHomeomorph).toSchwartzMap (hs.comp splitFreq.contDiff)
  let K := (SchwartzMap.fourierTransformCLE ℂ).symm A
  have hK : (K : Freq8 → ℂ) = 𝓕⁻ (fun ξ : Freq8 => a (splitFreq ξ)) :=
    SchwartzMap.fourierTransformCLE_symm_apply _ _
  have hk : blockKernel a = (K : Freq8 → ℂ) ∘ splitFreq.symm := by
    funext y
    change _ = (K : Freq8 → ℂ) (splitFreq.symm y)
    rw [hK]; rfl
  rw [hk]
  have hmp := splitFreq_preserves_volume.symm splitFreq.toHomeomorph.toMeasurableEquiv
  exact ⟨hmp.integrable_comp_of_integrable K.integrable,K.continuous.comp splitFreq.symm.continuous⟩

/-- The reference inverse-transform mass provides one finite constant for every scale
and every admissible triple of exponents. -/
theorem blockKernel_uniform_pairing (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {p s r t : ℝ≥0∞} [ENNReal.HolderTriple p s r]
      [ENNReal.HolderTriple r t 1] (f v w : SchwartzMap E ℂ) (scale : ℝ),
      (∫⁻ y : Joint, ∫⁻ x, ‖blockKernel a y * (f (x-scale • y.1)*v (x-scale • y.2)*w x)‖ₑ) ≤
        C * (eLpNorm (f : E → ℂ) p volume * eLpNorm (v : E → ℂ) s volume * eLpNorm (w : E → ℂ) t volume) := by
  obtain ⟨hi,hc⟩ := blockKernel_integrable a ha hs
  refine ⟨_,hi.hasFiniteIntegral,?_⟩
  intro p s r t _ _ f v w scale
  exact dilated_kernel_trilinear_bound (p := p) (s := s) (r := r) (t := t) _ hc.measurable f v w scale

end Burnett.A02.FrequencySplit
