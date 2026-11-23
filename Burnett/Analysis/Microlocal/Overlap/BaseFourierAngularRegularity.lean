import Burnett.Analysis.Microlocal.Overlap.CompactParameterIntegral
import Burnett.Analysis.Microlocal.Overlap.CompactBaseZeroFourier

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped ContDiff FourierTransform InnerProduct

/-- A jointly smooth angular family is smooth on every fixed nonzero
frequency section. A smooth zero section completes the base regularity. -/
theorem contDiff_baseAngularSection (p : E → E → ℂ)
    (hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => p x 0)) (ξ : E) : ContDiff ℝ ∞ (fun x => p x ξ) := by
  by_cases hξ : ξ = 0
  · simpa only [hξ] using hZero
  · apply contDiffOn_univ.mp
    exact hJoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x _ => ⟨mem_univ x, hξ⟩)

/-- The compact-base transform is angularly smooth off the zero frequency. -/
theorem contDiffOn_baseFourierCoefficient
    (p : E → E → ℂ) (K : Set E) (hK : IsCompact K)
    (hSupport : ∀ ξ, tsupport (fun x => p x ξ) ⊆ K)
    (hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E))) (k : E) :
    ContDiffOn ℝ ∞ (baseFourierCoefficient p k) ({0}ᶜ : Set E) := by
  let phase (x : E) := Complex.exp ((↑(-2 * Real.pi * inner ℝ x k) : ℂ) * Complex.I)
  let G (q : E × E) := phase q.2 * p q.2 q.1
  have hInner : ContDiff ℝ ∞ (fun x : E => inner ℝ x k) := contDiff_id.inner ℝ contDiff_const
  have hArg : ContDiff ℝ ∞ (fun x : E => -2 * Real.pi * inner ℝ x k) :=
    contDiff_const.mul hInner
  have hPhase : ContDiff ℝ ∞ phase :=
    ((Complex.ofRealCLM.contDiff.comp hArg).mul contDiff_const).cexp
  have hSwap : ContDiff ℝ ∞ (Prod.swap : E × E → E × E) := contDiff_snd.prodMk contDiff_fst
  have hP : ContDiffOn ℝ ∞ (fun q : E × E => p q.2 q.1) (({0}ᶜ : Set E) ×ˢ univ) :=
    hJoint.comp hSwap.contDiffOn fun _ hq => ⟨hq.2, hq.1⟩
  have hG : ContDiffOn ℝ ∞ G (({0}ᶜ : Set E) ×ˢ univ) :=
    (hPhase.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : E × E → E))).contDiffOn.mul hP
  have hf := Burnett.Analysis.contDiffOn_integral_compact_parameter (volume : Measure E) K hK
    G ({0}ᶜ : Set E) isOpen_compl_singleton hG
  apply hf.congr
  intro ξ hξ
  rw [baseFourierCoefficient, Real.fourierIntegral_eq']
  change (∫ x, phase x • p x ξ) = ∫ x in K, phase x * p x ξ
  simp only [smul_eq_mul]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    have hp : p x ξ = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => p y ξ) (fun h => hx (hSupport ξ h))
    rw [hp, mul_zero]).symm

/-- Positive homogeneity of degree zero is preserved by base Fourier transformation. -/
theorem degreeZero_baseFourierCoefficient {p : E → E → ℂ}
    (hDegree : ∀ x, DegreeZero (p x)) (k : E) : DegreeZero (baseFourierCoefficient p k) := by
  intro t ht ξ
  have h : (fun x => p x (t • ξ)) = fun x => p x ξ := funext fun x => hDegree x t ht ξ
  unfold baseFourierCoefficient
  rw [h]

end Burnett.Microlocal.Overlap
