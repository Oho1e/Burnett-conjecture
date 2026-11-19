import Burnett.Analysis.SignedFourierWindow.SignAverage
import Burnett.Analysis.SignedFourierWindow.CalderonFiniteKernel
import Burnett.Analysis.SignedFourierWindow.KernelLpExhaustion

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Finset MeasureTheory
open scoped ENNReal

def annularKernel (a : SchwartzMap Space ℂ) (t : ℝ) (q : Space) (k : ℕ) :=
  shiftedSpatialKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) ((2:ℝ)^k*t) q

def annularSquare {n : ℕ} (e : Fin n ↪ ℕ) (a : SchwartzMap Space ℂ) (t : ℝ) (q : Space) (f : Space → ℂ) (x : Space) :=
  Real.sqrt (vectorEnergy (fun i => kernelApply (annularKernel a t q (e i)) f x))

private def wordCoefficient {n : ℕ} (e : Fin n ↪ ℕ) (s : Fin n → Bool) (k : ℕ) : ℂ := by
  classical
  exact if h : ∃ i,e i=k then signValue (s (Classical.choose h)) else 0

private theorem word_at {n : ℕ} (e : Fin n ↪ ℕ) (s : Fin n → Bool) (i : Fin n) :
    wordCoefficient e s (e i) = signValue (s i) := by
  classical
  have h : ∃ j,e j=e i := ⟨i,rfl⟩
  rw [wordCoefficient,dif_pos h,e.injective (Classical.choose_spec h)]

theorem kernelApply_measurable_ae (K : Space → ℂ) (hK : Continuous K) (f : Space → ℂ)
    (hf : AEStronglyMeasurable f volume) : Measurable (kernelApply K f) := by
  let g := hf.mk f
  have e : kernelApply K f = kernelApply K g := funext (fun x =>
    integral_congr_ae (hf.ae_eq_mk.mono fun y hy => congrArg (fun z => K (x-y)*z) hy))
  rw [e]
  exact measurable_kernelApply _ _ hK hf.stronglyMeasurable_mk.measurable

/-- A sign word on any finite set of distinct scales gives an admissible global
coefficient sequence and the same pointwise convolution sum for every Lᵖ input. -/
theorem window_sign_expansion {n : ℕ} (e : Fin n ↪ ℕ) (s : Fin n → Bool) (a : SchwartzMap Space ℂ)
    (t : ℝ) (ht : 0<t) (q : Space) (p : ℝ) (hp : 1≤p) (f : Space → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∃ c : ℕ → ℂ, (∀ k, ‖c k‖ ≤ 1) ∧
      ∀ x, signedVector (fun i => kernelApply (annularKernel a t q (e i)) f x) s =
        kernelApply (finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q (univ.map e) c) f x := by
  classical
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let K := fun i => annularKernel a t q (e i)
  refine ⟨wordCoefficient e s,?_,?_⟩
  · intro k
    unfold wordCoefficient
    split_ifs with h
    · cases s (Classical.choose h) <;> simp [signValue]
    · simp
  intro x
  have one (i : Fin n) : Integrable (fun y : Space => K i (x-y)*f y) := by
    obtain ⟨hK,hI,_,D,hD⟩ := finite_kernel_regular φ t ht q {e i} (fun _ => 1)
    have eq : finiteWindowKernel φ t q {e i} (fun _ => 1) = K i := by
      ext z; simp [finiteWindowKernel,K,annularKernel,φ]
    rw [eq] at hK hI hD
    exact kernel_integrand_Lp (K i) hK hI D hD p hp f hf x
  have step (i : Fin n) : signValue (s i)*kernelApply (K i) f x =
      ∫ y : Space, signValue (s i)*(K i (x-y)*f y) := (integral_const_mul _ _).symm
  change (∑ i, signValue (s i)*kernelApply (K i) f x) = _
  simp_rw [step]
  rw [← integral_finset_sum _ (fun i _ => (one i).const_mul (signValue (s i)))]
  unfold kernelApply
  apply integral_congr_ae
  filter_upwards with y
  simp only [finiteWindowKernel,sum_map,word_at,sum_mul,mul_assoc]
  rfl

end Burnett.Analysis.SignedFourierWindow
