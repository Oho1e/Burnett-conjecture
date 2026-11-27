import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeylFiniteFormalSymmetry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory
open Burnett.A02.FrequencySplit (E)
open scoped ComplexConjugate Topology

/-- The manuscript uses the Lebesgue pairing linear in its first argument. -/
def weylLebesguePairing (f g : E → ℂ) : ℂ := ∫ x : E, f x * conj (g x)

private theorem weyl_lebesgue_pairing_conj (f g : E → ℂ) :
    conj (weylLebesguePairing f g) = weylLebesguePairing g f := by
  unfold weylLebesguePairing
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [mul_comm]

/-- Pointwise limits with a uniform output bound converge in the actual
Lebesgue pairing against every Schwartz test. -/
theorem schwartz_weyl_pairing_tendsto_of_uniform_output_bound
    (F : ℕ → E → ℂ) (f : E → ℂ)
    (meas : ∀ n, AEStronglyMeasurable (F n) volume)
    (C : ℝ) (bound : ∀ n x, ‖F n x‖ ≤ C)
    (limit : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (v : SchwartzMap E ℂ) :
    Integrable (fun x => f x * conj (v x)) volume ∧
    Tendsto (fun n => weylLebesguePairing (F n) v) atTop (𝓝 (weylLebesguePairing f v)) := by
  have vm : AEStronglyMeasurable (fun x => conj (v x)) volume :=
    (Complex.continuous_conj.comp v.continuous).aestronglyMeasurable
  have fM : AEStronglyMeasurable f volume :=
    aestronglyMeasurable_of_tendsto_ae atTop meas (Eventually.of_forall limit)
  have cb (x : E) : ‖f x‖ ≤ C :=
    le_of_tendsto (limit x).norm (Eventually.of_forall fun n => bound n x)
  have vi : Integrable (v : E → ℂ) volume := v.integrable
  let g (x : E) := C * ‖v x‖
  have gi : Integrable g volume := vi.norm.const_mul C
  have dom (h : E → ℂ) (hb : ∀ x, ‖h x‖ ≤ C) (x : E) : ‖h x * conj (v x)‖ ≤ g x := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  refine ⟨gi.mono' (fM.mul vm) (Eventually.of_forall (dom f cb)),?_⟩
  exact tendsto_integral_of_dominated_convergence g (fun n => (meas n).mul vm) gi
    (fun n => Eventually.of_forall (dom (F n) (bound n)))
    (Eventually.of_forall fun x => (limit x).mul_const (conj (v x)))

/-- A sequence of formally symmetric actions remains symmetric once the
two actual Schwartz pairings converge by dominated convergence. -/
theorem schwartz_weyl_formal_symmetry_of_uniform_pointwise_limit
    (B : ℕ → SchwartzMap E ℂ → E → ℂ) (A : SchwartzMap E ℂ → E → ℂ)
    (meas : ∀ n u, AEStronglyMeasurable (B n u) volume)
    (bound : ∀ u, ∃ C : ℝ, ∀ n x, ‖B n u x‖ ≤ C)
    (limit : ∀ u x, Tendsto (fun n => B n u x) atTop (𝓝 (A u x)))
    (sym : ∀ n (u v : SchwartzMap E ℂ),
      weylLebesguePairing (B n u) v = weylLebesguePairing u (B n v))
    (u v : SchwartzMap E ℂ) :
    Tendsto (fun n => weylLebesguePairing (B n u) v) atTop (𝓝 (weylLebesguePairing (A u) v)) ∧
    Tendsto (fun n => weylLebesguePairing u (B n v)) atTop (𝓝 (weylLebesguePairing u (A v))) ∧
    weylLebesguePairing (A u) v = weylLebesguePairing u (A v) := by
  obtain ⟨C,cb⟩ := bound u
  obtain ⟨D,db⟩ := bound v
  have l := (schwartz_weyl_pairing_tendsto_of_uniform_output_bound (fun n => B n u) (A u)
    (fun n => meas n u) C cb (limit u) v).2
  have r := (schwartz_weyl_pairing_tendsto_of_uniform_output_bound (fun n => B n v) (A v)
    (fun n => meas n v) D db (limit v) u).2
  have r' : Tendsto (fun n => weylLebesguePairing u (B n v)) atTop (𝓝 (weylLebesguePairing u (A v))) := by
    have h : Tendsto (fun n => conj (weylLebesguePairing (B n v) u)) atTop
        (𝓝 (conj (weylLebesguePairing (A v) u))) :=
      Complex.continuous_conj.continuousAt.tendsto.comp r
    simpa only [weyl_lebesgue_pairing_conj] using h
  exact ⟨l,r',tendsto_nhds_unique (l.congr' (Eventually.of_forall fun n => sym n u v)) r'⟩

end Burnett.A03
