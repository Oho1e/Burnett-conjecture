import Burnett.Analysis.LocalWeakDerivative

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.WeakTestCalculus

open MeasureTheory Filter Set
open scoped ContDiff Topology
open Burnett.Analysis.LocalWeakDerivative

def SmoothWeakZero (U : Set Space) (f : ℕ → Space → ℝ) : Prop :=
  (∀ n, ContDiffOn ℝ ∞ (f n) U) ∧
  ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    Tendsto (fun n => ∫ x, ψ x * f n x) atTop (𝓝 0)

theorem SmoothWeakZero.of_uniform {U : Set Space} (hU : IsOpen U) {f : ℕ → Space → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hu : ∀ K : Set Space, IsCompact K → K ⊆ U →
      TendstoUniformlyOn f (fun _ => 0) atTop K) : SmoothWeakZero U f :=
  ⟨hf, fun _ hψ hcψ hsψ => integral_test_local_tendsto_zero hU hψ hcψ hsψ hf hu⟩

theorem SmoothWeakZero.congr {U : Set Space} {f g : ℕ → Space → ℝ}
    (hf : SmoothWeakZero U f) (heq : ∀ n x, g n x = f n x) : SmoothWeakZero U g := by
  refine ⟨fun n => (hf.1 n).congr (fun x _ => heq n x), ?_⟩
  intro ψ hψ hcψ hsψ
  apply (hf.2 ψ hψ hcψ hsψ).congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => congrArg (fun z => ψ x * z) (heq n x).symm)

theorem SmoothWeakZero.zero (U : Set Space) : SmoothWeakZero U (fun _ _ => 0) := by
  refine ⟨fun _ => contDiffOn_const, ?_⟩
  intro ψ _ _ _
  simp only [mul_zero, integral_zero]
  exact tendsto_const_nhds

theorem SmoothWeakZero.mul_fixed {U : Set Space} (hU : IsOpen U)
    {f : ℕ → Space → ℝ} (hf : SmoothWeakZero U f)
    {A : Space → ℝ} (hA : ContDiffOn ℝ ∞ A U) :
    SmoothWeakZero U (fun n x => A x * f n x) := by
  refine ⟨fun n => hA.mul (hf.1 n), ?_⟩
  intro ψ hψ hcψ hsψ
  have h := hf.2 (fun x => ψ x * A x) (contDiff_test_mul_local hU hψ hsψ hA)
    hcψ.mul_right (tsupport_mul_subset_left.trans hsψ)
  apply h.congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

theorem SmoothWeakZero.add {U : Set Space} (hU : IsOpen U)
    {f g : ℕ → Space → ℝ} (hf : SmoothWeakZero U f) (hg : SmoothWeakZero U g) :
    SmoothWeakZero U (fun n x => f n x + g n x) := by
  refine ⟨fun n => (hf.1 n).add (hg.1 n), ?_⟩
  intro ψ hψ hcψ hsψ
  have h := (hf.2 ψ hψ hcψ hsψ).add (hg.2 ψ hψ hcψ hsψ)
  simp only [add_zero] at h
  apply h.congr
  intro n
  have hif : Integrable (fun x => ψ x * f n x) (volume : Measure Space) :=
    (contDiff_test_mul_local hU hψ hsψ (hf.1 n)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  have hig : Integrable (fun x => ψ x * g n x) (volume : Measure Space) :=
    (contDiff_test_mul_local hU hψ hsψ (hg.1 n)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  have hi := integral_add hif hig
  simpa only [Pi.add_apply, ← mul_add] using hi.symm

theorem SmoothWeakZero.sub {U : Set Space} (hU : IsOpen U)
    {f g : ℕ → Space → ℝ} (hf : SmoothWeakZero U f) (hg : SmoothWeakZero U g) :
    SmoothWeakZero U (fun n x => f n x - g n x) := by
  refine ⟨fun n => (hf.1 n).sub (hg.1 n), ?_⟩
  intro ψ hψ hcψ hsψ
  have h := (hf.2 ψ hψ hcψ hsψ).sub (hg.2 ψ hψ hcψ hsψ)
  simp only [sub_zero] at h
  apply h.congr
  intro n
  have hif : Integrable (fun x => ψ x * f n x) (volume : Measure Space) :=
    (contDiff_test_mul_local hU hψ hsψ (hf.1 n)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  have hig : Integrable (fun x => ψ x * g n x) (volume : Measure Space) :=
    (contDiff_test_mul_local hU hψ hsψ (hg.1 n)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  have hi := integral_sub hif hig
  simpa only [Pi.sub_apply, ← mul_sub] using hi.symm

theorem SmoothWeakZero.directional {U : Set Space} (hU : IsOpen U)
    {f : ℕ → Space → ℝ} (hf : SmoothWeakZero U f) (v : Space) :
    SmoothWeakZero U (fun n x => fderiv ℝ (f n) x v) := by
  refine ⟨fun n => ((hf.1 n).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const, ?_⟩
  intro ψ hψ hcψ hsψ
  have hDψ : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have h := (hf.2 _ hDψ (hcψ.fderiv_apply ℝ v)
    ((tsupport_directional_subset ψ v).trans hsψ)).neg
  simp only [neg_zero] at h
  exact h.congr (fun n => (integral_test_directional_local hU hψ hcψ hsψ (hf.1 n) v).symm)

theorem SmoothWeakZero.finset_sum {U : Set Space} (hU : IsOpen U)
    {ι : Type*} (s : Finset ι) {f : ι → ℕ → Space → ℝ}
    (hf : ∀ i ∈ s, SmoothWeakZero U (f i)) :
    SmoothWeakZero U (fun n x => ∑ i ∈ s, f i n x) := by
  refine ⟨fun n => ContDiffOn.sum (fun i hi => (hf i hi).1 n), ?_⟩
  intro ψ hψ hcψ hsψ
  have h := tendsto_finset_sum s (fun i hi => (hf i hi).2 ψ hψ hcψ hsψ)
  simp only [Finset.sum_const_zero] at h
  apply h.congr
  intro n
  have hi (i : ι) (his : i ∈ s) : Integrable (fun x => ψ x * f i n x) :=
    (contDiff_test_mul_local hU hψ hsψ ((hf i his).1 n)).continuous.integrable_of_hasCompactSupport hcψ.mul_right
  rw [← integral_finset_sum s hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (Finset.mul_sum s (fun i => f i n x) (ψ x)).symm)

end Burnett.Analysis.WeakTestCalculus
