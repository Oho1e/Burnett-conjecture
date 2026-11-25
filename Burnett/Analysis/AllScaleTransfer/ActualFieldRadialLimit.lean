import Burnett.Analysis.AllScaleTransfer.ActualNearOuterAssembly
import Burnett.Analysis.AllScaleTransfer.SymmetricRadialFourierLimit

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open scoped ENNReal Topology BigOperators

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private theorem schwartzFieldLp3_norm_le_sum {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap E ℂ) :
    ‖schwartzFieldLp3 f‖ ≤ ∑ i, ‖(f i).toLp (ENNReal.ofReal 3) volume‖ := by
  classical
  let F : E → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 (fun i => f i x)
  let g (i : ι) (x : E) : ℝ := ‖f i x‖
  have hg (i : ι) : MemLp (g i) (ENNReal.ofReal 3) volume := ((f i).memLp _ volume).norm
  have pointwise : ∀ᵐ x ∂(volume : Measure E), ‖F x‖ ≤ (∑ i, g i) x := by
    apply Eventually.of_forall
    intro x
    rw [Finset.sum_apply]
    have repr : (∑ i, f i x • EuclideanSpace.single i (1 : ℂ)) = F x := by
      simpa only [EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun ι ℂ).sum_repr (F x)
    calc
      _ = ‖∑ i, f i x • EuclideanSpace.single i (1 : ℂ)‖ := congrArg norm repr.symm
      _ ≤ _ := by simpa only [norm_smul,EuclideanSpace.norm_single,norm_one,mul_one,g] using
        norm_sum_le (s := Finset.univ) (fun i : ι => f i x • EuclideanSpace.single i (1 : ℂ))
  have hnorm : eLpNorm F (ENNReal.ofReal 3) volume ≤
      ∑ i, eLpNorm (g i) (ENNReal.ofReal 3) volume :=
    (eLpNorm_mono_ae_real pointwise).trans
      (eLpNorm_sum_le (fun i _ => (hg i).aestronglyMeasurable)
        (by norm_num : 1 ≤ ENNReal.ofReal (3 : ℝ)))
  have finite (i : ι) : eLpNorm (g i) (ENNReal.ofReal 3) volume ≠ ⊤ :=
    (hg i).eLpNorm_lt_top.ne
  have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => finite i)) hnorm
  rw [ENNReal.toReal_sum (fun i _ => finite i)] at h
  simpa only [schwartzFieldLp3,Lp.norm_toLp,SchwartzMap.norm_toLp,F,g,eLpNorm_norm] using h

private theorem schwartzFieldLp3_coordinate {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap E ℂ) (i : ι) :
    fieldCoordinateLp i (schwartzFieldLp3 f) = (f i).toLp (ENNReal.ofReal 3) volume :=
  fieldCoordinateLp_toLp i (fieldArray_memLp (fun i x => f i x) (fun i => (f i).memLp _ volume))

/-- The actual common finite radial selection has a uniform field bound
with the Euclidean fiber norm and a fixed dimension factor. -/
theorem exists_finiteIntegerRadialTruncation_fieldLp3_bound {ι : Type*} [Fintype ι] :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (J : Finset ℤ) (ε : ℤ → ℂ), (∀ j ∈ J, ‖ε j‖ ≤ 1) →
      ∀ f : ι → SchwartzMap E ℂ,
        ‖schwartzFieldLp3 (fun i => finiteIntegerRadialTruncation J ε (f i))‖ ≤
          D * ‖schwartzFieldLp3 f‖ := by
  obtain ⟨C,hC,scalar⟩ := exists_finiteIntegerRadialTruncation_L3_bound
  refine ⟨(Fintype.card ι : ℝ) * C.toReal,by positivity,?_⟩
  intro J ε hε f
  let F (i : ι) := finiteIntegerRadialTruncation J ε (f i)
  have hScalar (i : ι) :
      ‖(F i).toLp (ENNReal.ofReal 3) volume‖ ≤ C.toReal * ‖(f i).toLp (ENNReal.ofReal 3) volume‖ := by
    rw [SchwartzMap.norm_toLp,SchwartzMap.norm_toLp,← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC.ne ((f i).memLp _ volume).eLpNorm_lt_top.ne)
      (scalar J ε hε (f i))
  have coord (i : ι) :
      ‖(F i).toLp (ENNReal.ofReal 3) volume‖ ≤ C.toReal * ‖schwartzFieldLp3 f‖ :=
    (hScalar i).trans (mul_le_mul_of_nonneg_left
      (by rw [← schwartzFieldLp3_coordinate f i]; exact fieldCoordinateLp_norm_le i _)
      ENNReal.toReal_nonneg)
  calc
    ‖schwartzFieldLp3 F‖ ≤ ∑ i, ‖(F i).toLp (ENNReal.ofReal 3) volume‖ :=
      schwartzFieldLp3_norm_le_sum F
    _ ≤ ∑ _ : ι, C.toReal * ‖schwartzFieldLp3 f‖ := Finset.sum_le_sum (fun i _ => coord i)
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]

/-- A uniform estimate of the finite contractions passes to the original
Schwartz Fourier form on the same three Euclidean fields. -/
theorem exists_radianTrilinearForm_field_bound_of_symmetric_radial_bounds
    {ι ξ : Type*} [Fintype ι] [Fintype ξ] :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (m : ξ → Joint → ℂ) (f : Fin 3 → ι → SchwartzMap E ℂ)
      (left middle right : ξ → ι),
      (∀ k, Integrable (radianTrilinearWeight (m k) (f 0 (left k)) (f 1 (middle k)) (f 2 (right k)))) →
      ∀ B : ℝ, 0 ≤ B →
      let F (N : ℕ) (i : Fin 3) (a : ι) :=
        finiteIntegerRadialTruncation (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun _ => 1) (f i a)
      (∀ N, ‖∑ k : ξ, radianTrilinearForm (m k) (F N 0 (left k)) (F N 1 (middle k))
          (F N 2 (right k))‖ ≤
        B * ‖schwartzFieldLp3 (F N 0)‖ * ‖schwartzFieldLp3 (F N 1)‖ * ‖schwartzFieldLp3 (F N 2)‖) →
      ‖∑ k : ξ, radianTrilinearForm (m k) (f 0 (left k)) (f 1 (middle k)) (f 2 (right k))‖ ≤
        (B * D^3) * ‖schwartzFieldLp3 (f 0)‖ * ‖schwartzFieldLp3 (f 1)‖ * ‖schwartzFieldLp3 (f 2)‖ := by
  obtain ⟨D,hD,radial⟩ := exists_finiteIntegerRadialTruncation_fieldLp3_bound (ι := ι)
  refine ⟨D,hD,?_⟩
  intro m f left middle right hInt B hB F bound
  let T (u : Fin 3 → ι → SchwartzMap E ℂ) :=
    ∑ k : ξ, radianTrilinearForm (m k) (u 0 (left k)) (u 1 (middle k)) (u 2 (right k))
  have lim : Tendsto (fun N => T (F N)) atTop (𝓝 (T f)) := by
    have h (k : ξ) : Tendsto
        (fun N => radianTrilinearForm (m k) (F N 0 (left k)) (F N 1 (middle k)) (F N 2 (right k)))
        atTop (𝓝 (radianTrilinearForm (m k) (f 0 (left k)) (f 1 (middle k)) (f 2 (right k)))) :=
      radianTrilinearForm_tendsto_symmetric_radial_truncations _ _ _ _ (hInt k)
    simpa only [T,Finset.sum_apply] using tendsto_finset_sum Finset.univ (fun k _ => h k)
  have fields (N : ℕ) (i : Fin 3) :
      ‖schwartzFieldLp3 (F N i)‖ ≤ D * ‖schwartzFieldLp3 (f i)‖ :=
    radial _ _ (fun _ _ => norm_one.le) (f i)
  apply le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp lim)
  intro N
  refine (bound N).trans ?_
  calc
    _ ≤ B * (D * ‖schwartzFieldLp3 (f 0)‖) * (D * ‖schwartzFieldLp3 (f 1)‖) *
      (D * ‖schwartzFieldLp3 (f 2)‖) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (fields N 0) hB) (fields N 1)
        (norm_nonneg _) (by positivity)) (fields N 2) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Burnett.A05
