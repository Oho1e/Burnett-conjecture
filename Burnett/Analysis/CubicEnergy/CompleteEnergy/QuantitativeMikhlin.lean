import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeWindowLp
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinIntersection

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Finset MeasureTheory Filter Metric Burnett.Fourier
open scoped Topology ContDiff ENNReal

private theorem normalized_multiplier_bound (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (m : E → ℝ), ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ) →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n m ξ‖ ≤ 1) →
      ∀ (M : BoundedSymbol E), (∀ ξ, M ξ = (m ξ : ℂ)) →
      ∀ (f : E → ℂ) (hf : MemLp f 2 volume), MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fourierMultiplier M (hf.toLp f) : E → ℂ) (ENNReal.ofReal p) volume ≤
          C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨B,hB,kernel⟩ := mikhlin_profile_kernel_bounds
  obtain ⟨C,hC,bound⟩ := unmodulated_window_all_Lp B hB p hp
  refine ⟨C,hC,?_⟩
  intro m hm hh jet M hM f hf hfp
  obtain ⟨a,ha,ac,cut⟩ := mikhlin_profile_exists m hm
  obtain ⟨sup,moment,deriv⟩ := kernel m hm hh 1 zero_le_one jet a ha cut
  let t := fun N : ℕ => ((2:ℝ)^N)⁻¹
  have ht (N : ℕ) : 0<t N := inv_pos.mpr (pow_pos (by norm_num) _)
  let I := fun N : ℕ => range (N+N)
  let A := fun n => mikhlinBands a cut (t n) (ht n) (I n)
  let F := hf.toLp f
  have ev : ∀ᵐ ξ ∂(volume : Measure E), ∀ᶠ N : ℕ in atTop, A N ξ = M ξ := by
    filter_upwards [(Set.countable_singleton (0:E)).ae_notMem volume] with ξ hx
    filter_upwards [mikhlin_scale_partition m hh a ha ξ hx] with n hn
    simpa only [A,t,I,mikhlinBands_eval,hM,bandFactor] using hn
  have conv := mikhlin_strong_L2 M A (2*SchwartzMap.seminorm ℝ 0 0 a) (fun n ξ => (A n).norm_le ξ) ev F
  obtain ⟨ns,_,aeLim⟩ := (tendstoInMeasure_of_tendsto_Lp conv).exists_seq_tendsto_ae
  have bn (n : ℕ) : eLpNorm (fourierMultiplier (A n) F : E → ℂ) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
    rw [eLpNorm_congr_ae (mikhlinBands_all_L2 a ac cut (t n) (ht n) (I n) f hf)]
    simp only [mul_one] at sup moment deriv
    exact bound a ac cut sup moment deriv (t n) (ht n) (I n) f hfp
  exact (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun n => Lp.aestronglyMeasurable (fourierMultiplier (A (ns n)) F)) _ aeLim).trans
    ((liminf_le_liminf (Eventually.of_forall (fun n => bn (ns n)))).trans_eq (liminf_const _))

private theorem zero_on_puncture (m : E → ℝ)
    (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 0 m ξ‖ ≤ 0)
    (ξ : E) (hx : ξ ≠ 0) : m ξ = 0 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hx
  let u := ‖ξ‖⁻¹ • ξ
  have hu : u ∈ sphere (0 : E) 1 := by
    rw [mem_sphere,dist_zero_right]
    change ‖‖ξ‖⁻¹ • ξ‖ = 1
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have h := jet u hu
  rw [norm_iteratedFDeriv_zero, norm_le_zero_iff] at h
  exact (hh ‖ξ‖⁻¹ (inv_pos.mpr hn) ξ).symm.trans h

private theorem fourierMultiplier_zero_of_ae (M : BoundedSymbol E)
    (h : ∀ᵐ ξ ∂(volume : Measure E), M ξ = 0) (F : ComplexL2 E) :
    fourierMultiplier M F = 0 := by
  apply fourierL2Equiv.injective
  rw [fourier_fourierMultiplier,map_zero]
  apply Lp.ext
  filter_upwards [h,symbolL2_ae M (fourierL2Equiv F),Lp.coeFn_zero ℂ 2 (volume : Measure E)] with ξ hξ hs hz
  simpa only [hs,hξ,zero_mul] using hz.symm

private theorem fourierMultiplier_smul_of_eq (M N : BoundedSymbol E) (c : ℂ)
    (h : ∀ ξ, M ξ = c * N ξ) (F : ComplexL2 E) :
    fourierMultiplier M F = c • fourierMultiplier N F := by
  apply fourierL2Equiv.injective
  rw [map_smul,fourier_fourierMultiplier,fourier_fourierMultiplier]
  apply Lp.ext
  let v := fourierL2Equiv F
  filter_upwards [symbolL2_ae M v,symbolL2_ae N v,Lp.coeFn_smul c (symbolL2 N v)] with ξ hM hN hs
  change symbolL2 M v ξ = (c • symbolL2 N v) ξ
  rw [hM,hs,Pi.smul_apply,hN,h ξ,smul_eq_mul,mul_assoc]

/-- In four dimensions the unmodulated degree-zero multiplier has a linear
bound from the supremum of environmental derivatives through order six on the
unit sphere. The multiplier is the actual Fourier L² operator, restricted to
L² ∩ Lᵖ, and the constant is selected before the symbol. -/
theorem homogeneous_multiplier_intersection_sphere_bound (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (m : E → ℝ), ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n m ξ‖ ≤ D) →
      ∀ (M : BoundedSymbol E), (∀ ξ, M ξ = (m ξ : ℂ)) →
      ∀ (f : E → ℂ) (hf : MemLp f 2 volume), MemLp f (ENNReal.ofReal p) volume →
        MemLp (fourierMultiplier M (hf.toLp f) : E → ℂ) (ENNReal.ofReal p) volume ∧
        eLpNorm (fourierMultiplier M (hf.toLp f) : E → ℂ) (ENNReal.ofReal p) volume ≤
          C * ENNReal.ofReal D * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,est⟩ := normalized_multiplier_bound p hp
  refine ⟨C,hC,?_⟩
  intro m hm hh D hD jet M hM f hf hfp
  let F := hf.toLp f
  have bound : eLpNorm (fourierMultiplier M F : E → ℂ) (ENNReal.ofReal p) volume ≤
      C * ENNReal.ofReal D * eLpNorm f (ENNReal.ofReal p) volume := by
    by_cases hD₀ : D = 0
    · have hz : ∀ᵐ ξ ∂(volume : Measure E), M ξ = 0 := by
        filter_upwards [(Set.countable_singleton (0:E)).ae_notMem volume] with ξ hx
        rw [hM, zero_on_puncture m hh (fun u hu => by simpa only [hD₀] using jet 0 (by decide) u hu) ξ hx]
        simp
      rw [fourierMultiplier_zero_of_ae M hz F, eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (volume : Measure E))]
      simp only [eLpNorm_zero]
      exact zero_le _
    have d : 0 < D := lt_of_le_of_ne hD (fun h => hD₀ h.symm)
    let m' := fun ξ => D⁻¹ • m ξ
    have hm' : ContDiffOn ℝ ∞ m' {ξ | ξ ≠ 0} := hm.const_smul D⁻¹
    have hh' (t : ℝ) (ht : 0<t) (ξ : E) : m' (t • ξ) = m' ξ := by
      simp only [m', hh t ht ξ]
    have unit (n : ℕ) (hn : n ≤ 6) (ξ : E) (hx : ξ ∈ sphere (0 : E) 1) :
        ‖iteratedFDeriv ℝ n m' ξ‖ ≤ 1 := by
      have hz : ξ ≠ 0 := ne_of_mem_sphere hx (by norm_num)
      have smooth : ContDiffAt ℝ ∞ m ξ := hm.contDiffAt
        (isClosed_singleton.isOpen_compl.mem_nhds hz)
      have hsmall : ContDiffAt ℝ n m ξ := smooth.of_le (by exact_mod_cast le_top)
      change ‖iteratedFDeriv ℝ n (fun u => D⁻¹ • m u) ξ‖ ≤ 1
      rw [iteratedFDeriv_const_smul_apply' hsmall,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hD)]
      exact (mul_le_mul_of_nonneg_left (jet n hn ξ hx) (inv_nonneg.mpr hD)).trans_eq
        (inv_mul_cancel₀ hD₀)
    let M' : BoundedSymbol E := {
      toFun := fun ξ => ((D⁻¹ : ℝ) : ℂ) * M ξ
      measurable := aestronglyMeasurable_const.mul M.measurable
      bound := D⁻¹ * M.bound
      bound_nonneg := mul_nonneg (inv_nonneg.mpr hD) M.bound_nonneg
      norm_le := fun ξ => by
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hD)]
        exact mul_le_mul_of_nonneg_left (M.norm_le ξ) (inv_nonneg.mpr hD) }
    have hM' (ξ) : M' ξ = (m' ξ : ℂ) := by
      change ((D⁻¹ : ℝ) : ℂ) * M ξ = ((D⁻¹ * m ξ : ℝ) : ℂ)
      rw [hM,Complex.ofReal_mul]
    have scale : ∀ ξ, M ξ = (D : ℂ) * M' ξ := by
      intro ξ
      change _ = (D : ℂ) * (((D⁻¹ : ℝ) : ℂ) * M ξ)
      rw [← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ d.ne',Complex.ofReal_one,one_mul]
    have hn := est m' hm' hh' unit M' hM' f hf hfp
    have scalar : ‖(D : ℂ)‖ₑ = ENNReal.ofReal D := by
      rw [← ofReal_norm_eq_enorm,Complex.norm_real,Real.norm_of_nonneg hD]
    rw [fourierMultiplier_smul_of_eq M M' D scale F, eLpNorm_congr_ae (Lp.coeFn_smul (D : ℂ) _)]
    exact (eLpNorm_const_smul_le.trans (mul_le_mul_left' hn _)).trans_eq (by rw [scalar]; ring)
  exact ⟨⟨Lp.aestronglyMeasurable _,bound.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top) hfp.2)⟩,bound⟩

end Burnett.A02.FrequencySplit
