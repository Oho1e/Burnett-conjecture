import Burnett.Analysis.Fourier.L2Extension

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Data for an actual bounded measurable fixed frequency symbol. -/
structure BoundedSymbol (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] where
  toFun : V → ℂ
  measurable : AEStronglyMeasurable toFun volume
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ ξ, ‖toFun ξ‖ ≤ bound

instance : CoeFun (BoundedSymbol V) (fun _ => V → ℂ) := ⟨BoundedSymbol.toFun⟩

theorem symbol_product_memLp (m : BoundedSymbol V) (u : ComplexL2 V) :
    MemLp (fun ξ => m ξ * u ξ) 2 (volume : Measure V) := by
  apply (Lp.memLp u).of_le_mul (c := m.bound) (m.measurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards with ξ
  change ‖m ξ * u ξ‖ ≤ m.bound * ‖u ξ‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _)

def symbolL2 (m : BoundedSymbol V) (u : ComplexL2 V) : ComplexL2 V :=
  (symbol_product_memLp m u).toLp (fun ξ => m ξ * u ξ)

theorem symbolL2_ae (m : BoundedSymbol V) (u : ComplexL2 V) :
    (symbolL2 m u : V → ℂ) =ᵐ[volume] (fun ξ => m ξ * u ξ) :=
  (symbol_product_memLp m u).coeFn_toLp

def symbolLinear (m : BoundedSymbol V) : ComplexL2 V →ₗ[ℂ] ComplexL2 V where
  toFun := symbolL2 m
  map_add' u v := by
    apply Lp.ext
    filter_upwards [symbolL2_ae m (u + v), symbolL2_ae m u, symbolL2_ae m v,
      Lp.coeFn_add u v, Lp.coeFn_add (symbolL2 m u) (symbolL2 m v)] with ξ ha hu hv huv hout
    rw [ha, hout]
    simp only [Pi.add_apply]
    rw [hu, hv, huv]
    simp only [Pi.add_apply]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [symbolL2_ae m (c • u), symbolL2_ae m u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (symbolL2 m u)] with ξ ha hu hcu hout
    simp only [RingHom.id_apply]
    rw [ha, hout]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu, hcu]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem symbolL2_norm_le (m : BoundedSymbol V) (u : ComplexL2 V) :
    ‖symbolL2 m u‖ ≤ m.bound * ‖u‖ := by
  have hb := norm_toLp_le_of_norm_le (symbol_product_memLp m u) (Lp.memLp u)
    m.bound_nonneg (fun ξ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _))
  simpa only [Lp.toLp_coeFn] using hb

def symbolCLM (m : BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  (symbolLinear m).mkContinuous m.bound (symbolL2_norm_le m)

/-- The physical-space multiplier is Fourier, actual symbol multiplication,
then inverse Fourier on the complete L² space. -/
def fourierMultiplier (m : BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  fourierL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((symbolCLM m).comp fourierL2Equiv.toContinuousLinearEquiv.toContinuousLinearMap)

theorem fourierMultiplier_apply (m : BoundedSymbol V) (u : ComplexL2 V) :
    fourierMultiplier m u = fourierL2Equiv.symm (symbolL2 m (fourierL2Equiv u)) := rfl

theorem fourier_fourierMultiplier (m : BoundedSymbol V) (u : ComplexL2 V) :
    fourierL2Equiv (fourierMultiplier m u) = symbolL2 m (fourierL2Equiv u) :=
  fourierL2Equiv.apply_symm_apply _

theorem fourierMultiplier_norm_le (m : BoundedSymbol V) (u : ComplexL2 V) :
    ‖fourierMultiplier m u‖ ≤ m.bound * ‖u‖ := by
  rw [fourierMultiplier_apply, LinearIsometryEquiv.norm_map]
  exact (symbolL2_norm_le m _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

theorem l2_norm_sq_integral (u : ComplexL2 V) : ‖u‖^2 = ∫ ξ, ‖u ξ‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem symbolL2_norm_sq_le_restrict (m : BoundedSymbol V) {S : Set V}
    (hS : MeasurableSet S) (hmS : ∀ ξ, ξ ∉ S → m ξ = 0) (u : ComplexL2 V) :
    ‖symbolL2 m u‖^2 ≤ m.bound^2 * ∫ ξ in S, ‖u ξ‖^2 := by
  have hui : Integrable (fun ξ => ‖u ξ‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hmi : Integrable (fun ξ => ‖m ξ * u ξ‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (symbol_product_memLp m u).1).mp (symbol_product_memLp m u)
  rw [l2_norm_sq_integral]
  have heq : (∫ ξ, ‖symbolL2 m u ξ‖^2) = ∫ ξ, ‖m ξ * u ξ‖^2 :=
    integral_congr_ae ((symbolL2_ae m u).fun_comp (fun z => ‖z‖^2))
  rw [heq, ← integral_const_mul, ← integral_indicator hS]
  apply integral_mono hmi ((hui.const_mul _).indicator hS)
  intro ξ
  by_cases hx : ξ ∈ S
  · rw [Set.indicator_of_mem hx]
    change ‖m ξ * u ξ‖^2 ≤ m.bound^2 * ‖u ξ‖^2
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) m.bound_nonneg).mpr (m.norm_le ξ)) (sq_nonneg _)
  · simp [Set.indicator_of_notMem hx, hmS ξ hx]

theorem fourierMultiplier_schwartz_norm_sq_le (m : BoundedSymbol V) {S : Set V}
    (hS : MeasurableSet S) (hmS : ∀ ξ, ξ ∉ S → m ξ = 0) (f : SchwartzMap V ℂ) :
    ‖fourierMultiplier m (f.toLp 2 volume)‖^2 ≤
      m.bound^2 * ∫ ξ in S, ‖Real.fourierIntegral (f : V → ℂ) ξ‖^2 := by
  rw [fourierMultiplier_apply, LinearIsometryEquiv.norm_map]
  have hb := symbolL2_norm_sq_le_restrict m hS hmS (fourierL2Equiv (f.toLp 2 volume))
  have heq : (∫ ξ in S, ‖fourierL2Equiv (f.toLp 2 volume) ξ‖^2) =
      ∫ ξ in S, ‖Real.fourierIntegral (f : V → ℂ) ξ‖^2 :=
    integral_congr_ae ((fourierL2Equiv_schwartz_ae f).restrict.fun_comp (fun z => ‖z‖^2))
  rwa [heq] at hb

/-- Fixed bounded symbols supported in an off-cone region consume the
actual Fourier energy convergence, and give physical whole-space L²
convergence, with inverse-transform tails retained. -/
theorem fourierMultiplier_schwartz_tendsto_zero (m : BoundedSymbol V) {S : Set V}
    (hS : MeasurableSet S) (hmS : ∀ ξ, ξ ∉ S → m ξ = 0)
    (f : ℕ → SchwartzMap V ℂ)
    (hf : Tendsto (fun n => ∫ ξ in S, ‖Real.fourierIntegral (f n : V → ℂ) ξ‖^2)
      atTop (𝓝 0)) :
    Tendsto (fun n => fourierMultiplier m ((f n).toLp 2 volume)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ‖fourierMultiplier m ((f n).toLp 2 volume)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (fun n => fourierMultiplier_schwartz_norm_sq_le m hS hmS (f n))
    simpa only [mul_zero] using hf.const_mul (m.bound^2)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht := hs.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

end Burnett.Fourier
