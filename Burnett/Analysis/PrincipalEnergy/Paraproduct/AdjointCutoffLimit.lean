import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualParaproductMass

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped Topology NNReal ComplexConjugate

/-- The Hilbert-space pairing of the actual bilateral paraproduct applied
to a Schwartz input with an expanding constant test tends to zero. -/
theorem exists_compactBase_bilateral_paraproduct_adjoint_expanding_test_tendsto
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0)
    (r f χ : SchwartzMap Space ℂ) (hOne : ∀ x : Space, ‖x‖≤1 → χ x=1)
    (L : NNReal) (U : ℝ) (hU : 0≤U)
    (hLip : LipschitzWith L r) (hR : ∀ x, ‖r x‖≤U) (t : ℝ) (ht : 0<t) :
    let b := coefficientCommutatorConstant a r
    let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
    ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
      let v := fun j => (hTerm j).toLp (T j)
      Summable v ∧ Tendsto (fun n : ℕ => ∫ x,
        conj ((∑' j, v j) x) * expandingInput χ ((n:ℝ)+1) x) atTop (𝓝 0) := by
  intro b T
  obtain ⟨hTerm,hSum,hI,hZ⟩ := exists_compactBase_bilateral_two_window_paraproduct_integral_zero
    ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀ r f L U hU hLip hR t ht
  let v := fun j => (hTerm j).toLp (T j)
  let P : Space → ℂ := ((∑' j, v j : ComplexL2 Space) : Space → ℂ)
  have hP : Integrable P volume := hI
  have hP₀ : (∫ x, P x)=0 := hZ
  refine ⟨hTerm,hSum,?_⟩
  let K := SchwartzMap.seminorm ℝ 0 0 χ
  let R (n : ℕ) : ℝ := (n:ℝ)+1
  let G (n : ℕ) (x : Space) := conj (P x)*expandingInput χ (R n) x
  have hMeas (n : ℕ) : AEStronglyMeasurable (G n) (volume : Measure Space) :=
    hP.aestronglyMeasurable.star.mul
      (χ.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable
  have hDom (n : ℕ) (x : Space) : ‖G n x‖ ≤ K*‖P x‖ := by
    dsimp only [G,expandingInput]
    rw [norm_mul,Complex.norm_conj,mul_comm ‖P x‖]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ χ _) (norm_nonneg _)
  have hPoint (x : Space) : Tendsto (fun n => G n x) atTop (𝓝 (conj (P x))) := by
    obtain ⟨N,hN⟩ := exists_nat_ge ‖x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast hn
    have hPos : 0<R n := by unfold R; positivity
    have hNR : ‖x‖≤R n := by unfold R; linarith
    have hScale : ‖(R n)⁻¹ • x‖≤1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hPos.le),← div_eq_inv_mul]
      exact (div_le_one hPos).mpr hNR
    simp only [G,expandingInput,hOne _ hScale,mul_one]
  have hLimit := tendsto_integral_of_dominated_convergence (fun x => K*‖P x‖) hMeas
    (hP.norm.const_mul K) (fun n => Eventually.of_forall (hDom n)) (Eventually.of_forall hPoint)
  rw [integral_conj,hP₀,map_zero] at hLimit
  exact hLimit

end Burnett.Analysis.CarlesonEmbedding
