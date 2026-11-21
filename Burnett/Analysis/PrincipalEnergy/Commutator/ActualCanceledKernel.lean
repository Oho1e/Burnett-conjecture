import Burnett.Analysis.PrincipalEnergy.Commutator.ActualFullCommutatorKernel
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductSeparatedPair

set_option autoImplicit false
set_option maxHeartbeats 4700000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate NNReal Topology InnerProductSpace

/-- The actual low-plus-high commutator and the same bilateral
paraproduct used to cancel both constant distributions. -/
def canceledCoefficientKernel (a : Space → Space → ℂ) (r : SchwartzMap Space ℂ)
    (φ ψ θ : SchwartzMap Space ℂ) (t : ℝ) (x y : Space) : ℂ :=
  let P := bilateralParaproductKernel φ ψ θ t (coefficientCommutatorConstant a r)
  fullCoefficientKernel a r x y-P x y+adjointKernel P x y

/-- The single physical canceled form has both constant tests, the full
off-diagonal kernel identity and uniform size and two first differences.
The coefficient bounds are on the actual function and its real derivative. -/
theorem exists_compactBase_canceledCoefficientPair_with_kernel
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (hSym : FirstOrderFormalSymmetry a)
    (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (hφ₁ : (∫ z, φ z)=1) (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0)
    (hFac : WaveletFactorization φ ψ θ) :
    ∃ M C : ℝ, 0≤M ∧ 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x)=r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖≤U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖≤(L:ℝ)) →
      ∀ (t : ℝ), 0<t →
      let b := coefficientCommutatorConstant a r
      let K := canceledCoefficientKernel a r φ ψ θ t
      ∃ P : SchwartzMap Space ℂ → ComplexL2 Space,
        (∀ f : SchwartzMap Space ℂ,
          let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
          ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
            let v (j : ℤ) := (hTerm j).toLp (T j)
            Summable v ∧ P f=(∑' j, v j) ∧ ‖P f‖≤M*(U+(L:ℝ))*‖f.toLp 2 volume‖) ∧
        (∀ (χ g : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)),
          (∀ x : Space, ‖x‖≤1 → χ x=1) →
          Tendsto (fun n => canceledCoefficientPair a r P (expandingTestSchwartz χ hχ n) g) atTop (𝓝 0) ∧
          Tendsto (fun n => canceledCoefficientPair a r P g (expandingTestSchwartz χ hχ n)) atTop (𝓝 0)) ∧
        CalderonZygmundKernelBounds K (C*(U+(L:ℝ))) ∧
        (∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
          ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
          canceledCoefficientPair a r P f g =
            ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
              ∂((volume : Measure Space).prod volume)) := by
  obtain ⟨M,hM,hForm⟩ := exists_compactBase_canceledCoefficientPair
    ha hBase hCont hSym φ ψ θ hφ hψ hφ₁ hψ₀ hθ₀ hFac
  obtain ⟨A,hA,hFull⟩ := exists_fullCoefficientKernel_bounds ha
  obtain ⟨D,hD,hPara⟩ := exists_compactBase_bilateral_paraproduct_kernel_bounds
    ha hBase hCont φ ψ θ hφ hψ hθ hψ₀
  refine ⟨M,A+2*D,hM,add_nonneg hA (mul_nonneg (by norm_num) hD),?_⟩
  intro r L U hr hReal hUae hLae t ht b K
  obtain ⟨hU,hR,hLip⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hUae hLae
  obtain ⟨P,hP,hCancel⟩ := hForm r L U hU hr hReal hLip hR t ht
  let T := fullCoefficientKernel a r
  let Q := bilateralParaproductKernel φ ψ θ t b
  have hT : CalderonZygmundKernelBounds T (A*(U+(L:ℝ))) := (hFull r L hLip).mono <| by
    rw [mul_comm (L:ℝ) A]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hU) hA
  obtain ⟨hSize,hSource,hTarget⟩ := hPara r L U hU hLip hR t ht
  have hQ : CalderonZygmundKernelBounds Q (D*(U+(L:ℝ))) :=
    ⟨mul_nonneg hD (add_nonneg hU L.coe_nonneg),fun x y h => (hSize x y h).2,hSource,hTarget⟩
  have hCombined := (hT.add hQ.neg).add hQ.adjoint
  have hCeq : A*(U+(L:ℝ))+D*(U+(L:ℝ))+D*(U+(L:ℝ))=(A+2*D)*(U+(L:ℝ)) := by ring
  rw [hCeq] at hCombined
  have hKernel : CalderonZygmundKernelBounds K ((A+2*D)*(U+(L:ℝ))) := by
    simpa only [K,canceledCoefficientKernel,sub_eq_add_neg,T,Q,b] using hCombined
  refine ⟨P,hP,hCancel,hKernel,?_⟩
  intro f g hf d hd hGap
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  have hPair (f' g' : SchwartzMap Space ℂ) (hSep : ∀ x y : Space, f' y≠0 → g' x≠0 → d≤‖x-y‖) :
      inner ℂ (g'.toLp 2 volume) (P f') =
        ∫ p : Space × Space, conj (g' p.1)*(Q p.1 p.2*f' p.2) ∂μ := by
    obtain ⟨_,_,hWitness,_⟩ := hP f'
    obtain ⟨_,_,hExact⟩ := exists_compactBase_bilateral_paraproduct_separated_pair_eq_kernel
      ha hBase hCont φ ψ θ hφ hψ hθ hψ₀ hθ₀ r f' g' L U hU hLip hR t ht d hd hSep
    rw [hWitness]
    exact hExact
  have hGap' (x y : Space) (hgy : g y≠0) (hfx : f x≠0) : d≤‖x-y‖ :=
    by simpa only [norm_sub_rev y x] using hGap y x hfx hgy
  have hAdj :
      inner ℂ (P g) (f.toLp 2 volume) =
        ∫ p : Space × Space, conj (g p.1)*(adjointKernel Q p.1 p.2*f p.2) ∂μ := by
    rw [← inner_conj_symm (𝕜 := ℂ) (P g) (f.toLp 2 volume),hPair g f hGap',← integral_conj]
    calc
      _ = ∫ p : Space × Space, conj (conj (f p.2)*(Q p.2 p.1*g p.1)) ∂μ :=
        (integral_prod_swap (μ := (volume : Measure Space)) (ν := (volume : Measure Space))
          (fun p : Space × Space => conj (conj (f p.1)*(Q p.1 p.2*g p.2)))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with p
        simp [adjointKernel,map_mul,mul_comm,mul_left_comm]
  let W (J : Space → Space → ℂ) (p : Space × Space) := conj (g p.1)*(J p.1 p.2*f p.2)
  have hWT : Integrable (W T) μ := integrable_separated_kernel_pair hT f g d hd hGap
  have hWQ : Integrable (W Q) μ := integrable_separated_kernel_pair hQ f g d hd hGap
  have hWA : Integrable (W (adjointKernel Q)) μ := integrable_separated_kernel_pair hQ.adjoint f g d hd hGap
  have hWsub : Integrable (fun p : Space × Space => W T p-W Q p) μ := hWT.sub hWQ
  unfold canceledCoefficientPair
  rw [actualCoefficientCommutator_separated_pair_eq_kernel ha hCont r f g L U hLip hR hf d hd hGap,
    hPair f g hGap,hAdj]
  change (∫ p, W T p ∂μ)-(∫ p, W Q p ∂μ)+(∫ p, W (adjointKernel Q) p ∂μ) = ∫ p, W K p ∂μ
  rw [← integral_sub hWT hWQ,← integral_add hWsub hWA]
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [W,K,canceledCoefficientKernel,T,Q,b]
  ring

end Burnett.Analysis.CarlesonEmbedding
