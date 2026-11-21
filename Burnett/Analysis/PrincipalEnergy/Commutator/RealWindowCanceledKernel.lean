import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletFactorizationWitness
import Burnett.Analysis.PrincipalEnergy.Commutator.ActualCanceledKernel
import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledWeakTest

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ComplexConjugate NNReal Topology

/-- A single triple of the concrete real windows works for every admitted
compact-base scalar symbol and coefficient. The physical series, both
cancellations, normalized-ball test, and full kernel use the same P. -/
theorem exists_compactBase_realWindow_canceledCoefficientPair_with_kernel :
    ∃ φ φHalf ψ θ : SchwartzMap Space ℂ,
      (∫ x, φ x)=1 ∧ (∀ x, 1/2<‖x‖ → φ x=0) ∧
      (∀ x, φHalf x=compactWaveletKernel φ (1/2) x) ∧
      (∀ x, conj (φ x)=φ x ∧ conj (φHalf x)=φHalf x ∧ conj (ψ x)=ψ x ∧ conj (θ x)=θ x) ∧
      (∫ x, ψ x)=0 ∧ (∀ x, 1<‖x‖ → ψ x=0) ∧
      (∫ x, θ x)=0 ∧ (∀ x, 1<‖x‖ → θ x=0) ∧ WaveletFactorization φ ψ θ ∧
      (∀ (t : ℝ), 0<t → ∀ f : ComplexL2 Space,
        Tendsto (fun N => reproducingPartialAction ψ θ t N f) atTop (𝓝 f)) ∧
      ∀ {a : Space → Space → ℂ}, FirstBaseFrequencyOrderOne a → CompactBaseOrderOne a →
        Continuous (Function.uncurry a) → FirstOrderFormalSymmetry a →
        ∃ M C W : ℝ, 0≤M ∧ 0≤C ∧ 0≤W ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
          HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x)=r x) →
          (∀ᵐ x ∂(volume : Measure Space), ‖r x‖≤U) →
          (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖≤(L:ℝ)) →
          ∀ (t : ℝ), 0<t →
          let b := coefficientCommutatorConstant a r
          let K := canceledCoefficientKernel a r φ ψ θ t
          ∃ P : SchwartzMap Space ℂ → ComplexL2 Space,
            let R := canceledCoefficientPair a r P
            (∀ f : SchwartzMap Space ℂ,
              let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
              ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
                let v (j : ℤ) := (hTerm j).toLp (T j)
                Summable v ∧ P f=(∑' j, v j) ∧ ‖P f‖≤M*(U+(L:ℝ))*‖f.toLp 2 volume‖) ∧
            (∀ (χ g : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)),
              (∀ x : Space, ‖x‖≤1 → χ x=1) →
              Tendsto (fun n => R (expandingTestSchwartz χ hχ n) g) atTop (𝓝 0) ∧
              Tendsto (fun n => R g (expandingTestSchwartz χ hχ n)) atTop (𝓝 0)) ∧
            (∀ f g, R g f= -conj (R f g)) ∧
            (∀ (c : Space) (ρ : ℝ), 0<ρ → ∀ (f g : SchwartzMap Space ℂ),
              tsupport (f : Space → ℂ) ⊆ Metric.closedBall c ρ →
              tsupport (g : Space → ℂ) ⊆ Metric.closedBall c ρ →
              (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
              (∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖≤ρ⁻¹) →
              (∀ (j : Fin 4) x, ‖fderiv ℝ (⇑g) x (coordinateDirection j)‖≤ρ⁻¹) →
              ‖R f g‖≤W*(U+(L:ℝ))*ρ^4) ∧
            CalderonZygmundKernelBounds K (C*(U+(L:ℝ))) ∧
            (∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
              ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
              R f g = ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
                ∂((volume : Measure Space).prod volume)) := by
  obtain ⟨φ,φHalf,ψ,θ,hφ,hφs,hHalf,hReal,hψ,hψs,hθ,hθs,hFac⟩ :=
    exists_real_compact_wavelet_factorization
  refine ⟨φ,φHalf,ψ,θ,hφ,hφs,hHalf,hReal,hψ,hψs,hθ,hθs,hFac,?_,?_⟩
  · exact reproducing_windows_L2_tendsto φ ψ θ hφ hFac
  intro a ha hBase hCont hSym
  have hφUnit (z : Space) (hz : 1<‖z‖) : φ z=0 := hφs z (by linarith)
  obtain ⟨M,C,hM,hC,hCanceled⟩ := exists_compactBase_canceledCoefficientPair_with_kernel
    ha hBase hCont hSym φ ψ θ hφUnit hψs hθs hφ hψ hθ hFac
  obtain ⟨W,hW,hWeak⟩ :=
    exists_canceledCoefficientPair_normalizedBall_weakBound ha.frequency hBase hCont hSym M hM
  refine ⟨M,C,W,hM,hC,hW,?_⟩
  intro r L U hr hrReal hUae hLae t ht b K
  obtain ⟨P,hSeries,hTests,hKernel,hPair⟩ := hCanceled r L U hr hrReal hUae hLae t ht
  obtain ⟨hU,hR,hLip⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hUae hLae
  refine ⟨P,hSeries,hTests,canceledCoefficientPair_formal_skew hBase hCont hSym r hrReal P,?_,hKernel,hPair⟩
  apply hWeak r L U hU hrReal hLip hR P
  intro f
  obtain ⟨_,_,_,hBound⟩ := hSeries f
  exact hBound

end Burnett.Analysis.CarlesonEmbedding
