import Burnett.Analysis.PrincipalEnergy.Commutator.RealWindowCanceledKernel
import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairLinearity
import Burnett.Analysis.PrincipalEnergy.Commutator.NearWaveletPair

set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate NNReal

/-- Both bounds apply to one physical canceled form for every coefficient.
The window, symbol, and form constants are fixed before its scale tests. -/
theorem exists_compactBase_realWindow_canceledCoefficientPair_wavelet_bounds :
    ∃ φ ψ θ : SchwartzMap Space ℂ,
      (∫ x, φ x)=1 ∧ (∀ x, 1/2<‖x‖ → φ x=0) ∧
      (∀ x, conj (φ x)=φ x ∧ conj (ψ x)=ψ x ∧ conj (θ x)=θ x) ∧
      (∫ x, ψ x)=0 ∧ (∀ x, 1<‖x‖ → ψ x=0) ∧
      (∫ x, θ x)=0 ∧ ∃ hθ : ∀ x, 1<‖x‖ → θ x=0,
      WaveletFactorization φ ψ θ ∧
      ∀ {a : Space → Space → ℂ}, FirstBaseFrequencyOrderOne a → CompactBaseOrderOne a →
        Continuous (Function.uncurry a) → FirstOrderFormalSymmetry a →
        ∃ M A B : ℝ, 0≤M ∧ 0≤A ∧ 0≤B ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
          HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x)=r x) →
          (∀ᵐ x ∂(volume : Measure Space), ‖r x‖≤U) →
          (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖≤(L:ℝ)) →
          ∀ (t₀ : ℝ), 0<t₀ →
          ∃ P : SchwartzMap Space ℂ → ComplexL2 Space,
            let R := canceledCoefficientPair a r P
            (∀ f : SchwartzMap Space ℂ, ‖P f‖≤M*(U+(L:ℝ))*‖f.toLp 2 volume‖) ∧
            (∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g) ∧
            (∀ f g : SchwartzMap Space ℂ, R g f= -conj (R f g)) ∧
            (∀ s t : ℝ, ∀ (hs : 0<s) (ht : 0<t), s≤t →
              (∀ x y : Space,
                ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet θ hθ s hs x)‖≤
                  (A*(U+(L:ℝ)))*Real.sqrt (s/t)*(t^4)⁻¹) ∧
              (∀ x y : Space, 4*t≤‖x-y‖ →
                ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet θ hθ s hs x)‖≤
                  (B*(U+(L:ℝ)))*s*(‖x-y‖^5)⁻¹)) := by
  obtain ⟨φ,φHalf,ψ,θ,hφ,hφs,hHalf,hReal,hψ,hψs,hθ,hθs,hFac,_,hActual⟩ :=
    exists_compactBase_realWindow_canceledCoefficientPair_with_kernel
  have hReal' (x : Space) : conj (φ x)=φ x ∧ conj (ψ x)=ψ x ∧ conj (θ x)=θ x :=
    ⟨(hReal x).1,(hReal x).2.2⟩
  refine ⟨φ,ψ,θ,hφ,hφs,hReal',hψ,hψs,hθ,hθs,hFac,?_⟩
  obtain ⟨S₁,S₂,hS₁,hS₂,hNear⟩ := centeredWaveletPair_near_bound θ θ hθs hθs hθ
  let V := ∫ z : Space, ‖θ z‖
  have hV : 0≤V := integral_nonneg fun _ => norm_nonneg _
  intro a ha hBase hCont hSym
  obtain ⟨M,C,W,hM,hC,hW,hResult⟩ := hActual ha hBase hCont hSym
  refine ⟨M,W*S₁+C*S₂,32*C*V^2,hM,by positivity,by positivity,?_⟩
  intro r L U hr hR hUae hL t₀ hT
  obtain ⟨P,hSeries,hCancel,hSkew,hWeak,hKernel,hPair⟩ := hResult r L U hr hR hUae hL t₀ hT
  let R := canceledCoefficientPair a r P
  have hP (f : SchwartzMap Space ℂ) : ‖P f‖≤M*(U+(L:ℝ))*‖f.toLp 2 volume‖ := by
    obtain ⟨_,_,_,h⟩ := hSeries f
    exact h
  have hPL (f g : SchwartzMap Space ℂ) (c : ℂ) : P (f-c • g)=P f-c • P g := by
    refine compactWaveletParaproduct_sub_smul φ ψ θ
      (coefficientCommutatorConstant_integrable ha.frequency hBase hCont r) t₀ hT P ?_ f g c
    intro v
    obtain ⟨hMem,hSum,hEq,_⟩ := hSeries v
    exact ⟨hMem,hSum,hEq⟩
  have hRL (f u g : SchwartzMap Space ℂ) (c : ℂ) : R (f-c • u) g=R f g-c*R u g :=
    canceledCoefficientPair_sub_smul ha.frequency hBase hCont r P hPL f u g c
  obtain ⟨hU,_,_⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hUae hL
  have hWC : 0≤W*(U+(L:ℝ)) := by positivity
  refine ⟨P,hP,hRL,hSkew,?_⟩
  intro s t hs ht hst
  constructor
  · intro x y
    have h := hNear hKernel hWC R hPair hRL hSkew hWeak
      (fun χ g hχ hχ₁ => (hCancel χ g hχ hχ₁).1) s t hs ht hst x y
    exact h.trans_eq (by ring)
  · intro x y hDist
    have h := centeredWaveletPair_far_bound hKernel R hPair θ θ hθs hθs hθ s t hs ht hst x y hDist
    exact h.trans_eq (by dsimp only [V]; ring)

end Burnett.Analysis.CarlesonEmbedding
