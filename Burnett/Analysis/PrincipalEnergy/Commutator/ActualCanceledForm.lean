import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualInputCutoffLimit
import Burnett.Analysis.PrincipalEnergy.Paraproduct.AdjointCutoffLimit
import Burnett.Analysis.PrincipalEnergy.Quantization.FullConstantDistribution
import Burnett.Analysis.PrincipalEnergy.Quantization.FormalCommutatorAdjoint

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped NNReal Topology ComplexConjugate InnerProductSpace

/-- The paraproduct corrections to the actual skew commutator, with the
adjoint represented by the exchanged Hilbert-space pairing. -/
def canceledCoefficientPair (a : Space → Space → ℂ) (r : SchwartzMap Space ℂ)
    (P : SchwartzMap Space ℂ → ComplexL2 Space) (f g : SchwartzMap Space ℂ) : ℂ :=
  (∫ x, conj (g x)*actualCoefficientCommutator a r f x)-
    inner ℂ (g.toLp 2 volume) (P f)+inner ℂ (P g) (f.toLp 2 volume)

theorem canceledCoefficientPair_formal_skew {a : Space → Space → ℂ}
    (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (hSym : FirstOrderFormalSymmetry a) (r : SchwartzMap Space ℂ) (hReal : ∀ x, conj (r x)=r x)
    (P : SchwartzMap Space ℂ → ComplexL2 Space) (f g : SchwartzMap Space ℂ) :
    canceledCoefficientPair a r P g f = -conj (canceledCoefficientPair a r P f g) := by
  have hConj :
      (∫ x, conj (actualCoefficientCommutator a r f x)*g x) =
        conj (∫ x, conj (g x)*actualCoefficientCommutator a r f x) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    simp [map_mul,mul_comm]
  unfold canceledCoefficientPair
  rw [actualCoefficientCommutator_formal_skew hBase hCont hSym r hReal f g,hConj,
    map_add,map_sub,inner_conj_symm,inner_conj_symm]
  ring

/-- The physical L² paraproduct realizes both cancellations of the
remainder of the original compact-base scalar commutator. -/
theorem exists_compactBase_canceledCoefficientPair
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (hSym : FirstOrderFormalSymmetry a)
    (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (hφ₁ : (∫ z, φ z)=1) (hψ₀ : (∫ z, ψ z)=0) (hθ₀ : (∫ z, θ z)=0)
    (hFac : WaveletFactorization φ ψ θ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0≤U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x)=r x) →
      LipschitzWith L r → (∀ x, ‖r x‖≤U) → ∀ (t : ℝ), 0<t →
      let b := coefficientCommutatorConstant a r
      ∃ P : SchwartzMap Space ℂ → ComplexL2 Space,
        (∀ f : SchwartzMap Space ℂ,
          let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
          ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
            let v (j : ℤ) := (hTerm j).toLp (T j)
            Summable v ∧ P f=(∑' j, v j) ∧ ‖P f‖≤C*(U+(L:ℝ))*‖f.toLp 2 volume‖) ∧
        (∀ (χ g : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)),
          (∀ x : Space, ‖x‖≤1 → χ x=1) →
          Tendsto (fun n => canceledCoefficientPair a r P (expandingTestSchwartz χ hχ n) g) atTop (𝓝 0) ∧
          Tendsto (fun n => canceledCoefficientPair a r P g (expandingTestSchwartz χ hχ n)) atTop (𝓝 0)) := by
  obtain ⟨C,hC,hAll⟩ := exists_compactBase_bilateral_two_window_paraproduct ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀
  refine ⟨C,hC,?_⟩
  intro r L U hU hr hReal hLip hR t ht b
  let T (f : SchwartzMap Space ℂ) (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
  let hTerm (f : SchwartzMap Space ℂ) := Classical.choose (hAll r f L U hU hLip hR t ht)
  let P (f : SchwartzMap Space ℂ) : ComplexL2 Space := ∑' j, (hTerm f j).toLp (T f j)
  refine ⟨P,?_,?_⟩
  · intro f
    have h := Classical.choose_spec (hAll r f L U hU hLip hR t ht)
    exact ⟨hTerm f,h.1,rfl,h.2.1⟩
  intro χ g hχ hχ₁
  let F := expandingTestSchwartz χ hχ
  obtain ⟨hB,_,_,hInput⟩ := exists_compactBase_bilateral_paraproduct_input_expanding_tendsto
    ha hBase hCont φ ψ θ hφ hψ hφ₁ hψ₀ hθ₀ hFac r χ hχ hχ₁ L U hU hLip hR t ht
  have hP : Tendsto (fun n => P (F n)) atTop (𝓝 (hB.toLp b)) := hInput
  have hP₁ : inner ℂ (g.toLp 2 volume) (hB.toLp b) = ∫ x, conj (g x)*b x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume,MemLp.coeFn_toLp hB] with x hg hb
    rw [hg,hb,RCLike.inner_apply']
  have hInner : Continuous (fun u : ComplexL2 Space => inner ℂ (g.toLp 2 volume) u) :=
    continuous_const.inner continuous_id
  have hOne : Tendsto (fun n => inner ℂ (g.toLp 2 volume) (P (F n))) atTop
      (𝓝 (∫ x, conj (g x)*b x)) := by
    rw [← hP₁]
    exact hInner.continuousAt.tendsto.comp hP
  obtain ⟨_,_,hAdj⟩ := exists_compactBase_bilateral_paraproduct_adjoint_expanding_test_tendsto
    ha hBase hCont φ ψ θ hφ hψ hψ₀ hθ₀ r g χ hχ₁ L U hU hLip hR t ht
  have hP₂ (n : ℕ) : inner ℂ (P g) ((F n).toLp 2 volume) =
      ∫ x, conj ((P g) x)*expandingInput χ ((n:ℝ)+1) x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(F n).coeFn_toLp 2 volume] with x hx
    rw [hx,RCLike.inner_apply',expandingTestSchwartz_apply]
  have hTwo : Tendsto (fun n => inner ℂ (P g) ((F n).toLp 2 volume)) atTop (𝓝 0) :=
    hAdj.congr fun n => (hP₂ n).symm
  have hOrig := coefficientCommutator_expandingInput_tested ha.frequency hBase hCont r χ g hr hχ hχ₁
  have hF (n : ℕ) : (F n : Space → ℂ) = expandingInput χ ((n:ℝ)+1) := rfl
  have hProd (n : ℕ) :
      (scalarSchwartzProduct r (F n) : Space → ℂ) =
        fun y => r y*expandingInput χ ((n:ℝ)+1) y := by
    funext y
    rw [scalarSchwartzProduct_apply]
    rfl
  have hMain : Tendsto (fun n => ∫ x, conj (g x)*actualCoefficientCommutator a r (F n) x)
      atTop (𝓝 (∫ x, conj (g x)*b x)) := by
    simp_rw [actualCoefficientCommutator,hF,hProd]
    exact hOrig
  have hCancel : Tendsto (fun n => canceledCoefficientPair a r P (F n) g) atTop (𝓝 0) := by
    simpa only [canceledCoefficientPair,sub_self,zero_add] using (hMain.sub hOne).add hTwo
  refine ⟨hCancel,?_⟩
  have hConj := (Complex.continuous_conj.continuousAt.tendsto.comp hCancel).neg
  rw [map_zero,neg_zero] at hConj
  exact hConj.congr fun n => (canceledCoefficientPair_formal_skew hBase hCont hSym r hReal P (F n) g).symm

end Burnett.Analysis.CarlesonEmbedding
