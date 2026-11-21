import Burnett.Analysis.PrincipalEnergy.Commutator.ActualWaveletPairBounds
import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairH1Bound
import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletRemainderSummation

set_option autoImplicit false
set_option maxHeartbeats 5400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate InnerProductSpace NNReal

/-- For compact-base scalar symbols, the source commutator has a true
Schwartz-pair \(L^2\) bound controlled by the coefficient and its real
first derivative in essential supremum. -/
theorem exists_compactBase_coefficientCommutator_L2_pair_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (hSym : FirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x)=r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖≤U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖≤(L:ℝ)) →
      ∀ f g : SchwartzMap Space ℂ,
        ‖∫ x, conj (g x)*actualCoefficientCommutator a r f x‖≤
          C*(U+(L:ℝ))*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  obtain ⟨φ,ψ,θ,hφ,_,_,hψ,_,_,hθ,hFac,hActual⟩ :=
    exists_compactBase_realWindow_canceledCoefficientPair_wavelet_bounds
  obtain ⟨S,hS,hSum⟩ := exists_wavelet_remainder_L2_pair_bound φ ψ θ hφ hψ hθ hFac
  obtain ⟨M,A,B,hM,hA,hB,hActual⟩ := hActual ha hBase hCont hSym
  obtain ⟨D,hD,hH1⟩ := exists_canceledCoefficientPair_H1_bound ha.frequency hBase hCont hSym M hM
  let V := ∫ z : Space, waveletNearCutoff 1 z
  let J := ∫ z : Space, inverseFifthTail 1 z
  have hV : 0≤V := by
    apply integral_nonneg
    intro z
    change (0:ℝ)≤waveletNearCutoff 1 z
    by_cases hz : z ∈ Metric.closedBall (0:Space) (4*1)
    · simpa only [waveletNearCutoff,Set.indicator_of_mem hz] using (zero_le_one : (0:ℝ)≤1)
    · simpa only [waveletNearCutoff,Set.indicator_of_notMem hz] using (le_rfl : (0:ℝ)≤0)
  have hJ : 0≤J := integral_nonneg (inverseFifthTail_nonneg 1)
  refine ⟨S*(A*V+B*J/4)+2*M,by positivity,?_⟩
  intro r L U hr hReal hUae hLae f g
  obtain ⟨hU,hR,_⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hUae hLae
  obtain ⟨P,hP,hLin,hSkew,hPacket⟩ := hActual r L U hr hReal hUae hLae 1 zero_lt_one
  let R := canceledCoefficientPair a r P
  let Q := U+(L:ℝ)
  have hQ : 0≤Q := add_nonneg hU L.coe_nonneg
  have hFull := hH1 r U L hU L.coe_nonneg hReal hR P hP
  have hRBound := hSum R hLin hSkew (D*Q) (mul_nonneg hD hQ) hFull
    (A*Q) (B*Q) (mul_nonneg hA hQ) (mul_nonneg hB hQ) hPacket 1 zero_lt_one f g
  let X := ⟪g.toLp 2 volume,P f⟫_ℂ
  let Y := ⟪P g,f.toLp 2 volume⟫_ℂ
  have hX : ‖X‖≤M*Q*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
    calc
      _ ≤ ‖g.toLp 2 volume‖*‖P f‖ := norm_inner_le_norm _ _
      _ ≤ ‖g.toLp 2 volume‖*(M*Q*‖f.toLp 2 volume‖) := mul_le_mul_of_nonneg_left (hP f) (norm_nonneg _)
      _ = _ := by ring
  have hY : ‖Y‖≤M*Q*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
    calc
      _ ≤ ‖P g‖*‖f.toLp 2 volume‖ := norm_inner_le_norm _ _
      _ ≤ (M*Q*‖g.toLp 2 volume‖)*‖f.toLp 2 volume‖ := mul_le_mul_of_nonneg_right (hP g) (norm_nonneg _)
      _ = _ := by ring
  have hT : (∫ x, conj (g x)*actualCoefficientCommutator a r f x)=R f g+X-Y := by
    dsimp only [R,X,Y,canceledCoefficientPair]
    ring
  rw [hT]
  calc
    _ ≤ ‖R f g‖+‖X‖+‖Y‖ := (norm_sub_le _ _).trans
      (add_le_add_right (norm_add_le _ _) _)
    _ ≤ S*(A*Q*V+B*Q*J/4)*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖+
        M*Q*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖+M*Q*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ :=
      add_le_add (add_le_add hRBound hX) hY
    _ = _ := by dsimp only [Q]; ring

/-- The actual full Fourier commutator returns an \(L^2\) function, and its
norm bound holds on every Schwartz input with the same coefficient controls. -/
theorem exists_compactBase_coefficientCommutator_L2_action_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (hSym : FirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x)=r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖≤U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖≤(L:ℝ)) →
      ∀ f : SchwartzMap Space ℂ,
        ∃ hT : MemLp (actualCoefficientCommutator a r f) 2 volume,
          ‖hT.toLp (actualCoefficientCommutator a r f)‖≤C*(U+(L:ℝ))*‖f.toLp 2 volume‖ := by
  obtain ⟨C,hC,hPair⟩ := exists_compactBase_coefficientCommutator_L2_pair_bound ha hBase hCont hSym
  obtain ⟨_,_,hMap⟩ := exists_compactBase_firstOrderAction_h1_to_l2 hBase hCont
  refine ⟨C,hC,?_⟩
  intro r L U hr hReal hUae hLae f
  obtain ⟨hU,_,_⟩ := smoothCoefficient_bounds_of_ae_norm_firstDerivative r (r.smooth 1) U L hUae hLae
  obtain ⟨hF,_⟩ := hMap f
  obtain ⟨hProd,_⟩ := hMap (scalarSchwartzProduct r f)
  have hT : MemLp (actualCoefficientCommutator a r f) 2 volume :=
    (hF.mul' (r.memLp_top volume)).sub hProd
  refine ⟨hT,?_⟩
  let T : ComplexL2 Space := hT.toLp (actualCoefficientCommutator a r f)
  let D := C*(U+(L:ℝ))*‖f.toLp 2 volume‖
  have hD : 0≤D := by dsimp only [D]; positivity
  have hAll (v : ComplexL2 Space) : ‖⟪v,T⟫_ℂ‖≤D*‖v‖ := by
    apply (schwartz_toLp_denseRange (V := Space)).induction_on (p := fun v => ‖⟪v,T⟫_ℂ‖≤D*‖v‖) v
    · exact isClosed_le (continuous_id.inner continuous_const).norm (continuous_const.mul continuous_norm)
    · intro g
      have hEq : ⟪g.toLp 2 volume,T⟫_ℂ=∫ x, conj (g x)*actualCoefficientCommutator a r f x := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [g.coeFn_toLp 2 volume,MemLp.coeFn_toLp hT] with x hg hu
        change inner ℂ ((g.toLp 2 volume) x) ((hT.toLp _) x)=_
        rw [hg,hu,RCLike.inner_apply']
      change ‖⟪g.toLp 2 volume,T⟫_ℂ‖≤_
      rw [hEq]
      exact hPair r L U hr hReal hUae hLae f g
  have h := hAll T
  rw [inner_self_eq_norm_sq_to_K,norm_pow] at h
  change ‖((‖T‖:ℝ):ℂ)‖^2≤D*‖T‖ at h
  rw [Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),pow_two] at h
  change ‖T‖≤D
  by_cases hz : ‖T‖=0
  · rw [hz]
    exact hD
  · have hPos : 0<‖T‖ := lt_of_le_of_ne (norm_nonneg T) (fun he => hz he.symm)
    exact (mul_le_mul_iff_left₀ hPos).mp h

end Burnett.Analysis.CarlesonEmbedding
