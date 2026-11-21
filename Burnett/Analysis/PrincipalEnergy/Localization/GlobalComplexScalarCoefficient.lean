import Burnett.Analysis.PrincipalEnergy.Localization.GlobalSmoothCoefficientL2

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff NNReal

/-- The actual scalar commutator for smooth multiplication on a compact
Schwartz input. -/
def smoothCoefficientCommutator (a : Space → Space → ℂ)
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (f : SchwartzMap Space ℂ)
    (hf : HasCompactSupport (f : Space → ℂ)) (x : Space) : ℂ :=
  r x * firstOrderAction a f x - firstOrderAction a (smoothScalarSchwartzProduct r hr f hf) x

private theorem exists_real_smoothCoefficientCommutator_global_L2_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : FirstOrderFormalSymmetry a) (hProper : ProperKernelRelation (firstOrderKernelRelation a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)),
        ∃ hT : MemLp (smoothCoefficientCommutator a r hr f hf) 2 volume,
          ‖hT.toLp (smoothCoefficientCommutator a r hr f hf)‖ ≤ C * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ := by
  let b (_ _ : Unit) := a
  have hB : MatrixFirstOrderFormalSymmetry b := by
    intro f g
    simpa only [matrixFirstOrderAction, Fintype.sum_unique, b] using hSym (g ()) (f ())
  obtain ⟨C, hC, hBound⟩ := exists_smoothMatrixCoefficientCommutator_global_L2_bound
    (fun (_ _ : Unit) => ha) (fun _ _ => hs) (fun _ _ => hb) hB (fun _ _ => hProper)
  refine ⟨C, hC, fun r hr L U hReal hVal hDer f hf => ?_⟩
  obtain ⟨hT, hTbound⟩ := hBound r hr L U hReal hVal hDer (fun _ => f) (fun _ => hf)
  have hEq : smoothMatrixCoefficientCommutator b r hr (fun _ => f) (fun _ => hf) () =
      smoothCoefficientCommutator a r hr f hf := by
    funext x
    simp only [smoothMatrixCoefficientCommutator, smoothCoefficientCommutator, matrixFirstOrderAction,
      Fintype.sum_unique, b]
  have hT' : MemLp (smoothCoefficientCommutator a r hr f hf) 2 volume := hEq ▸ hT ()
  refine ⟨hT', ?_⟩
  have hLp : hT'.toLp (smoothCoefficientCommutator a r hr f hf) =
      (hT ()).toLp (smoothMatrixCoefficientCommutator b r hr (fun _ => f) (fun _ => hf) ()) :=
    MemLp.toLp_congr hT' (hT ()) (EventuallyEq.of_eq hEq.symm)
  have hInput : matrixSchwartzL2Norm (fun _ : Unit => f) = ‖f.toLp 2 volume‖ := by
    unfold matrixSchwartzL2Norm
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fintype.sum_unique, PiLp.toLp_apply]
  rw [hLp, ← hInput]
  exact (PiLp.norm_apply_le (WithLp.toLp 2
    (fun i => (hT i).toLp (smoothMatrixCoefficientCommutator b r hr (fun _ => f) (fun _ => hf) i))) ()).trans hTbound

private theorem projected_smoothCoefficient_controls (Q : ℂ →L[ℝ] ℂ) (hQ : ‖Q‖ ≤ 1)
    (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ)
    (hU : ∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U)
    (hL : ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) :
    (∀ᵐ x ∂(volume : Measure Space), ‖Q (r x)‖ ≤ U) ∧
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (Q ∘ r) x‖ ≤ (L : ℝ)) := by
  constructor
  · filter_upwards [hU] with x hx
    exact ((Q.le_opNorm (r x)).trans (mul_le_of_le_one_left (norm_nonneg _) hQ)).trans hx
  · filter_upwards [hL] with x hx
    have hd : fderiv ℝ (Q ∘ r) x = Q.comp (fderiv ℝ r x) :=
      (Q.hasFDerivAt.comp x (((hr.differentiable (by simp)) x).hasFDerivAt)).fderiv
    rw [hd]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hQ)).trans hx

/-- Full scalar complex multiplication in the original physical commutator,
with the original coefficient and derivative controls. -/
theorem exists_complex_smoothCoefficientCommutator_global_L2_bound
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : FirstOrderFormalSymmetry a) (hProper : ProperKernelRelation (firstOrderKernelRelation a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Space → ℂ) (hr : ContDiff ℝ ∞ r) (L : NNReal) (U : ℝ),
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ r x‖ ≤ (L : ℝ)) →
      ∀ (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)),
        ∃ hT : MemLp (smoothCoefficientCommutator a r hr f hf) 2 volume,
          ‖hT.toLp (smoothCoefficientCommutator a r hr f hf)‖ ≤ C * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ := by
  obtain ⟨C, hC, hBound⟩ := exists_real_smoothCoefficientCommutator_global_L2_bound ha hs hb hSym hProper
  refine ⟨2*C, by positivity, fun r hr L U hU hL f hf => ?_⟩
  let Q := Complex.ofRealCLM.comp Complex.reCLM
  let P := Complex.ofRealCLM.comp Complex.imCLM
  have hQ : ‖Q‖ ≤ 1 := Q.opNorm_le_bound zero_le_one fun z => by
    change ‖(z.re : ℂ)‖ ≤ 1 * ‖z‖
    rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact Complex.abs_re_le_norm z
  have hP : ‖P‖ ≤ 1 := P.opNorm_le_bound zero_le_one fun z => by
    change ‖(z.im : ℂ)‖ ≤ 1 * ‖z‖
    rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact Complex.abs_im_le_norm z
  let u : Space → ℂ := Q ∘ r
  let v : Space → ℂ := P ∘ r
  have hu : ContDiff ℝ ∞ u := Q.contDiff.comp hr
  have hv : ContDiff ℝ ∞ v := P.contDiff.comp hr
  obtain ⟨hu₀, hu₁⟩ := projected_smoothCoefficient_controls Q hQ r hr L U hU hL
  obtain ⟨hv₀, hv₁⟩ := projected_smoothCoefficient_controls P hP r hr L U hU hL
  obtain ⟨hA, hAest⟩ := hBound u hu L U (fun _ => Complex.conj_ofReal _) hu₀ hu₁ f hf
  obtain ⟨hB, hBest⟩ := hBound v hv L U (fun _ => Complex.conj_ofReal _) hv₀ hv₁ f hf
  let A := smoothCoefficientCommutator a u hu f hf
  let B := smoothCoefficientCommutator a v hv f hf
  have split (x : Space) : r x = u x + Complex.I * v x := by
    change r x = ((r x).re : ℂ) + Complex.I * ((r x).im : ℂ)
    rw [mul_comm Complex.I, Complex.re_add_im]
  have pr : smoothScalarSchwartzProduct r hr f hf =
      smoothScalarSchwartzProduct u hu f hf - (-Complex.I) • smoothScalarSchwartzProduct v hv f hf := by
    ext x
    change r x * f x = u x * f x - (-Complex.I) * (v x * f x)
    rw [split]
    ring
  have hEq : smoothCoefficientCommutator a r hr f hf = A + Complex.I • B := by
    funext x
    simp only [smoothCoefficientCommutator, split, pr, firstOrderAction_sub_smul a ha.frequency, A, B,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hAB : MemLp (A + Complex.I • B) 2 volume := hA.add (hB.const_smul _)
  have hT : MemLp (smoothCoefficientCommutator a r hr f hf) 2 volume := hEq.symm ▸ hAB
  refine ⟨hT, ?_⟩
  have hFull : hT.toLp (smoothCoefficientCommutator a r hr f hf) =
      hA.toLp A + Complex.I • hB.toLp B := by
    calc
      _ = hAB.toLp (A + Complex.I • B) := MemLp.toLp_congr hT hAB (EventuallyEq.of_eq hEq)
      _ = _ := by
        change (hA.add (hB.const_smul Complex.I)).toLp (A + Complex.I • B) = _
        rw [MemLp.toLp_add hA (hB.const_smul Complex.I), MemLp.toLp_const_smul Complex.I hB]
  rw [hFull]
  calc
    _ ≤ ‖hA.toLp A‖ + ‖Complex.I • hB.toLp B‖ := norm_add_le _ _
    _ = ‖hA.toLp A‖ + ‖hB.toLp B‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ C * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ + C * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ :=
      add_le_add hAest hBest
    _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
