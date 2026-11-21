import Burnett.Analysis.AngularCaps.NullScreenBasis

set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set
open scoped BigOperators

private def firstNullCoordinate : NullFrequencyCoordinates →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ (ℝ × NullScreenSpace)

private def secondNullCoordinate : NullFrequencyCoordinates →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ NullScreenSpace).comp (LinearMap.snd ℝ ℝ (ℝ × NullScreenSpace))

private def screenCoordinate (j : Fin 2) : NullFrequencyCoordinates →ₗ[ℝ] ℝ :=
  (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).comp
    ((LinearMap.snd ℝ ℝ NullScreenSpace).comp (LinearMap.snd ℝ ℝ (ℝ × NullScreenSpace)))

private def assembleNullCoordinates {m : Form} {w n : Vec} (e : NullScreenAxes m w n) :
    NullFrequencyCoordinates →ₗ[ℝ] Vec :=
  firstNullCoordinate.smulRight w + secondNullCoordinate.smulRight n +
    (screenCoordinate 0).smulRight e.first + (screenCoordinate 1).smulRight e.second

private theorem assembleNullCoordinates_apply {m : Form} {w n : Vec} (e : NullScreenAxes m w n)
    (u : NullFrequencyCoordinates) :
    assembleNullCoordinates e u = u.1 • w + u.2.1 • n + u.2.2 0 • e.first + u.2.2 1 • e.second :=
  rfl

private def screenVector (a b : ℝ) : NullScreenSpace :=
  WithLp.toLp 2 ![a,b]

@[simp] private theorem screenVector_first (a b : ℝ) : screenVector a b 0 = a := rfl
@[simp] private theorem screenVector_second (a b : ℝ) : screenVector a b 1 = b := rfl

private theorem screenVector_norm_sq (a b : ℝ) : ‖screenVector a b‖^2 = a^2+b^2 := by
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
  simp only [screenVector_first,screenVector_second,Real.norm_eq_abs,sq_abs]

private def extractNullCoordinates {m : Form} {w n : Vec} (e : NullScreenAxes m w n)
    (x : Vec) : NullFrequencyCoordinates :=
  (-2*pairing m n x,-2*pairing m w x,screenVector (pairing m e.first x) (pairing m e.second x))

private theorem pair_against_assembled {m : Form} {w n : Vec} (e : NullScreenAxes m w n)
    (x : Vec) (u : NullFrequencyCoordinates) :
    pairing m x (assembleNullCoordinates e u) =
      u.1*pairing m x w + u.2.1*pairing m x n + u.2.2 0*pairing m x e.first +
        u.2.2 1*pairing m x e.second := by
  simp only [assembleNullCoordinates_apply,pairing_add_right,pairing_smul_right]

private theorem assembled_pairings {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n)
    (u : NullFrequencyCoordinates) :
    pairing m w (assembleNullCoordinates e u) = -u.2.1/2 ∧
    pairing m n (assembleNullCoordinates e u) = -u.1/2 ∧
    pairing m e.first (assembleNullCoordinates e u) = u.2.2 0 ∧
    pairing m e.second (assembleNullCoordinates e u) = u.2.2 1 := by
  have hWW : pairing m w w = 0 := hw.2
  have hNN : pairing m n n = 0 := hn.1
  have hNW : pairing m n w = -1/2 := (pairing_symm hSym n w).trans hn.2
  have hAA : pairing m e.first e.first = 1 := e.first_quadratic
  have hBB : pairing m e.second e.second = 1 := e.second_quadratic
  have hAW : pairing m e.first w = 0 := (pairing_symm hSym _ _).trans e.first_orthogonal.1
  have hAN : pairing m e.first n = 0 := (pairing_symm hSym _ _).trans e.first_orthogonal.2
  have hBW : pairing m e.second w = 0 := (pairing_symm hSym _ _).trans e.second_orthogonal.1
  have hBN : pairing m e.second n = 0 := (pairing_symm hSym _ _).trans e.second_orthogonal.2
  have hBA : pairing m e.second e.first = 0 := (pairing_symm hSym _ _).trans e.mixed_zero
  refine ⟨?_,?_,?_,?_⟩
  · rw [pair_against_assembled,hWW,hn.2,e.first_orthogonal.1,e.second_orthogonal.1]
    ring
  · rw [pair_against_assembled,hNW,hNN,e.first_orthogonal.2,e.second_orthogonal.2]
    ring
  · simp only [pair_against_assembled,hAW,hAN,hAA,e.mixed_zero,mul_zero,mul_one,zero_add,add_zero]
  · simp only [pair_against_assembled,hBW,hBN,hBA,hBB,mul_zero,mul_one,zero_add]

private theorem extract_assemble {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n) :
    Function.LeftInverse (extractNullCoordinates e) (assembleNullCoordinates e) := by
  intro u
  obtain ⟨hW,hN,hA,hB⟩ := assembled_pairings hSym hw hn e u
  apply Prod.ext
  · change -2*pairing m n (assembleNullCoordinates e u) = _
    rw [hN]
    ring
  · apply Prod.ext
    · change -2*pairing m w (assembleNullCoordinates e u) = _
      rw [hW]
      ring
    · change screenVector (pairing m e.first (assembleNullCoordinates e u))
        (pairing m e.second (assembleNullCoordinates e u)) = _
      rw [hA,hB]
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl

private theorem assembled_quadratic {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n)
    (u : NullFrequencyCoordinates) :
    quadratic m (assembleNullCoordinates e u) = nullCoordinateQuadratic u := by
  obtain ⟨hW,hN,hA,hB⟩ := assembled_pairings hSym hw hn e u
  unfold quadratic
  conv_lhs => arg 2; rw [assembleNullCoordinates_apply]
  simp only [pairing_add_left,pairing_smul_left,hW,hN,hA,hB,nullCoordinateQuadratic]
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
  simp only [Real.norm_eq_abs,sq_abs]
  ring

/-- Construct the actual signed null coordinate chart. The factor `-1/2` in
the null-plane pairing gives the coefficient `-1` in front of `st`. -/
def constructNullCapChart {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n) :
    NullCapChart m w := by
  let L := assembleNullCoordinates e
  have hDim : Module.finrank ℝ NullFrequencyCoordinates = Module.finrank ℝ Vec := by
    norm_num [NullFrequencyCoordinates,NullScreenSpace,Module.finrank_prod,Module.finrank_self,
      finrank_euclideanSpace_fin]
  let F := (L.linearEquivOfInjective (extract_assemble hSym hw hn e).injective hDim).toContinuousLinearEquiv
  refine ⟨F,?_,assembled_quadratic hSym hw hn e⟩
  change assembleNullCoordinates e nullAxis = w
  simp [assembleNullCoordinates_apply,nullAxis]

private theorem constructNullCapChart_apply {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n)
    (u : NullFrequencyCoordinates) :
    (constructNullCapChart hSym hw hn e).toFrequency u = assembleNullCoordinates e u :=
  rfl

private theorem constructNullCapChart_symm_apply {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n) (x : Vec) :
    (constructNullCapChart hSym hw hn e).toFrequency.symm x = extractNullCoordinates e x := by
  let F := constructNullCapChart hSym hw hn e
  have h := extract_assemble hSym hw hn e (F.toFrequency.symm x)
  change extractNullCoordinates e (F.toFrequency (F.toFrequency.symm x)) = F.toFrequency.symm x at h
  rw [F.toFrequency.apply_symm_apply] at h
  exact h.symm

private theorem chart_forward_norm_bound {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n)
    {L E : ℝ} (hN : ‖n‖ ≤ L) (hA : ‖e.first‖ ≤ E) (hB : ‖e.second‖ ≤ E) :
    ‖(constructNullCapChart hSym hw hn e).toFrequency.toContinuousLinearMap‖ ≤ 1+L+2*E := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hN
  have hE : 0 ≤ E := (norm_nonneg _).trans hA
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖(constructNullCapChart hSym hw hn e).toFrequency u‖ ≤ _
  rw [constructNullCapChart_apply,assembleNullCoordinates_apply]
  have hs : |u.1| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le u
  have ht : |u.2.1| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using ((norm_fst_le u.2).trans (norm_snd_le u))
  have hz (i : Fin 2) : |u.2.2 i| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using
      ((PiLp.norm_apply_le u.2.2 i).trans ((norm_snd_le u.2).trans (norm_snd_le u)))
  let a := u.1 • w
  let b := u.2.1 • n
  let c := u.2.2 0 • e.first
  let d := u.2.2 1 • e.second
  change ‖a+b+c+d‖ ≤ _
  have hTri : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    have hab := norm_add_le a b
    have habc := (norm_add_le (a+b) c).trans (add_le_add_right hab ‖c‖)
    exact (norm_add_le (a+b+c) d).trans (add_le_add_right habc ‖d‖)
  have ha : ‖a‖ ≤ ‖u‖ := by simpa only [a,norm_smul,Real.norm_eq_abs,hw.1,mul_one] using hs
  have hb : ‖b‖ ≤ ‖u‖*L := by
    simpa only [b,norm_smul,Real.norm_eq_abs] using mul_le_mul ht hN (norm_nonneg n) (norm_nonneg u)
  have hc : ‖c‖ ≤ ‖u‖*E := by
    simpa only [c,norm_smul,Real.norm_eq_abs] using mul_le_mul (hz 0) hA (norm_nonneg _) (norm_nonneg u)
  have hd : ‖d‖ ≤ ‖u‖*E := by
    simpa only [d,norm_smul,Real.norm_eq_abs] using mul_le_mul (hz 1) hB (norm_nonneg _) (norm_nonneg u)
  linarith only [hTri,ha,hb,hc,hd]

private theorem screenVector_norm_le {a b M : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    ‖screenVector a b‖ ≤ 2*M := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg zero_le_two hM)).mp
  rw [screenVector_norm_sq]
  have hA := pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hB := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hA hB
  nlinarith only [hA,hB,sq_nonneg M]

private theorem chart_inverse_norm_bound {m : Form} (hSym : Symmetric m) {w n : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n) (e : NullScreenAxes m w n)
    {L E C : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hPair : ∀ x y : Vec, |pairing m x y| ≤ C*‖x‖*‖y‖)
    (hN : ‖n‖ ≤ L) (hA : ‖e.first‖ ≤ E) (hB : ‖e.second‖ ≤ E) :
    ‖(constructNullCapChart hSym hw hn e).toFrequency.symm.toContinuousLinearMap‖ ≤
      2*C*(1+L+E) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖(constructNullCapChart hSym hw hn e).toFrequency.symm x‖ ≤ _
  rw [constructNullCapChart_symm_apply,extractNullCoordinates,Prod.norm_def,Prod.norm_def,
    Real.norm_eq_abs,Real.norm_eq_abs]
  have hX := norm_nonneg x
  have hb (v : Vec) {M : ℝ} (hv : ‖v‖ ≤ M) : |pairing m v x| ≤ C*M*‖x‖ :=
    (hPair v x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) hX)
  have hnB : |(-2:ℝ)*pairing m n x| ≤ 2*(C*L*‖x‖) := by
    rw [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ) ≤ 2 from zero_le_two)]
    exact mul_le_mul_of_nonneg_left (hb n hN) zero_le_two
  have hwB : |(-2:ℝ)*pairing m w x| ≤ 2*(C*1*‖x‖) := by
    rw [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ) ≤ 2 from zero_le_two)]
    exact mul_le_mul_of_nonneg_left (hb w hw.1.le) zero_le_two
  have hc := screenVector_norm_le (mul_nonneg (mul_nonneg hC hE) hX) (hb e.first hA) (hb e.second hB)
  have hG (M : ℝ) (hM : M ≤ 1+L+E) : 2*(C*M*‖x‖) ≤ 2*C*(1+L+E)*‖x‖ := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (mul_nonneg zero_le_two hC)) hX
    linarith only [h]
  exact max_le (hnB.trans (hG L (by linarith only [hE])))
    (max_le (hwB.trans (hG 1 (by linarith only [hL,hE]))) (hc.trans (hG E (by linarith only [hL]))))

/-- Every true unit null center of each form in the compact Lorentz family
has an actual null chart with a common two-sided operator norm bound. -/
theorem exists_uniform_nullCapCharts {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (hND : ∀ m ∈ K, Nondegenerate m) :
    ∃ B : ℝ, 0 < B ∧ ∀ m ∈ K, ∀ w ∈ unitNull m,
      ∃ F : NullCapChart m w, ‖F.toFrequency.toContinuousLinearMap‖ ≤ B ∧
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B := by
  have hSym (m : Form) (hm : m ∈ K) : Symmetric m := (hFrame m hm).elim lorentzFrame_symm
  obtain ⟨L,hL,hAxis⟩ := exists_uniform_complementaryNullAxis hK hSym hND
  obtain ⟨ℓ,hℓ,hScreen⟩ := exists_uniform_unitScreen_quadratic_lower hK hFrame L
  obtain ⟨C,hC,hPair⟩ := exists_uniform_pairing_norm_bound hK
  let E := 1+1/ℓ
  have hE : 0 < E := by dsimp only [E]; positivity
  let B := max (1+L+2*E) (2*C*(1+L+E))
  have hB : 0 < B := (show 0 < 1+L+2*E by positivity).trans_le (le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro m hm w hw
  obtain ⟨n,hn,hN⟩ := hAxis m hm w hw
  obtain ⟨f⟩ := hFrame m hm
  obtain ⟨e⟩ := exists_nullScreenAxes f hw hn
  have hScreen' := hScreen m hm w hw n hn hN
  have hA : ‖e.first‖ ≤ E := norm_le_of_screen_unit_quadratic hℓ hScreen' e.first_orthogonal e.first_quadratic
  have hE₂ : ‖e.second‖ ≤ E := norm_le_of_screen_unit_quadratic hℓ hScreen' e.second_orthogonal e.second_quadratic
  refine ⟨constructNullCapChart (hSym m hm) hw hn e,?_,?_⟩
  · exact (chart_forward_norm_bound (hSym m hm) hw hn e hN hA hE₂).trans (le_max_left _ _)
  · exact (chart_inverse_norm_bound (hSym m hm) hw hn e hL.le hE.le hC.le
      (hPair m hm) hN hA hE₂).trans (le_max_right _ _)

end Burnett.Analysis.ProjectiveNullCaps
