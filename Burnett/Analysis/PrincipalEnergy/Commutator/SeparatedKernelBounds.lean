import Burnett.Analysis.PrincipalEnergy.Commutator.ActualCanceledForm

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter
open scoped ComplexConjugate Topology

/-- The size and first differences away from the diagonal in dimension four. -/
structure CalderonZygmundKernelBounds (K : Space → Space → ℂ) (C : ℝ) : Prop where
  const_nonneg : 0≤C
  size : ∀ x y, x≠y → ‖K x y‖≤C*(‖x-y‖^4)⁻¹
  source : ∀ x y y', x≠y → ‖y-y'‖≤‖x-y‖/2 →
    ‖K x y-K x y'‖≤C*‖y-y'‖*(‖x-y‖^5)⁻¹
  target : ∀ x x' y, x≠y → ‖x-x'‖≤‖x-y‖/2 →
    ‖K x y-K x' y‖≤C*‖x-x'‖*(‖x-y‖^5)⁻¹

def adjointKernel (K : Space → Space → ℂ) (x y : Space) : ℂ := conj (K y x)

namespace CalderonZygmundKernelBounds

variable {K K' : Space → Space → ℂ} {C C' : ℝ}

theorem mono (h : CalderonZygmundKernelBounds K C) (hC : C≤C') :
    CalderonZygmundKernelBounds K C' := by
  refine ⟨h.const_nonneg.trans hC,?_,?_,?_⟩
  · intro x y hxy
    exact (h.size x y hxy).trans (mul_le_mul_of_nonneg_right hC (by positivity))
  · intro x y y' hxy hd
    exact (h.source x y y' hxy hd).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (norm_nonneg _)) (by positivity))
  · intro x x' y hxy hd
    exact (h.target x x' y hxy hd).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (norm_nonneg _)) (by positivity))

theorem add (h : CalderonZygmundKernelBounds K C) (h' : CalderonZygmundKernelBounds K' C') :
    CalderonZygmundKernelBounds (fun x y => K x y+K' x y) (C+C') := by
  refine ⟨add_nonneg h.const_nonneg h'.const_nonneg,?_,?_,?_⟩
  · intro x y hxy
    exact (norm_add_le _ _).trans ((add_le_add (h.size x y hxy) (h'.size x y hxy)).trans_eq (by ring))
  · intro x y y' hxy hd
    change ‖K x y+K' x y-(K x y'+K' x y')‖≤_
    rw [show K x y+K' x y-(K x y'+K' x y')=(K x y-K x y')+(K' x y-K' x y') by ring]
    exact (norm_add_le _ _).trans ((add_le_add (h.source x y y' hxy hd) (h'.source x y y' hxy hd)).trans_eq (by ring))
  · intro x x' y hxy hd
    change ‖K x y+K' x y-(K x' y+K' x' y)‖≤_
    rw [show K x y+K' x y-(K x' y+K' x' y)=(K x y-K x' y)+(K' x y-K' x' y) by ring]
    exact (norm_add_le _ _).trans ((add_le_add (h.target x x' y hxy hd) (h'.target x x' y hxy hd)).trans_eq (by ring))

theorem neg (h : CalderonZygmundKernelBounds K C) :
    CalderonZygmundKernelBounds (fun x y => -K x y) C := by
  refine ⟨h.const_nonneg,?_,?_,?_⟩
  · intro x y hxy
    simpa only [norm_neg] using h.size x y hxy
  · intro x y y' hxy hd
    change ‖-K x y- -K x y'‖≤_
    rw [show -K x y- -K x y'= -(K x y-K x y') by ring,norm_neg]
    exact h.source x y y' hxy hd
  · intro x x' y hxy hd
    change ‖-K x y- -K x' y‖≤_
    rw [show -K x y- -K x' y= -(K x y-K x' y) by ring,norm_neg]
    exact h.target x x' y hxy hd

theorem adjoint (h : CalderonZygmundKernelBounds K C) :
    CalderonZygmundKernelBounds (adjointKernel K) C := by
  refine ⟨h.const_nonneg,?_,?_,?_⟩
  · intro x y hxy
    simpa only [adjointKernel,Complex.norm_conj,norm_sub_rev y x] using h.size y x hxy.symm
  · intro x y y' hxy hd
    have hd' : ‖y-y'‖≤‖y-x‖/2 := by simpa only [norm_sub_rev y x] using hd
    simpa only [adjointKernel,← map_sub,Complex.norm_conj,norm_sub_rev y x] using h.target y y' x hxy.symm hd'
  · intro x x' y hxy hd
    have hd' : ‖x-x'‖≤‖y-x‖/2 := by simpa only [norm_sub_rev y x] using hd
    simpa only [adjointKernel,← map_sub,Complex.norm_conj,norm_sub_rev y x] using h.source y x x' hxy.symm hd'

theorem continuousAt_offDiagonal (h : CalderonZygmundKernelBounds K C) (x y : Space) (hxy : x≠y) :
    ContinuousAt (Function.uncurry K) (x,y) := by
  let R := ‖x-y‖
  have hR : 0<R := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let A := C*(R^5)⁻¹
  let B := C*((R/2)^5)⁻¹
  have hA : 0≤A := mul_nonneg h.const_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))
  have hB : 0≤B := mul_nonneg h.const_nonneg (inv_nonneg.mpr (pow_nonneg (half_pos hR).le _))
  have hM : 0<A+B+1 := add_pos_of_nonneg_of_pos (add_nonneg hA hB) zero_lt_one
  refine Metric.continuousAt_iff.mpr fun ε hε => ?_
  refine ⟨min (R/4) (ε/(A+B+1)),lt_min (div_pos hR (by norm_num)) (div_pos hε hM),?_⟩
  intro p hp
  let d := ‖p-(x,y)‖
  have hd : d<min (R/4) (ε/(A+B+1)) := by simpa only [dist_eq_norm,d] using hp
  have hSmall : d<R/4 := hd.trans_le (min_le_left _ _)
  have hMoveX : ‖x-p.1‖≤d := by simpa only [norm_sub_rev x p.1] using norm_fst_le (p-(x,y))
  have hMoveY : ‖y-p.2‖≤d := by simpa only [norm_sub_rev y p.2] using norm_snd_le (p-(x,y))
  have hTri := norm_add_le (x-p.1) (p.1-y)
  rw [show x-p.1+(p.1-y)=x-y by abel] at hTri
  have hR' : R/2≤‖p.1-y‖ := by
    change R≤‖x-p.1‖+‖p.1-y‖ at hTri
    linarith
  have hPos' : 0<‖p.1-y‖ := (half_pos hR).trans_le hR'
  have hX := h.target x p.1 y hxy (show ‖x-p.1‖≤R/2 by linarith)
  have hY := h.source p.1 y p.2 (sub_ne_zero.mp (norm_pos_iff.mp hPos'))
    (show ‖y-p.2‖≤‖p.1-y‖/2 by linarith)
  have hInv : (‖p.1-y‖^5)⁻¹≤((R/2)^5)⁻¹ :=
    (inv_le_inv₀ (pow_pos hPos' _) (pow_pos (half_pos hR) _)).mpr
      (pow_le_pow_left₀ (half_pos hR).le hR' _)
  have hX' : ‖K x y-K p.1 y‖≤A*d :=
    hX.trans (((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMoveX h.const_nonneg) (by positivity)).trans_eq (by dsimp only [A,R]; ring)))
  have hY' : ‖K p.1 y-K p.1 p.2‖≤B*d := by
    refine hY.trans (mul_le_mul (mul_le_mul_of_nonneg_left hMoveY h.const_nonneg) hInv
      (by positivity) (mul_nonneg h.const_nonneg (norm_nonneg _)) |>.trans_eq ?_)
    dsimp only [B]
    ring
  have hSum := norm_add_le (K x y-K p.1 y) (K p.1 y-K p.1 p.2)
  rw [sub_add_sub_cancel] at hSum
  change dist (K p.1 p.2) (K x y)<ε
  rw [dist_eq_norm,norm_sub_rev]
  calc
    _ ≤ ‖K x y-K p.1 y‖+‖K p.1 y-K p.1 p.2‖ := hSum
    _ ≤ A*d+B*d := add_le_add hX' hY'
    _ = (A+B)*d := by ring
    _ ≤ (A+B+1)*d := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < ε := by rw [mul_comm]; exact (lt_div_iff₀ hM).mp (hd.trans_le (min_le_right _ _))

end CalderonZygmundKernelBounds

/-- A positive gap on the nonzero test factors gives the ordinary
integrable product-space kernel integrand, including its zero extension
near the diagonal. -/
theorem integrable_separated_kernel_pair {K : Space → Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds K C) (f g : SchwartzMap Space ℂ) (d : ℝ) (hd : 0<d)
    (hGap : ∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) :
    Integrable (fun p : Space × Space => conj (g p.1)*(K p.1 p.2*f p.2))
      ((volume : Measure Space).prod volume) := by
  let H (p : Space × Space) := conj (g p.1)*(K p.1 p.2*f p.2)
  have hZero (p : Space × Space) (hp : ‖p.1-p.2‖<d) : H p=0 := by
    by_cases hf : f p.2=0
    · simp [H,hf]
    have hg : g p.1=0 := by
      by_contra h
      exact (not_le_of_gt hp) (hGap _ _ hf h)
    simp [H,hg]
  have hCont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hp : p.1≠p.2
    · have hAt : ContinuousAt (Function.uncurry K) p := hK.continuousAt_offDiagonal p.1 p.2 hp
      exact (g.continuous.comp continuous_fst).star.continuousAt.mul
        (hAt.mul (f.continuous.comp continuous_snd).continuousAt)
    · have hSmall : ‖p.1-p.2‖<d := by rw [not_ne_iff.mp hp,sub_self,norm_zero]; exact hd
      have hOpen : IsOpen {q : Space × Space | ‖q.1-q.2‖<d} :=
        isOpen_lt (continuous_fst.sub continuous_snd).norm continuous_const
      have hx : ∀ᶠ q : Space × Space in 𝓝 p, ‖q.1-q.2‖<d := hOpen.mem_nhds hSmall
      change Tendsto H (𝓝 p) (𝓝 (H p))
      rw [hZero _ hSmall]
      exact tendsto_const_nhds.congr' (hx.mono fun q hq => (hZero q hq).symm)
  let D := C*(d^4)⁻¹
  have hDom : Integrable (fun p : Space × Space => D*(‖g p.1‖*‖f p.2‖))
      ((volume : Measure Space).prod volume) :=
    ((g.integrable (μ := (volume : Measure Space))).norm.mul_prod
      (f.integrable (μ := (volume : Measure Space))).norm).const_mul D
  refine hDom.mono' hCont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  change ‖H p‖≤D*(‖g p.1‖*‖f p.2‖)
  by_cases hf : f p.2=0
  · simp [H,hf]
  by_cases hg : g p.1=0
  · simp [H,hg]
  have hDist := hGap p.1 p.2 hf hg
  have hPos := hd.trans_le hDist
  have hInv : (‖p.1-p.2‖^4)⁻¹≤(d^4)⁻¹ :=
    (inv_le_inv₀ (pow_pos hPos _) (pow_pos hd _)).mpr (pow_le_pow_left₀ hd.le hDist _)
  have hSize := (hK.size p.1 p.2 (sub_ne_zero.mp (norm_pos_iff.mp hPos))).trans
      (mul_le_mul_of_nonneg_left hInv hK.const_nonneg)
  calc
    _ = ‖K p.1 p.2‖*(‖g p.1‖*‖f p.2‖) := by dsimp only [H]; rw [norm_mul,Complex.norm_conj,norm_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hSize (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end Burnett.Analysis.CarlesonEmbedding
