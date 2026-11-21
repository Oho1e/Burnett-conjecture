import Burnett.Analysis.PrincipalEnergy.Commutator.ActualCanceledForm

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate InnerProductSpace

private theorem compactWavelet_section_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ)
    {f : Space → ℂ} (hf : Integrable f volume) (x : Space) :
    Integrable (fun y => compactWaveletKernel ψ s (x-y)*f y) := by
  have hK : Continuous (fun y => compactWaveletKernel ψ s (x-y)) := by
    unfold compactWaveletKernel
    fun_prop
  exact hf.bdd_mul hK.aestronglyMeasurable
    ⟨|(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 ψ,fun y => by
      rw [compactWaveletKernel,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ ψ _) (abs_nonneg _)⟩

/-- Linearity under the actual convolution integral on integrable inputs. -/
theorem compactWaveletAction_sub_smul (ψ : SchwartzMap Space ℂ) (s : ℝ)
    {f g : Space → ℂ} (hf : Integrable f volume) (hg : Integrable g volume) (c : ℂ)
    (x : Space) :
    compactWaveletAction ψ s (fun y => f y-c*g y) x =
      compactWaveletAction ψ s f x-c*compactWaveletAction ψ s g x := by
  let K (y : Space) := compactWaveletKernel ψ s (x-y)
  change (∫ y, K y*(f y-c*g y))=(∫ y, K y*f y)-c*(∫ y, K y*g y)
  have hF : Integrable (fun y => K y*f y) := compactWavelet_section_integrable ψ s hf x
  have hG : Integrable (fun y => K y*g y) := compactWavelet_section_integrable ψ s hg x
  have hEq (y : Space) : K y*(f y-c*g y)=K y*f y-c*(K y*g y) := by ring
  simp_rw [hEq]
  rw [integral_sub hF (hG.const_mul c),integral_const_mul]

private theorem compactWaveletParaproductAtScale_sub_smul
    (φ ψ θ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    {b : Space → ℂ} (hb : Integrable b volume) (f g : SchwartzMap Space ℂ) (c : ℂ) :
    compactWaveletParaproductAtScale φ ψ θ s b (f-c • g) =
      fun x => compactWaveletParaproductAtScale φ ψ θ s b f x-
        c*compactWaveletParaproductAtScale φ ψ θ s b g x := by
  let B := compactWaveletAction ψ s b
  let G (w : SchwartzMap Space ℂ) (x : Space) := B x*compactWaveletAction φ s w x
  have hG (w : SchwartzMap Space ℂ) : Integrable (G w) volume := by
    have hB : Integrable B volume := compactWaveletAction_integrable ψ s hs hb
    have hw : Integrable (w : Space → ℂ) volume := w.integrable
    have hC := compactWaveletAction_continuous φ s hs w hw
    simpa only [G,mul_comm (B _)] using
      hB.bdd_mul hC.aestronglyMeasurable ⟨_,compactWaveletAction_norm_le_integral_norm φ s hw⟩
  have hEq : G (f-c • g)=fun x => G f x-c*G g x := by
    funext x
    change B x*compactWaveletAction φ s (f-c • g : SchwartzMap Space ℂ) x=_
    have h := compactWaveletAction_sub_smul φ s f.integrable g.integrable c x
    change B x*compactWaveletAction φ s (fun y => f y-c*g y) x=
      B x*compactWaveletAction φ s f x-c*(B x*compactWaveletAction φ s g x)
    rw [h]
    ring
  funext x
  change compactWaveletAction θ s (G (f-c • g)) x=
    compactWaveletAction θ s (G f) x-c*compactWaveletAction θ s (G g) x
  rw [hEq]
  exact compactWaveletAction_sub_smul θ s (hG f) (hG g) c x

/-- A map represented by the actual bilateral spatial series is complex linear
in the input. The identity is for exactly the same sum P. -/
theorem compactWaveletParaproduct_sub_smul
    (φ ψ θ : SchwartzMap Space ℂ) {b : Space → ℂ} (hb : Integrable b volume)
    (t : ℝ) (ht : 0<t)
    (P : SchwartzMap Space ℂ → ComplexL2 Space)
    (hSeries : ∀ f : SchwartzMap Space ℂ,
      let T (j : ℤ) := compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b f
      ∃ hTerm : ∀ j, MemLp (T j) 2 volume,
        let v (j : ℤ) := (hTerm j).toLp (T j)
        Summable v ∧ P f = ∑' j, v j)
    (f g : SchwartzMap Space ℂ) (c : ℂ) :
    P (f-c • g)=P f-c • P g := by
  let T (w : SchwartzMap Space ℂ) (j : ℤ) :=
    compactWaveletParaproductAtScale φ ψ θ (bilateralWaveletScale t j) b w
  obtain ⟨hf,hSf,hPf⟩ := hSeries f
  obtain ⟨hg,hSg,hPg⟩ := hSeries g
  obtain ⟨hd,_,hPd⟩ := hSeries (f-c • g)
  let F (j : ℤ) : ComplexL2 Space := (hf j).toLp (T f j)
  let G (j : ℤ) : ComplexL2 Space := (hg j).toLp (T g j)
  let D (j : ℤ) : ComplexL2 Space := (hd j).toLp (T (f-c • g) j)
  have hTerm (j : ℤ) : D j=F j-c • G j := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hd j),MemLp.coeFn_toLp (hf j),MemLp.coeFn_toLp (hg j),
      Lp.coeFn_sub (F j) (c • G j),Lp.coeFn_smul c (G j)] with x hDx hFx hGx hSub hMul
    rw [hSub]
    change D j x=F j x- (c • G j) x
    rw [hMul]
    change D j x=F j x-c • G j x
    change D j x=T (f-c • g) j x at hDx
    change F j x=T f j x at hFx
    change G j x=T g j x at hGx
    rw [hDx,hFx,hGx,smul_eq_mul]
    exact congrFun (compactWaveletParaproductAtScale_sub_smul φ ψ θ _
      (by simpa only [bilateralWaveletScale] using div_pos ht (by positivity : 0<(2:ℝ)^j)) hb f g c) x
  have hSF : Summable F := hSf
  have hSG : Summable G := hSg
  change P f=(∑' j, F j) at hPf
  change P g=(∑' j, G j) at hPg
  change P (f-c • g)=(∑' j, D j) at hPd
  rw [hPd,hPf,hPg]
  simp_rw [hTerm]
  rw [hSF.tsum_sub (hSG.const_smul c), hSG.tsum_const_smul c]

/-- The actual canceled commutator is linear in the first Schwartz test
for the same P that represents its physical paraproduct. -/
theorem canceledCoefficientPair_sub_smul
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (r : SchwartzMap Space ℂ)
    (P : SchwartzMap Space ℂ → ComplexL2 Space)
    (hP : ∀ (f g : SchwartzMap Space ℂ) (c : ℂ), P (f-c • g)=P f-c • P g)
    (f g h : SchwartzMap Space ℂ) (c : ℂ) :
    canceledCoefficientPair a r P (f-c • g) h=
      canceledCoefficientPair a r P f h-c*canceledCoefficientPair a r P g h := by
  have hProduct : scalarSchwartzProduct r (f-c • g)=
      scalarSchwartzProduct r f-c • scalarSchwartzProduct r g := by
    ext x
    simp only [scalarSchwartzProduct_apply,SchwartzMap.sub_apply,SchwartzMap.smul_apply,smul_eq_mul]
    ring
  have hT (x : Space) : actualCoefficientCommutator a r (f-c • g) x=
      actualCoefficientCommutator a r f x-c*actualCoefficientCommutator a r g x := by
    simp only [actualCoefficientCommutator,hProduct,firstOrderAction_sub_smul a ha]
    ring
  have hI (v : SchwartzMap Space ℂ) : Integrable (fun x => conj (h x)*actualCoefficientCommutator a r v x) :=
    (actualCoefficientCommutator_integrable hBase hCont r v).bdd_mul
      h.continuous.aestronglyMeasurable.star ⟨SchwartzMap.seminorm ℝ 0 0 h,fun x => by
        rw [Complex.norm_conj]
        exact SchwartzMap.norm_le_seminorm ℝ h x⟩
  have hInt : (∫ x, conj (h x)*actualCoefficientCommutator a r (f-c • g) x)=
      (∫ x, conj (h x)*actualCoefficientCommutator a r f x)-
        c*(∫ x, conj (h x)*actualCoefficientCommutator a r g x) := by
    have hEq (x : Space) : conj (h x)*actualCoefficientCommutator a r (f-c • g) x=
        conj (h x)*actualCoefficientCommutator a r f x-
          c*(conj (h x)*actualCoefficientCommutator a r g x) := by rw [hT]; ring
    simp_rw [hEq]
    rw [integral_sub (hI f) ((hI g).const_mul c),integral_const_mul]
  have hLp : (f-c • g : SchwartzMap Space ℂ).toLp 2 volume =
      f.toLp 2 volume-c • g.toLp 2 volume := by
    let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
    change J (f-c • g)=J f-c • J g
    rw [map_sub,map_smul]
  simp only [canceledCoefficientPair,hInt,hP f g c,hLp,inner_sub_right,inner_smul_right]
  ring

end Burnett.Analysis.CarlesonEmbedding
