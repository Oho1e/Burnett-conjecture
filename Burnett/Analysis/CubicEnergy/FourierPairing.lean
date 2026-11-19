import Burnett.Analysis.CubicEnergy.SymbolDecomposition
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Burnett.RicciSymbol
open scoped FourierTransform ComplexConjugate ContDiff BigOperators
abbrev Joint := E × E

private theorem zeroOrder_control {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : X → ℝ) (hm : ContDiffOn ℝ ∞ m {x | x ≠ 0})
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ≠ 0 → ‖m x‖ ≤ C) :
    Measurable m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖m x‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := hbound
  refine ⟨measurable_of_continuousOn_compl_singleton 0 hm.continuousOn,
    max C ‖m 0‖,hC.trans (le_max_left _ _),?_⟩
  intro x
  by_cases hx : x=0
  · simp [hx]
  · exact (hB x hx).trans (le_max_left _ _)

private theorem cm_control (m : Joint → ℝ) (h : CoifmanMeyerSymbol m) :
    Measurable m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖m x‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := h.2 0
  apply zeroOrder_control m h.1
  exact ⟨C,hC,fun ⟨η,ξ⟩ hp => by simpa using hB η ξ hp⟩

private abbrev hat (f : SchwartzMap E ℂ) : SchwartzMap E ℂ := SchwartzMap.fourierTransformCLM ℂ f

/-- Absolutely integrable joint-frequency pairing for a symbol with one
derivative on the first factor and three genuine Schwartz Fourier transforms. -/
def weightedFourier (a : Joint → ℝ) (f v w : SchwartzMap E ℂ) (p : Joint) : ℂ :=
  (a p : ℂ) * (hat f) p.1 * (hat v) p.2 * conj ((hat w) (p.1+p.2))

theorem integrable_weightedFourier (a : Joint → ℝ) (ha : Measurable a)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ p, ‖a p‖ ≤ C * ‖p.1‖)
    (f v w : SchwartzMap E ℂ) : Integrable (weightedFourier a f v w) := by
  let S := SchwartzMap.seminorm ℝ 0 0 (hat w)
  have hs : 0 ≤ S := apply_nonneg _ _
  have hf : Integrable (fun η : E => ‖η‖*‖(hat f) η‖) :=
    by simpa only [pow_one] using (hat f).integrable_pow_mul volume 1
  have hv : Integrable (fun ξ : E => ‖(hat v) ξ‖) := (hat v).integrable.norm
  have hI := (hf.mul_prod hv).const_mul (C*S)
  rw [Measure.volume_eq_prod E E]
  apply hI.mono'
  · have hφ : Measurable (fun p : Joint => (hat f) p.1) := (hat f).continuous.measurable.comp measurable_fst
    have hψ : Measurable (fun p : Joint => (hat v) p.2) := (hat v).continuous.measurable.comp measurable_snd
    have hw : Measurable (fun p : Joint => (hat w) (p.1+p.2)) := (hat w).continuous.measurable.comp (measurable_fst.add measurable_snd)
    exact ((((Complex.continuous_ofReal.measurable.comp ha).mul hφ).mul hψ).mul
      (Complex.continuous_conj.measurable.comp hw)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro p
    change ‖weightedFourier a f v w p‖ ≤ C*S*((‖p.1‖*‖(hat f) p.1‖)*‖(hat v) p.2‖)
    simp only [weightedFourier,norm_mul,Complex.norm_real,Complex.norm_conj]
    calc
      _ ≤ (C*‖p.1‖) * ‖(hat f) p.1‖ * ‖(hat v) p.2‖ * S := by
        gcongr
        · exact hbound p
        · exact (hat w).norm_le_seminorm ℝ _
      _ = _ := by ring

def lowTerm (b : E → ℝ) (j : Index) (p : Joint) : ℝ := p.1 j * lowSymbol b j p.1 p.2
def productTerm (b : E → ℝ) (j : Index) (p : Joint) : ℝ :=
  angularComponent b j (p.1+p.2) * productSymbol j p.1 p.2 * ‖p.1‖
def inputTerm (b : E → ℝ) (j : Index) (p : Joint) : ℝ :=
  inputSymbol j p.1 p.2 * ‖p.1‖ * angularComponent b j p.2

theorem pieces_integrable (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (j : Index) (f v w : SchwartzMap E ℂ) :
    Integrable (weightedFourier (lowTerm b j) f v w) ∧
    Integrable (weightedFourier (productTerm b j) f v w) ∧
    Integrable (weightedFourier (inputTerm b j) f v w) := by
  obtain ⟨hl,hp,hi,hc,hd⟩ := (commutator_symbol_decomposition b hb hh).1 j
  obtain ⟨ml,L,hL,bl⟩ := cm_control _ hl
  obtain ⟨mp,P,hP,bp⟩ := cm_control _ hp
  obtain ⟨mi,N,hN,bn⟩ := cm_control _ hi
  obtain ⟨A,hA,bA⟩ := hd 0
  obtain ⟨mc,O,hO,bc⟩ := zeroOrder_control (angularComponent b j) hc
    ⟨A,hA,fun x hx => by simpa using bA x hx⟩
  refine ⟨?_,?_,?_⟩
  · apply integrable_weightedFourier _ (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp measurable_fst).mul ml) L hL
    intro p
    rw [norm_mul,mul_comm L]
    exact mul_le_mul (PiLp.norm_apply_le p.1 j) (bl p) (norm_nonneg _) (norm_nonneg _)
  · apply integrable_weightedFourier _ (((mc.comp (measurable_fst.add measurable_snd)).mul mp).mul measurable_fst.norm) (O*P) (mul_nonneg hO hP)
    intro p
    simp only [norm_mul,norm_norm]
    gcongr
    · exact bc _
    · exact bp p
  · apply integrable_weightedFourier _ ((mi.mul measurable_fst.norm).mul (mc.comp measurable_snd)) (N*O) (mul_nonneg hN hO)
    intro p
    simp only [norm_mul,norm_norm]
    rw [mul_right_comm N O]
    gcongr
    · exact bn p
    · exact bc _

end Burnett.A02.FrequencySplit
