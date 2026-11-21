import Burnett.Analysis.PrincipalEnergy.Commutator.SeparatedKernelBounds
import Burnett.Analysis.PrincipalEnergy.Quantization.LowCommutatorKernelConditions
import Burnett.Analysis.PrincipalEnergy.Quantization.KernelConditions
import Burnett.Analysis.PrincipalEnergy.Quantization.OffSupportFirstOrder
import Burnett.Analysis.PrincipalEnergy.Quantization.PhysicalFrequencySplit

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate NNReal

/-- The low and high pieces of the actual left-quantized commutator kernel,
using the already fixed complementary Fourier cutoffs. -/
def fullCoefficientKernel (a : Space → Space → ℂ) (r : Space → ℂ) (x y : Space) : ℂ :=
  lowCoefficientKernel a r x y + coefficientKernel r (firstOrderKernel a) x y

theorem exists_fullCoefficientKernel_bounds {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : Space → ℂ) (L : NNReal), LipschitzWith L r →
      CalderonZygmundKernelBounds (fullCoefficientKernel a r) ((L:ℝ)*C) := by
  obtain ⟨A,hA,hLo⟩ := exists_firstOrderLow_commutatorKernel_conditions ha
  obtain ⟨B,hB,hHi⟩ := exists_firstOrderHigh_commutatorKernel_conditions ha
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro r L hLip
  obtain ⟨hLs,hLx,hLy⟩ := hLo r L hLip
  obtain ⟨hHs,hHx,hHy⟩ := hHi r L hLip
  have hLow : CalderonZygmundKernelBounds (lowCoefficientKernel a r) ((L:ℝ)*A) :=
    ⟨mul_nonneg L.coe_nonneg hA,hLs,hLx,hLy⟩
  have hHigh : CalderonZygmundKernelBounds (coefficientKernel r (firstOrderKernel a)) ((L:ℝ)*B) :=
    ⟨mul_nonneg L.coe_nonneg hB,hHs,hHx,hHy⟩
  rw [mul_add]
  exact hLow.add hHigh

/-- The full actual commutator on separated tests is the integral of the
sum of the genuine low and high coefficient kernels. -/
theorem actualCoefficientCommutator_separated_pair_eq_kernel
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (r f g : SchwartzMap Space ℂ)
    (L : NNReal) (U : ℝ) (hLip : LipschitzWith L r) (hR : ∀ x, ‖r x‖≤U)
    (hf : HasCompactSupport (f : Space → ℂ))
    (d : ℝ) (hd : 0<d) (hGap : ∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) :
    (∫ x, conj (g x)*actualCoefficientCommutator a r f x) =
      ∫ p : Space × Space, conj (g p.1)*(fullCoefficientKernel a r p.1 p.2*f p.2)
        ∂((volume : Measure Space).prod volume) := by
  obtain ⟨A,hA,hLo⟩ := exists_firstOrderLow_commutatorKernel_conditions ha
  obtain ⟨B,hB,hHi⟩ := exists_firstOrderHigh_commutatorKernel_conditions ha
  let low := lowCoefficientKernel a r
  let high := coefficientKernel r (firstOrderKernel a)
  obtain ⟨hLs,hLx,hLy⟩ := hLo r L hLip
  obtain ⟨hHs,hHx,hHy⟩ := hHi r L hLip
  have hLow : CalderonZygmundKernelBounds low ((L:ℝ)*A) := ⟨mul_nonneg L.coe_nonneg hA,hLs,hLx,hLy⟩
  have hHigh : CalderonZygmundKernelBounds high ((L:ℝ)*B) := ⟨mul_nonneg L.coe_nonneg hB,hHs,hHx,hHy⟩
  let μ : Measure (Space × Space) := (volume : Measure Space).prod volume
  let P (p : Space × Space) := conj (g p.1)*(low p.1 p.2*f p.2)
  let Q (p : Space × Space) := conj (g p.1)*(high p.1 p.2*f p.2)
  have hP : Integrable P μ := integrable_separated_kernel_pair hLow f g d hd hGap
  have hQ : Integrable Q μ := integrable_separated_kernel_pair hHigh f g d hd hGap
  let rf := scalarSchwartzProduct r f
  have hrf (y : Space) : rf y=r y*f y := scalarSchwartzProduct_apply r f y
  have hOffSupport (x : Space) (hg : g x≠0) : x∉tsupport (f : Space → ℂ) := by
    intro hx
    have hClosed : IsClosed {y : Space | d≤‖x-y‖} :=
      isClosed_le continuous_const (continuous_const.sub continuous_id).norm
    have hSet : tsupport (f : Space → ℂ) ⊆ {y : Space | d≤‖x-y‖} :=
      closure_minimal (fun y hy => hGap x y hy hg) hClosed
    have hAt : d≤‖x-x‖ := hSet hx
    rw [sub_self,norm_zero] at hAt
    exact (not_le_of_gt hd) hAt
  have hLoEq (x : Space) : conj (g x)*lowCoefficientCommutator a r f x=∫ y, P (x,y) := by
    change conj (g x)*lowCoefficientCommutator a r f x = ∫ y, conj (g x)*(low x y*f y)
    rw [integral_const_mul,lowCoefficientCommutator_eq_kernel ha.frequency hCont r r.continuous U hR f x]
  have hHiEq (x : Space) :
      conj (g x)*(r x*firstOrderHighAction a f x-firstOrderHighAction a rf x)=∫ y, Q (x,y) := by
    by_cases hg : g x=0
    · simp [Q,hg]
    change conj (g x)*(r x*firstOrderHighAction a f x-firstOrderHighAction a rf x) =
      ∫ y, conj (g x)*(high x y*f y)
    rw [integral_const_mul,firstOrderHighCoefficientCommutator_offSupport a ha.frequency r f rf hrf L hLip
      hf x (hOffSupport x hg)]
  have hSplit (x : Space) : actualCoefficientCommutator a r f x=lowCoefficientCommutator a r f x+
      (r x*firstOrderHighAction a f x-firstOrderHighAction a rf x) :=
    full_coefficient_commutator_split ha.frequency r f rf hrf x
  calc
    _ = ∫ x, (∫ y, P (x,y))+(∫ y, Q (x,y)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hSplit,mul_add,hLoEq,hHiEq]
    _ = (∫ p, P p ∂μ)+(∫ p, Q p ∂μ) := by
      rw [integral_add hP.integral_prod_left hQ.integral_prod_left,integral_prod P hP,integral_prod Q hQ]
    _ = _ := by
      rw [← integral_add hP hQ]
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [P,Q,fullCoefficientKernel,low,high]
      ring

end Burnett.Analysis.CarlesonEmbedding
