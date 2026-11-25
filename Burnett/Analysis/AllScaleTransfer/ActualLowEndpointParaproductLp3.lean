import Burnett.Analysis.AllScaleTransfer.EndpointWindowLp3
import Burnett.Analysis.AllScaleTransfer.ActualLowEndpointParaproduct
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.A05
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Filter Metric Finset Burnett.Fourier Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radialBallBump)
open Burnett.A02.FrequencySplit.CMBilinearDual (schwartz_toLp_denseRange)
open scoped ENNReal

private abbrev p3 := ENNReal.ofReal (3 : ℝ)
private abbrev p32 := (p3⁻¹ + p3⁻¹)⁻¹

local instance : Fact (1 ≤ p3) := ⟨by norm_num⟩
local instance : ENNReal.HolderTriple p3 p3 p32 := ENNReal.HolderTriple.of _ _

local instance : ENNReal.HolderConjugate p32 p3 := ⟨by
  change (p3⁻¹ + p3⁻¹)⁻¹⁻¹ + p3⁻¹ = (1 : ℝ≥0∞)⁻¹
  simp only [inv_inv,inv_one,p3,ENNReal.ofReal_ofNat]
  have hn : (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hs : (3 : ℝ≥0∞)⁻¹ + (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hn,hn⟩
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hs,hn⟩) ENNReal.one_ne_top).mp
  rw [ENNReal.toReal_add hs hn,ENNReal.toReal_add hn hn]
  norm_num⟩

local instance : Fact (1 ≤ p32) := ⟨ENNReal.HolderConjugate.one_le p32 p3⟩

private def endpointCubicIntegral (f g w : EndpointLp3) : ℂ :=
  let B := ContinuousLinearMap.mul ℂ ℂ
  (B.lpPairing volume p32 p3) ((B.holderL volume p3 p3 p32) f g) w

private theorem endpointCubicIntegral_eq (f g w : EndpointLp3) :
    endpointCubicIntegral f g w = ∫ x, f x * g x * w x := by
  unfold endpointCubicIntegral
  rw [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.holderL_apply_apply]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := p32) f g] with x hx
  rw [hx]
  rfl

private theorem endpointCubicIntegral_continuous {X : Type*} [TopologicalSpace X]
    (f g w : X → EndpointLp3) (hf : Continuous f) (hg : Continuous g) (hw : Continuous w) :
    Continuous (fun x => endpointCubicIntegral (f x) (g x) (w x)) := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let K := B.holderL (volume : Measure E) p3 p3 p32
  let L := B.lpPairing (volume : Measure E) p32 p3
  have h1 : Continuous (fun x => K (f x) (g x)) :=
    (K.continuous.comp hf).clm_apply hg
  exact (L.continuous.comp h1).clm_apply hw

private theorem endpointCubic_integrable (f g w : EndpointLp3) :
    Integrable (fun x => f x * g x * w x) (volume : Measure E) := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have h := B.memLp_of_bilin p32 (Lp.memLp f) (Lp.memLp g)
  exact memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 h (Lp.memLp w))

/-- The scale conversion from the integer radian annulus to a reference Fourier window. -/
def endpointScale (j : ℤ) : ℝ := (2 : ℝ)^(-j) * tau

private theorem endpointScale_pos (j : ℤ) : 0 < endpointScale j :=
  mul_pos (by positivity) (mul_pos (by norm_num) Real.pi_pos)

def endpointLowWindowLp3 (gap : ℕ) (j : ℤ) : EndpointLp3 →L[ℂ] EndpointLp3 :=
  endpointWindowLp3 endpointLowProfile ((2 : ℝ)^gap * endpointScale j)
    (mul_pos (by positivity) (endpointScale_pos j))

def endpointHighWindowLp3 (j : ℤ) : EndpointLp3 →L[ℂ] EndpointLp3 :=
  endpointWindowLp3 endpointHighProfile (endpointScale j) (endpointScale_pos j)

def endpointThickWindowLp3 (j : ℤ) : EndpointLp3 →L[ℂ] EndpointLp3 :=
  endpointWindowLp3 endpointThickProfile (endpointScale j) (endpointScale_pos j)

theorem endpointLowWindowSymbol_zero {s : ℝ} (hs : 0 < s) :
    rescaleSymbol (modulatedWindowSymbol endpointLowProfile 0) s hs (0 : E) = 1 := by
  rw [endpointWindowSymbol_eval,smul_zero,endpointLowProfile,
    CMBilinearDual.schwartzBump_apply]
  have h : radialBallBump (0 : E) = 1 := radialBallBump.one_of_mem_closedBall
    (by rw [mem_closedBall_zero_iff,norm_zero]; exact radialBallBump.rIn_pos.le)
  rw [h,Complex.ofReal_one]

/-- The finite spatial paraproduct with the three actual fixed Fourier windows. -/
def lowEndpointParaproductLp3 (gap : ℕ) {n : ℕ} (j : Fin n ↪ ℤ)
    (f g w : EndpointLp3) : ℂ :=
  ∑ i : Fin n, endpointCubicIntegral (endpointLowWindowLp3 gap (j i) f)
    (endpointHighWindowLp3 (j i) g) (endpointThickWindowLp3 (j i) w)

theorem lowEndpointParaproductLp3_eq_integral (gap : ℕ) {n : ℕ} (j : Fin n ↪ ℤ) (f g w : EndpointLp3) :
    let term (i : Fin n) (x : E) := endpointLowWindowLp3 gap (j i) f x *
      endpointHighWindowLp3 (j i) g x * endpointThickWindowLp3 (j i) w x
    (∀ i, Integrable (term i)) ∧
      lowEndpointParaproductLp3 gap j f g w = ∑ i, ∫ x, term i x := by
  refine ⟨fun i => endpointCubic_integrable _ _ _,?_⟩
  unfold lowEndpointParaproductLp3
  exact Finset.sum_congr rfl (fun i _ => endpointCubicIntegral_eq _ _ _)

theorem lowEndpointParaproductLp3_Schwartz (gap : ℕ) {n : ℕ} (j : Fin n ↪ ℤ)
    (f g w : SchwartzMap E ℂ) :
    lowEndpointParaproductLp3 gap j (f.toLp p3 volume) (g.toLp p3 volume) (w.toLp p3 volume) =
      ∑ i : Fin n, ∫ x, shiftedWindowOperator endpointLowProfile f ((2 : ℝ)^gap * endpointScale (j i)) 0 x *
        shiftedWindowOperator endpointHighProfile g (endpointScale (j i)) 0 x *
        shiftedWindowOperator endpointThickProfile w (endpointScale (j i)) 0 x := by
  rw [(lowEndpointParaproductLp3_eq_integral gap j _ _ _).2]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [endpointWindowLp3_Schwartz endpointLowProfile f ((2 : ℝ)^gap * endpointScale (j i))
      (mul_pos (by positivity) (endpointScale_pos (j i))),
    endpointWindowLp3_Schwartz endpointHighProfile g (endpointScale (j i)) (endpointScale_pos (j i)),
    endpointWindowLp3_Schwartz endpointThickProfile w (endpointScale (j i)) (endpointScale_pos (j i))]
    with x hf hg hw
  rw [endpointLowWindowLp3, endpointHighWindowLp3, endpointThickWindowLp3, hf,hg,hw]

private theorem lowEndpointParaproductLp3_continuous (gap : ℕ) {n : ℕ} (j : Fin n ↪ ℤ) :
    Continuous (fun u : EndpointLp3 × EndpointLp3 × EndpointLp3 => lowEndpointParaproductLp3 gap j u.1 u.2.1 u.2.2) := by
  let Triple := EndpointLp3 × EndpointLp3 × EndpointLp3
  let first (i : Fin n) (u : Triple) : EndpointLp3 := endpointLowWindowLp3 gap (j i) u.1
  let second (i : Fin n) (u : Triple) : EndpointLp3 := endpointHighWindowLp3 (j i) u.2.1
  let third (i : Fin n) (u : Triple) : EndpointLp3 := endpointThickWindowLp3 (j i) u.2.2
  have cfirst (i : Fin n) : Continuous (first i) :=
    (endpointLowWindowLp3 gap (j i)).continuous.comp continuous_fst
  have csecond (i : Fin n) : Continuous (second i) :=
    (endpointHighWindowLp3 (j i)).continuous.comp
      (show Continuous (fun u : Triple => u.2.1) from continuous_fst.comp continuous_snd)
  have cthird (i : Fin n) : Continuous (third i) :=
    (endpointThickWindowLp3 (j i)).continuous.comp
      (show Continuous (fun u : Triple => u.2.2) from continuous_snd.comp continuous_snd)
  have ct (i : Fin n) :
      Continuous (fun u : Triple => endpointCubicIntegral (first i u) (second i u) (third i u)) :=
    endpointCubicIntegral_continuous (first i) (second i) (third i) (cfirst i) (csecond i) (cthird i)
  change Continuous (fun u : Triple => ∑ i : Fin n, endpointCubicIntegral (first i u) (second i u) (third i u))
  exact continuous_finset_sum Finset.univ (fun i _ => ct i)

/-- The same constant as in the finite Schwartz estimate works on three L³ inputs. -/
theorem integer_low_endpoint_paraproduct_bound_Lp3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (gap n : ℕ) (j : Fin n ↪ ℤ) (f g w : EndpointLp3),
      ‖lowEndpointParaproductLp3 gap j f g w‖ ≤ C * ‖f‖ * ‖g‖ * ‖w‖ := by
  obtain ⟨C,hC,bound⟩ := integer_low_endpoint_paraproduct_bound
  refine ⟨C,hC,?_⟩
  intro gap n j f g w
  have hd := schwartz_toLp_denseRange (V := E) p3 (by norm_num [p3])
  have hc : IsClosed {u : EndpointLp3 × EndpointLp3 × EndpointLp3 |
      ‖lowEndpointParaproductLp3 gap j u.1 u.2.1 u.2.2‖ ≤ C * ‖u.1‖ * ‖u.2.1‖ * ‖u.2.2‖} :=
    isClosed_le (lowEndpointParaproductLp3_continuous gap j).norm
      (((continuous_const.mul continuous_fst.norm).mul continuous_snd.fst.norm).mul continuous_snd.snd.norm)
  refine hd.induction_on₃ hc (fun a b d => ?_) f g w
  rw [lowEndpointParaproductLp3_Schwartz]
  exact (bound gap n j a b d).2

/-- The actual angular Fourier actions can occupy both input slots of the
integer low endpoint paraproduct with their sixth-power mode losses. -/
theorem exists_integer_low_endpoint_angularLp3_bound (P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ R : FourierMode → (EndpointLp3 →L[ℂ] EndpointLp3),
      (∀ (a : FourierMode) (f : E → ℂ) (hf : MemLp f 2 volume) (h₃ : MemLp f p3 volume),
        (R a (h₃.toLp f) : E → ℂ) =ᵐ[volume]
          (fourierMultiplier (endpointModeBoundedSymbol P a) (hf.toLp f) : E → ℂ)) ∧
      (∀ (a : FourierMode) (f : SchwartzMap E ℂ),
        (R a (f.toLp p3 volume) : E → ℂ) =ᵐ[volume] endpointModeRadianAction P a f) ∧
      ∀ (ab : FourierModePair) (gap n : ℕ) (j : Fin n ↪ ℤ) (f g w : EndpointLp3),
        ‖lowEndpointParaproductLp3 gap j (R ab.1 f) (R ab.2 g) w‖ ≤
          C * modePairLoss ab * ‖f‖ * ‖g‖ * ‖w‖ := by
  obtain ⟨A,hA,para⟩ := integer_low_endpoint_paraproduct_bound_Lp3
  obtain ⟨B,hB,operator⟩ := exists_endpointMode_L3_bound P
  choose R loss intersection actual using operator
  refine ⟨A*B^2,by positivity,R,intersection,actual,?_⟩
  intro ab gap n j f g w
  calc
    _ ≤ A * ‖R ab.1 f‖ * ‖R ab.2 g‖ * ‖w‖ := para gap n j _ _ _
    _ ≤ A * (B * Burnett.A03.spatialLatticeWeight ab.1 ^ 6 * ‖f‖) *
        (B * Burnett.A03.spatialLatticeWeight ab.2 ^ 6 * ‖g‖) * ‖w‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left (loss ab.1 f) hA) (loss ab.2 g)
          (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = _ := by unfold modePairLoss; ring

end Burnett.A05
