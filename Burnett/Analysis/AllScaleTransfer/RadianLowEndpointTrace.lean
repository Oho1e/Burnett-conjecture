import Burnett.Analysis.AllScaleTransfer.RadianLowEndpointModes
import Burnett.Analysis.AllScaleTransfer.EndpointAngularTraceSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  integrable_radianTrilinearWeight_of_bounded)
open Burnett.Analysis.LowRatio (Angles Point Window endpoint)
open Burnett.A05.BoxFourier
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private def windowBound : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 endpointLowProfile * SchwartzMap.seminorm ℝ 0 0 endpointHighProfile *
    SchwartzMap.seminorm ℝ 0 0 endpointThickProfile

private theorem windows_continuous (gap : ℕ) (j : ℤ) : Continuous (lowEndpointRadianWindows gap j) := by
  change Continuous (fun p : Joint => lowEndpointRadianWindows gap j p)
  simp only [lowEndpointRadianWindows_eq_profiles]
  fun_prop

private theorem windows_norm (gap : ℕ) (j : ℤ) (p : Joint) :
    ‖lowEndpointRadianWindows gap j p‖ ≤ windowBound := by
  rw [lowEndpointRadianWindows_eq_profiles,norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (endpointLowProfile.norm_le_seminorm ℝ _) (endpointHighProfile.norm_le_seminorm ℝ _)
      (norm_nonneg _) (apply_nonneg _ _))
    (endpointThickProfile.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)

private def angularPair (P : ℝ) (ab : FourierModePair) (p : Joint) : ℂ :=
  endpointModeSymbol P ab.1 p.1 * endpointModeSymbol P ab.2 p.2

private theorem angularPair_measurable (P : ℝ) (ab : FourierModePair) : Measurable (angularPair P ab) :=
  ((endpointModeSymbol_measurable P ab.1).comp measurable_fst).mul
    ((endpointModeSymbol_measurable P ab.2).comp measurable_snd)

private theorem angularPair_norm (P : ℝ) (ab : FourierModePair) (p : Joint) :
    ‖angularPair P ab p‖ = 1 := by simp only [angularPair,norm_mul,endpointModeSymbol_norm,mul_one]

private theorem form_const_mul (c : ℂ) (m : Joint → ℂ) (f g w : SchwartzMap E ℂ) :
    radianTrilinearForm (fun p => c*m p) f g w = c * radianTrilinearForm m f g w := by
  unfold radianTrilinearForm radianTrilinearWeight
  simp only [mul_assoc, integral_const_mul, Algebra.smul_def]
  ring

private theorem form_finite_window_sum (P : ℝ) (ab : FourierModePair) (gap : ℕ)
    {n : ℕ} (j : Fin n ↪ ℤ) (f g w : SchwartzMap E ℂ) :
    radianTrilinearForm (fun p => angularPair P ab p * ∑ i : Fin n, lowEndpointRadianWindows gap (j i) p) f g w =
      ∑ i : Fin n, radianTrilinearForm (angularLowEndpointModeSymbol P ab gap (j i)) f g w := by
  have hInt (i : Fin n) : Integrable
      (radianTrilinearWeight (angularLowEndpointModeSymbol P ab gap (j i)) f g w) := by
    apply integrable_radianTrilinearWeight_of_bounded _ _ windowBound _ f g w
    · exact ((angularPair_measurable P ab).mul (windows_continuous gap (j i)).measurable).aestronglyMeasurable
    · intro p
      change ‖angularPair P ab p * lowEndpointRadianWindows gap (j i) p‖ ≤ _
      rw [norm_mul,angularPair_norm,one_mul]
      exact windows_norm gap (j i) p
  unfold radianTrilinearForm
  rw [← Finset.smul_sum, ← integral_finset_sum _ (fun i _ => hInt i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianTrilinearWeight, Finset.mul_sum,Finset.sum_mul,angularLowEndpointModeSymbol,angularPair]

private theorem chart_eligible_frequencies_ae :
    ∀ᵐ p : Joint ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  let μ : Measure E := volume
  have h : ∀ᵐ x : E ∂μ, x ≠ 0 := (Set.countable_singleton (0 : E)).ae_notMem μ
  rw [Measure.volume_eq_prod E E]
  exact Filter.Eventually.and
    ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h)
    ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h)

/-- The endpoint uses the same two signed directions as the angular expansion. -/
def lowEndpointM0Symbol (M : Point → ℂ) (p : Joint) : ℂ :=
  endpoint M (endpointTail (endpointDirection p.1), endpointTail (endpointDirection p.2))

private theorem form_hasSum_low_endpoint_modes (P : ℝ) (M : Point → ℂ) (c : FourierModePair → ℂ)
    (hc : Summable (fun ab => ‖c ab‖)) (gap : ℕ) {n : ℕ} (j : Fin n ↪ ℤ)
    (f g w : SchwartzMap E ℂ)
    (hSeries : ∀ᵐ p : Joint ∂(volume : Measure Joint),
      radianWeight (fun _ => 1) f g w p ≠ 0 →
      HasSum (fun ab => c ab * angularPair P ab p) (lowEndpointM0Symbol M p)) :
    HasSum (fun ab => c ab * ∑ i : Fin n,
      radianTrilinearForm (angularLowEndpointModeSymbol P ab gap (j i)) f g w)
      (radianTrilinearForm (fun p => lowEndpointM0Symbol M p *
        ∑ i : Fin n, lowEndpointRadianWindows gap (j i) p) f g w) := by
  let K := radianWeight (fun _ => 1) f g w
  let W (p : Joint) := ∑ i : Fin n, lowEndpointRadianWindows gap (j i) p
  let D : ℝ := (n:ℝ)*windowBound
  have hW : Measurable W := (continuous_finset_sum Finset.univ (fun i _ => windows_continuous gap (j i))).measurable
  have hBound (p : Joint) : ‖W p‖ ≤ D := by
    refine (norm_sum_le_of_le _ (fun i _ => windows_norm gap (j i) p)).trans_eq ?_
    simp [D]
  have hone : radianTrilinearWeight (fun _ => (1 : ℂ)) f g w = K := by
    funext p
    change (1 : ℂ) * K p = K p
    exact one_mul _
  have hK : Integrable K := by
    rw [← hone]
    exact integrable_radianTrilinearWeight_of_bounded (fun _ => (1 : ℂ))
      aestronglyMeasurable_const 1 (fun _ => norm_one.le) f g w
  let X (ab : FourierModePair) (p : Joint) := (c ab * angularPair P ab p) * W p * K p
  let d (ab : FourierModePair) := ‖c ab‖ * D
  have hd : Summable d := hc.mul_right D
  have hMass : Integrable (fun p : Joint => ∑' ab, d ab * ‖K p‖) := by
    have eq : (fun p : Joint => ∑' ab, d ab * ‖K p‖) =
        (fun p => (∑' ab, d ab) * ‖K p‖) := funext (fun p => hd.tsum_mul_right _)
    rw [eq]
    exact hK.norm.const_mul _
  have raw : HasSum (fun ab => ∫ p, X ab p) (∫ p, lowEndpointM0Symbol M p * W p * K p) := by
    apply hasSum_integral_of_dominated_convergence (fun ab p => d ab * ‖K p‖)
    · intro ab
      exact (((measurable_const.mul (angularPair_measurable P ab)).mul hW).aestronglyMeasurable.mul hK.1)
    · intro ab
      filter_upwards with p
      simp only [X,d,norm_mul,angularPair_norm,mul_one]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hBound p) (norm_nonneg _)
    · exact Eventually.of_forall (fun p => hd.mul_right ‖K p‖)
    · exact hMass
    · filter_upwards [hSeries] with p hp
      by_cases hz : K p = 0
      · simp only [X,hz,mul_zero]
        exact hasSum_zero
      · exact ((hp hz).mul_right (W p)).mul_right (K p)
  have normed := raw.const_smul ((tau^8)⁻¹ : ℝ)
  have term (ab : FourierModePair) :
      (tau^8)⁻¹ • (∫ p, X ab p) =
        c ab * ∑ i : Fin n, radianTrilinearForm (angularLowEndpointModeSymbol P ab gap (j i)) f g w := by
    change radianTrilinearForm (fun p => (c ab * angularPair P ab p) * W p) f g w = _
    simp_rw [mul_assoc (c ab)]
    rw [form_const_mul,form_finite_window_sum]
  exact normed.congr_fun (fun ab => (term ab).symm)

/-- On the actual selected chart, the finite integer low endpoint form with the
literal angular trace is bounded by its original C¹⁰⁰ symbol budget. -/
theorem exists_radian_lowEndpoint_M0_bound {U : Set Angles} (hU : IsOpen U)
    {a b r R P : ℝ} (ha : a < 0) (hb : 0 < b) (hr : 0 < r) (hR : r < R) (hP : 2 < P)
    (hChart : closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Point → ℂ) (A : ℝ), 0 ≤ A → ContDiffOn ℝ 100 M (Window U a b) →
      (∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j M z‖ ≤ A) →
      ∀ (gap n : ℕ) (j : Fin n ↪ ℤ) (f g w : SchwartzMap E ℂ),
        (∀ᵐ p : Joint ∂(volume : Measure Joint), radianWeight (fun _ => 1) f g w p ≠ 0 →
          ‖endpointTail (endpointDirection p.1)‖ ≤ r ∧ ‖endpointTail (endpointDirection p.2)‖ ≤ r) →
        ‖radianTrilinearForm (fun p => lowEndpointM0Symbol M p *
            ∑ i : Fin n, lowEndpointRadianWindows gap (j i) p) f g w‖ ≤
          C * A * ‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
            ‖w.toLp (ENNReal.ofReal 3) volume‖ := by
  obtain ⟨χ,C₀,hC₀,_,_,expansion⟩ := exists_endpointTrace_angular_series hU ha hb hr hR hP hChart
  obtain ⟨B,hB,op,compareL2,_,opBound⟩ := exists_integer_low_endpoint_angularLp3_bound P
  have hK : 0 ≤ modePairSummationConstant := by
    unfold modePairSummationConstant
    exact tsum_nonneg (by intro ab; unfold modePairMajorant; positivity)
  refine ⟨B*C₀*modePairSummationConstant, by positivity, ?_⟩
  intro M A hA hM jets gap n j f g w hChartTest
  let c (ab : FourierModePair) := boxCubeFourierCoefficient P (modeIndex ab)
    (fun z => χ z • endpointBoxProfile hr hR M z)
  obtain ⟨_,hWeighted,hWeightedBound,series⟩ := expansion M A hA hM jets
  have hc : Summable (fun ab => ‖c ab‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hWeighted
    intro ab
    unfold weightedModeCoefficient
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_modePairLoss ab) (norm_nonneg (c ab))
  have point : ∀ᵐ p : Joint ∂(volume : Measure Joint), radianWeight (fun _ => 1) f g w p ≠ 0 →
      HasSum (fun ab => c ab * angularPair P ab p) (lowEndpointM0Symbol M p) := by
    filter_upwards [hChartTest,chart_eligible_frequencies_ae] with p hp hn hK0
    obtain ⟨hp₁,hp₂⟩ := hp hK0
    exact series p.1 p.2 hn.1 hn.2 hp₁ hp₂
  have hLimit := form_hasSum_low_endpoint_modes P M c hc gap j f g w point
  let F := f.toLp (ENNReal.ofReal 3) volume
  let G := g.toLp (ENNReal.ofReal 3) volume
  let H := w.toLp (ENNReal.ofReal 3) volume
  let T (ab : FourierModePair) := c ab * ∑ i : Fin n,
    radianTrilinearForm (angularLowEndpointModeSymbol P ab gap (j i)) f g w
  let D := B * ‖F‖ * ‖G‖ * ‖H‖
  have hD : 0 ≤ D := by unfold D; positivity
  have hPoint (ab : FourierModePair) : ‖T ab‖ ≤ D * weightedModeCoefficient c ab := by
    have e := lowEndpointParaproductLp3_mode_radian P ab gap j f g w (op ab.1 F) (op ab.2 G)
      (compareL2 ab.1 f (f.memLp 2 volume) (f.memLp _ volume))
      (compareL2 ab.2 g (g.memLp 2 volume) (g.memLp _ volume))
    unfold T
    rw [← e,norm_mul]
    exact (mul_le_mul_of_nonneg_left (opBound ab gap n j F G H) (norm_nonneg _)).trans_eq
      (by unfold D weightedModeCoefficient; ring)
  have hNorm : Summable (fun ab => ‖T ab‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hPoint (hWeighted.mul_left D)
  rw [← hLimit.tsum_eq]
  calc
    _ ≤ ∑' ab, ‖T ab‖ := norm_tsum_le_tsum_norm hNorm
    _ ≤ ∑' ab, D * weightedModeCoefficient c ab := hNorm.tsum_le_tsum hPoint (hWeighted.mul_left D)
    _ = D * (∑' ab, weightedModeCoefficient c ab) := hWeighted.tsum_mul_left D
    _ ≤ D * (C₀*A*modePairSummationConstant) := mul_le_mul_of_nonneg_left hWeightedBound hD
    _ = _ := by unfold D F G H; ring

end Burnett.A05
