import Burnett.Analysis.AllScaleTransfer.SphereEndpointBox
import Burnett.Analysis.AllScaleTransfer.RadianLowEndpointModes
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearModeSeries
import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition

set_option autoImplicit false
set_option maxHeartbeats 5200000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open scoped ContDiff ENNReal Topology

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

def sphereEndpointRadianSymbol (M₀ : Joint → ℂ) (p : Joint) : ℂ :=
  M₀ (endpointDirection p.1, endpointDirection p.2)

private def Wbound : ℝ := SchwartzMap.seminorm ℝ 0 0 endpointLowProfile *
  SchwartzMap.seminorm ℝ 0 0 endpointHighProfile * SchwartzMap.seminorm ℝ 0 0 endpointThickProfile

private theorem Wbound_nonneg : 0 ≤ Wbound := by unfold Wbound; positivity

private theorem endpointWindow_continuous (gap : ℕ) (j : ℤ) :
    Continuous (lowEndpointRadianWindows gap j) := by
  change Continuous (fun p : Joint => lowEndpointRadianWindows gap j p)
  simp only [lowEndpointRadianWindows_eq_profiles]
  fun_prop

private theorem endpointWindow_norm (gap : ℕ) (j : ℤ) (p : Joint) :
    ‖lowEndpointRadianWindows gap j p‖ ≤ Wbound := by
  rw [lowEndpointRadianWindows_eq_profiles,norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (endpointLowProfile.norm_le_seminorm ℝ _) (endpointHighProfile.norm_le_seminorm ℝ _)
      (norm_nonneg _) (apply_nonneg _ _))
    (endpointThickProfile.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)

private theorem endpointWindow_local_support (gap : ℕ) (p : Joint) :
    ∃ I : Finset ℤ, I.card ≤ 3 ∧ ∀ j ∉ I, lowEndpointRadianWindows gap j p = 0 := by
  obtain ⟨I,hI,zero⟩ := exists_integerRadialWindow_support_card_le_three p.2
  refine ⟨I,hI,fun j hj => ?_⟩
  have hz : radialAnnularCutoff ((2 : ℝ)^j) p.2 = 0 := zero j hj
  simp only [lowEndpointRadianWindows,hz,Complex.ofReal_zero,mul_zero,zero_mul]

private theorem endpointWindow_partial_norm (gap : ℕ) (I : Finset ℤ) (p : Joint) :
    ‖∑ j ∈ I, lowEndpointRadianWindows gap j p‖ ≤ 3 * Wbound := by
  classical
  obtain ⟨J,hJ,hzero⟩ := endpointWindow_local_support gap p
  have e : (∑ j ∈ I, lowEndpointRadianWindows gap j p) = ∑ j ∈ I ∩ J, lowEndpointRadianWindows gap j p :=
    (Finset.sum_subset Finset.inter_subset_left (fun j hj hn => hzero j (fun h => hn (Finset.mem_inter.mpr ⟨hj,h⟩)))).symm
  rw [e]
  calc
    _ ≤ ∑ j ∈ I ∩ J, Wbound := norm_sum_le_of_le _ (fun j _ => endpointWindow_norm gap j p)
    _ = ((I ∩ J).card : ℝ) * Wbound := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans hJ) Wbound_nonneg

private theorem integral_endpoint_window_series (m : Joint → ℂ) (f g h : SchwartzMap E ℂ)
    (hi : Integrable (radianTrilinearWeight m f g h)) (gap : ℕ) :
    let T (j : ℤ) := radianTrilinearForm (fun p => m p * lowEndpointRadianWindows gap j p) f g h
    (∀ I : Finset ℤ, (∑ j ∈ I, T j) = radianTrilinearForm
      (fun p => m p * ∑ j ∈ I, lowEndpointRadianWindows gap j p) f g h) ∧
    HasSum T (radianTrilinearForm (fun p => m p * ∑' j, lowEndpointRadianWindows gap j p) f g h) := by
  intro T
  let K := radianTrilinearWeight m f g h
  let W := lowEndpointRadianWindows gap
  have form (V : Joint → ℂ) : radianTrilinearForm (fun p => m p * V p) f g h =
      (tau^8)⁻¹ • ∫ p, V p * K p := by
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    simp only [radianTrilinearWeight,K]
    ring
  have int (j : ℤ) : Integrable (fun p => W j p * K p) :=
    hi.bdd_mul' (c := Wbound) (endpointWindow_continuous gap j).aestronglyMeasurable
      (Eventually.of_forall (endpointWindow_norm gap j))
  have eq (I : Finset ℤ) : (∑ j ∈ I, T j) =
      radianTrilinearForm (fun p => m p * ∑ j ∈ I, W j p) f g h := by
    simp only [T,form,← Finset.smul_sum]
    change (tau^8)⁻¹ • (∑ j ∈ I, ∫ p, W j p * K p) =
      (tau^8)⁻¹ • ∫ p, (∑ j ∈ I, W j p) * K p
    rw [← integral_finset_sum _ (fun j _ => int j)]
    simp only [Finset.sum_mul]
  refine ⟨eq,?_⟩
  have lim : Tendsto (fun I : Finset ℤ => ∫ p, (∑ j ∈ I, W j p) * K p) atTop
      (𝓝 (∫ p, (∑' j, W j p) * K p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => (3 * Wbound) * ‖K p‖)
    · exact Eventually.of_forall (fun I =>
        (I.aestronglyMeasurable_fun_sum (fun j _ => (endpointWindow_continuous gap j).aestronglyMeasurable)).mul hi.1)
    · exact Eventually.of_forall (fun I => Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (endpointWindow_partial_norm gap I p) (norm_nonneg _)))
    · exact hi.norm.const_mul _
    · apply Eventually.of_forall
      intro p
      obtain ⟨J,_,hz⟩ := endpointWindow_local_support gap p
      have H : HasSum (fun j => W j p) (∑' j, W j p) := (summable_of_ne_finset_zero hz).hasSum
      exact (show Tendsto (fun I : Finset ℤ => ∑ j ∈ I, W j p) atTop (𝓝 (∑' j, W j p)) from H).mul
        tendsto_const_nhds
  change Tendsto (fun I : Finset ℤ => ∑ j ∈ I, T j) atTop _
  simp only [eq,form]
  exact lim.const_smul ((tau^8)⁻¹ : ℝ)

private def sphereMode (ab : FourierModePair) (p : Joint) : ℂ :=
  endpointModeSymbol 3 ab.1 p.1 * endpointModeSymbol 3 ab.2 p.2

private theorem sphereMode_measurable (ab : FourierModePair) : Measurable (sphereMode ab) :=
  ((endpointModeSymbol_measurable 3 ab.1).comp measurable_fst).mul
    ((endpointModeSymbol_measurable 3 ab.2).comp measurable_snd)

private theorem sphereMode_norm (ab : FourierModePair) (p : Joint) : ‖sphereMode ab p‖ = 1 := by
  simp only [sphereMode,norm_mul,endpointModeSymbol_norm,mul_one]

private theorem nonzero_frequency_pair_ae : ∀ᵐ p : Joint ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  let μ : Measure E := volume
  have h : ∀ᵐ x : E ∂μ, x ≠ 0 := (Set.countable_singleton (0 : E)).ae_notMem μ
  rw [Measure.volume_eq_prod E E]
  exact Filter.Eventually.and ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h)
    ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h)

private theorem trilinear_const_mul (c : ℂ) (m : Joint → ℂ) (f g h : SchwartzMap E ℂ) :
    radianTrilinearForm (fun p => c * m p) f g h = c * radianTrilinearForm m f g h := by
  unfold radianTrilinearForm radianTrilinearWeight
  simp only [mul_assoc,integral_const_mul,Algebra.smul_def]
  ring

/-- The zero-ratio endpoint on both full spheres, in the actual complex radian
trilinear form. The fixed off-axis box data controls every finite radial
truncation and the full integer window sum with one constant. -/
theorem exists_sphereEndpoint_radian_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M₀ : Joint → ℂ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 100 (sphereEndpointBoxPullback M₀) sphereEndpointAnnuli →
      (∀ j ≤ 100, ∀ z ∈ sphereEndpointAnnuli, ‖iteratedFDeriv ℝ j (sphereEndpointBoxPullback M₀) z‖ ≤ A) →
      ∀ (gap : ℕ) (f g h : SchwartzMap E ℂ),
        let m := sphereEndpointRadianSymbol M₀
        let W := lowEndpointRadianWindows gap
        let B := C*A*‖f.toLp (ENNReal.ofReal 3) volume‖*‖g.toLp (ENNReal.ofReal 3) volume‖*
          ‖h.toLp (ENNReal.ofReal 3) volume‖
        (∀ I : Finset ℤ, ‖radianTrilinearForm (fun p => m p * ∑ j ∈ I, W j p) f g h‖ ≤ B) ∧
        HasSum (fun j : ℤ => radianTrilinearForm (fun p => m p * W j p) f g h)
          (radianTrilinearForm (fun p => m p * ∑' j, W j p) f g h) ∧
        ‖radianTrilinearForm (fun p => m p * ∑' j, W j p) f g h‖ ≤ B := by
  classical
  obtain ⟨χ,C₀,_,hC₀,trace⟩ := exists_sphereEndpoint_angular_series
  obtain ⟨C₁,hC₁,op,compareL2,_,opBound⟩ := exists_integer_low_endpoint_angularLp3_bound 3
  have hK : 0 ≤ modePairSummationConstant := by
    unfold modePairSummationConstant
    exact tsum_nonneg (by intro ab; unfold modePairMajorant; positivity)
  refine ⟨C₁*C₀*modePairSummationConstant,by positivity,?_⟩
  intro M₀ A hA hM jets gap f g h m W B
  let c (ab : FourierModePair) :=
    boxCubeFourierCoefficient 3 (modeIndex ab) (fun z => χ z • sphereEndpointBoxProfile M₀ z)
  obtain ⟨_,hcWeighted,hCoefficient,series⟩ := trace M₀ A hA hM jets
  have hc : Summable (fun ab => ‖c ab‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hcWeighted
    intro ab
    unfold weightedModeCoefficient
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_modePairLoss ab) (norm_nonneg (c ab))
  have onSphere : ∀ᵐ p : Joint ∂(volume : Measure Joint),
      HasSum (fun ab => c ab * sphereMode ab p) (m p) := by
    filter_upwards [nonzero_frequency_pair_ae] with p hp
    exact series p.1 p.2 hp.1 hp.2
  have m_meas : AEStronglyMeasurable m volume := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset FourierModePair))
      (f := fun I p => ∑ ab ∈ I, c ab * sphereMode ab p)
    · intro I
      exact I.aestronglyMeasurable_fun_sum (fun ab _ =>
        ((sphereMode_measurable ab).const_mul (c ab)).aestronglyMeasurable)
    · filter_upwards [onSphere] with p hp using hp
  have m_norm : ∀ᵐ p ∂(volume : Measure Joint), ‖m p‖ ≤ ∑' ab, ‖c ab‖ := by
    filter_upwards [onSphere] with p hp
    rw [← hp.tsum_eq]
    have hs : Summable (fun ab => ‖c ab * sphereMode ab p‖) := by simpa only [norm_mul,sphereMode_norm,mul_one] using hc
    simpa only [norm_mul,sphereMode_norm,mul_one] using norm_tsum_le_tsum_norm hs
  have int_m : Integrable (radianTrilinearWeight m f g h) := by
    have h₀ : Integrable (radianWeight (fun _ => (1 : ℝ)) f g h) := by
      have eq : radianTrilinearWeight (fun _ => (1 : ℂ)) f g h = radianWeight (fun _ => 1) f g h :=
        funext (fun p => one_mul (radianWeight (fun _ => 1) f g h p))
      rw [← eq]
      exact integrable_radianTrilinearWeight_of_bounded (fun _ => (1 : ℂ))
        aestronglyMeasurable_const 1 (fun _ => norm_one.le) f g h
    exact h₀.bdd_mul' (c := ∑' ab, ‖c ab‖) m_meas m_norm
  have allWindows := integral_endpoint_window_series m f g h int_m gap
  have finite (I : Finset ℤ) : ‖radianTrilinearForm (fun p => m p * ∑ j ∈ I, W j p) f g h‖ ≤ B := by
    let V (p : Joint) := ∑ j ∈ I, W j p
    let F := f.toLp (ENNReal.ofReal 3) volume
    let G := g.toLp (ENNReal.ofReal 3) volume
    let H := h.toLp (ENNReal.ofReal 3) volume
    let D := C₁*‖F‖*‖G‖*‖H‖
    have hD : 0 ≤ D := by unfold D; positivity
    have measV : Measurable V := I.measurable_fun_sum (fun j _ => (endpointWindow_continuous gap j).measurable)
    have hsum := radianTrilinearForm_hasSum_of_symbol_expansion
      (fun ab p => c ab * (sphereMode ab p * V p)) (fun p => m p * V p)
      (fun ab => ‖c ab‖ * (3 * Wbound))
      (fun ab => (((sphereMode_measurable ab).mul measV).const_mul _).aestronglyMeasurable)
      (hc.mul_right _) (fun ab p => by
        simp only [norm_mul,sphereMode_norm,one_mul]
        exact mul_le_mul_of_nonneg_left (endpointWindow_partial_norm gap I p) (norm_nonneg _))
      (by
        filter_upwards [onSphere] with p hp
        simpa only [mul_assoc] using hp.mul_right (V p))
      f g h
    let T (ab : FourierModePair) := c ab * radianTrilinearForm (fun p => sphereMode ab p * V p) f g h
    have limit : HasSum T (radianTrilinearForm (fun p => m p * V p) f g h) := by
      simpa only [T,trilinear_const_mul] using hsum
    let n := Fintype.card (↑I : Type)
    let e : (↑I : Type) ≃ Fin n := Fintype.equivFin _
    let j : Fin n ↪ ℤ := e.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
    have reindex (U : ℤ → ℂ) : (∑ i : Fin n, U (j i)) = ∑ i ∈ I, U i := by
      calc
        _ = ∑ i : (↑I : Type), U i.val := e.symm.sum_comp (fun i => U i.val)
        _ = _ := Finset.sum_attach I U
    have point (ab : FourierModePair) : ‖T ab‖ ≤ D * weightedModeCoefficient c ab := by
      have int : Integrable (radianTrilinearWeight (sphereMode ab) f g h) :=
        integrable_radianTrilinearWeight_of_bounded _ (sphereMode_measurable ab).aestronglyMeasurable
          1 (fun p => (sphereMode_norm ab p).le) f g h
      have eqWin := (integral_endpoint_window_series (sphereMode ab) f g h int gap).1 I
      have eq := lowEndpointParaproductLp3_mode_radian 3 ab gap j f g h (op ab.1 F) (op ab.2 G)
        (compareL2 ab.1 f (f.memLp 2 volume) (f.memLp _ volume))
        (compareL2 ab.2 g (g.memLp 2 volume) (g.memLp _ volume))
      let Q (l : ℤ) := radianTrilinearForm (fun p => sphereMode ab p * W l p) f g h
      change lowEndpointParaproductLp3 gap j (op ab.1 F) (op ab.2 G) H = ∑ i : Fin n, Q (j i) at eq
      have eq' : lowEndpointParaproductLp3 gap j (op ab.1 F) (op ab.2 G) H =
          radianTrilinearForm (fun p => sphereMode ab p * V p) f g h :=
        (eq.trans (reindex Q)).trans eqWin
      unfold T
      rw [← eq',norm_mul]
      exact (mul_le_mul_of_nonneg_left (opBound ab gap n j F G H) (norm_nonneg _)).trans_eq
        (by unfold D weightedModeCoefficient; ring)
    have normSum : Summable (fun ab => ‖T ab‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) point (hcWeighted.mul_left D)
    change ‖radianTrilinearForm (fun p => m p * V p) f g h‖ ≤ B
    rw [← limit.tsum_eq]
    calc
      _ ≤ ∑' ab, ‖T ab‖ := norm_tsum_le_tsum_norm normSum
      _ ≤ ∑' ab, D * weightedModeCoefficient c ab := normSum.tsum_le_tsum point (hcWeighted.mul_left D)
      _ = D*(∑' ab, weightedModeCoefficient c ab) := hcWeighted.tsum_mul_left D
      _ ≤ D*(C₀*A*modePairSummationConstant) := mul_le_mul_of_nonneg_left hCoefficient hD
      _ = _ := by unfold D F G H B; ring
  refine ⟨finite,allWindows.2,?_⟩
  have lim := allWindows.2
  change Tendsto (fun I : Finset ℤ => ∑ j ∈ I, radianTrilinearForm (fun p => m p * W j p) f g h) atTop _ at lim
  apply le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp lim)
  intro I
  exact (le_of_eq (congrArg (fun z : ℂ => ‖z‖) (allWindows.1 I))).trans (finite I)

end Burnett.A05
