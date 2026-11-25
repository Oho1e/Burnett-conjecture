import Burnett.Analysis.CubicEnergy.HighSlotCommutator.NarrowReferenceOrbitSymbols
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.NarrowReferenceCoefficientBound
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadianLimit

set_option autoImplicit false
set_option maxHeartbeats 6600000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Filter Finset
open scoped FourierTransform ComplexConjugate Topology ContDiff ENNReal NNReal BigOperators

private theorem τ_pos : 0<tau := mul_pos (by norm_num) Real.pi_pos

private def narrowRadianSpectrum (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero (K := ℝ) (M := E) tau⁻¹ (inv_ne_zero τ_pos.ne')).toContinuousLinearEquiv)
    (SchwartzMap.fourierTransformCLM ℂ f)

private theorem narrowRadianSpectrum_apply (f : SchwartzMap E ℂ) (x : E) :
    narrowRadianSpectrum f x = radianFourier f x := by
  change 𝓕 (f : E → ℂ) (tau⁻¹ • x) = _
  rw [← radianFourier_scaled,smul_smul,mul_inv_cancel₀ τ_pos.ne',one_smul]

private def narrowRadianMajorant (M : ℝ) (f g h : SchwartzMap E ℂ) (p : Joint) : ℝ :=
  (M*SchwartzMap.seminorm ℝ 0 0 (narrowRadianSpectrum h)) *
    (‖narrowRadianSpectrum f p.1‖*((1+‖p.2‖)*‖narrowRadianSpectrum g p.2‖))

private theorem narrowRadianMajorant_integrable (M : ℝ) (f g h : SchwartzMap E ℂ) :
    Integrable (narrowRadianMajorant M f g h) := by
  let G := narrowRadianSpectrum g
  have hw : Integrable (fun p : E => (1+‖p‖)*‖G p‖) := by
    simp only [add_mul,one_mul]
    exact G.integrable.norm.add (by simpa only [pow_one] using G.integrable_pow_mul volume 1)
  rw [Measure.volume_eq_prod E E]
  exact ((narrowRadianSpectrum f).integrable.norm.mul_prod hw).const_mul _

private theorem narrowRadianWeight_measurable (b : Joint → ℂ) (hb : Measurable b)
    (f g h : SchwartzMap E ℂ) : Measurable (radianHighPairWeight b f g h) := by
  have eq : radianHighPairWeight b f g h = fun p : Joint => b p*narrowRadianSpectrum f p.1*
      narrowRadianSpectrum g p.2*conj (narrowRadianSpectrum h (p.2+p.1)) := by
    funext p
    simp only [radianHighPairWeight,narrowRadianSpectrum_apply]
  rw [eq]
  exact ((hb.mul ((narrowRadianSpectrum f).continuous.measurable.comp measurable_fst)).mul
    ((narrowRadianSpectrum g).continuous.measurable.comp measurable_snd)).mul
    (Complex.continuous_conj.measurable.comp
      ((narrowRadianSpectrum h).continuous.measurable.comp (measurable_snd.add measurable_fst)))

private theorem narrowRadianWeight_bound (b : Joint → ℂ) {M : ℝ}
    (hb : ∀ p : Joint, ‖b p‖≤M*(1+‖p.2‖)) (f g h : SchwartzMap E ℂ) (p : Joint) :
    ‖radianHighPairWeight b f g h p‖≤narrowRadianMajorant M f g h p := by
  simp only [radianHighPairWeight,norm_mul,Complex.norm_conj,← narrowRadianSpectrum_apply]
  calc
    _ ≤ (M*(1+‖p.2‖))*‖narrowRadianSpectrum f p.1‖*‖narrowRadianSpectrum g p.2‖*
        SchwartzMap.seminorm ℝ 0 0 (narrowRadianSpectrum h) := by
      refine mul_le_mul ?_ ((narrowRadianSpectrum h).norm_le_seminorm ℝ _) (norm_nonneg _) ?_
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)) (norm_nonneg _)
      · have b0 : 0≤M*(1+‖p.2‖) := (norm_nonneg _).trans (hb p)
        positivity
    _ = _ := by unfold narrowRadianMajorant; ring

private theorem narrowRadianPair_sum_symbol (J : Finset ℕ) (b : ℕ → Joint → ℂ)
    (hb : ∀ j ∈ J, Measurable (b j)) (M : ℕ → ℝ)
    (hM : ∀ j ∈ J, ∀ p, ‖b j p‖≤M j*(1+‖p.2‖)) (f g h : SchwartzMap E ℂ) :
    radianHighPair (fun p => ∑ j ∈ J, b j p) f g h = ∑ j ∈ J, radianHighPair (b j) f g h := by
  have I (j : ℕ) (hj : j∈J) : Integrable (radianHighPairWeight (b j) f g h) :=
    (narrowRadianMajorant_integrable (M j) f g h).mono'
      (narrowRadianWeight_measurable (b j) (hb j hj) f g h).aestronglyMeasurable
      (.of_forall (narrowRadianWeight_bound _ (hM j hj) f g h))
  have eq : radianHighPairWeight (fun p => ∑ j ∈ J, b j p) f g h =
      fun p => ∑ j ∈ J, radianHighPairWeight (b j) f g h p := by
    funext p
    simp only [radianHighPairWeight,sum_mul]
  simp only [radianHighPair,eq,integral_finset_sum J I,smul_sum]

private theorem narrowRadianPair_tendsto (b : ℕ → Joint → ℂ) (limitSymbol : Joint → ℂ)
    (hb : ∀ n, Measurable (b n)) (M : ℝ)
    (hM : ∀ n p, ‖b n p‖≤M*(1+‖p.2‖))
    (hlim : ∀ p, Tendsto (fun n => b n p) atTop (𝓝 (limitSymbol p))) (f g h : SchwartzMap E ℂ) :
    Tendsto (fun n => radianHighPair (b n) f g h) atTop (𝓝 (radianHighPair limitSymbol f g h)) := by
  have hint := tendsto_integral_of_dominated_convergence (μ := (volume : Measure Joint))
    (F := fun n => radianHighPairWeight (b n) f g h) (f := radianHighPairWeight limitSymbol f g h)
    (narrowRadianMajorant M f g h)
    (fun n => (narrowRadianWeight_measurable (b n) (hb n) f g h).aestronglyMeasurable)
    (narrowRadianMajorant_integrable M f g h)
    (fun n => .of_forall (narrowRadianWeight_bound (b n) (hM n) f g h))
    (.of_forall (fun p => ((hlim p).mul_const _).mul_const _ |>.mul_const _))
  exact hint.const_smul (tau^8)⁻¹

private theorem narrowCommutator_sum_symbols (J : Finset ℕ) (b : ℕ → Joint → ℂ)
    (hb : ∀ j ∈ J, Measurable (b j)) (M : ℕ → ℝ)
    (hM : ∀ j ∈ J, ∀ p, ‖b j p‖≤M j*(1+‖p.2‖)) (D f g h : SchwartzMap E ℂ) :
    radianHighCommutatorPair (fun p => ∑ j ∈ J, b j p) (fun x => (D x).re) f g h =
      ∑ j ∈ J, radianHighCommutatorPair (b j) (fun x => (D x).re) f g h := by
  have eq (g : SchwartzMap E ℂ) :
      (fun x : E => ((D x).re : ℂ)*g x) = (gapSchwartzProduct (coefficientRealPart D) g : E → ℂ) :=
    funext fun x => by rw [gapSchwartzProduct_apply,coefficientRealPart_apply]
  simp only [radianHighCommutatorPair,eq,narrowRadianPair_sum_symbol J b hb M hM,sum_sub_distrib]

private theorem narrowCommutator_tendsto (b : ℕ → Joint → ℂ) (limitSymbol : Joint → ℂ)
    (hb : ∀ n, Measurable (b n)) (M : ℝ)
    (hM : ∀ n p, ‖b n p‖≤M*(1+‖p.2‖))
    (hlim : ∀ p, Tendsto (fun n => b n p) atTop (𝓝 (limitSymbol p))) (D f g h : SchwartzMap E ℂ) :
    Tendsto (fun n => radianHighCommutatorPair (b n) (fun x => (D x).re) f g h) atTop
      (𝓝 (radianHighCommutatorPair limitSymbol (fun x => (D x).re) f g h)) := by
  have eq (g : SchwartzMap E ℂ) :
      (fun x : E => ((D x).re : ℂ)*g x) = (gapSchwartzProduct (coefficientRealPart D) g : E → ℂ) :=
    funext fun x => by rw [gapSchwartzProduct_apply,coefficientRealPart_apply]
  simp only [radianHighCommutatorPair,eq]
  exact (narrowRadianPair_tendsto b limitSymbol hb M hM hlim f (gapSchwartzProduct (coefficientRealPart D) g) h).sub
    (narrowRadianPair_tendsto b limitSymbol hb M hM hlim f g (gapSchwartzProduct (coefficientRealPart D) h))

/-- The complete high-frequency orbit of one fixed narrow reference symbol
has the same actual radian commutator estimate as the nested finite sums.
The result removes the operator truncation on this orbit. -/
theorem exists_narrowReferenceOrbit_radian_commutator_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4 ∧ ‖p.1‖≤(1/2)*‖p.2‖) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {s : ℝ}, 0<s → ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (narrowReferenceOrbitSymbol A s) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨M,hM,bound⟩ := exists_narrowReference_unfilteredCoefficient_bound_paper inputL2 A ha hA hBand
  refine ⟨M,hM,?_⟩
  intro D L hD s hs f g h
  have hSupport (p : Joint) (hp : A p≠0) : 1≤‖p.2‖ ∧ ‖p.2‖≤5/4 :=
    ⟨(hBand p hp).1,(hBand p hp).2.1⟩
  obtain ⟨B,hB₀,hB⟩ := exists_narrowReferenceOrbitPartial_order_bound A hA.continuous ha hSupport
  have hcut (n : ℕ) (p : Joint) :
      ‖narrowReferenceOrbitPartial A s n p‖≤B*(1+‖p.2‖) :=
    (hB hs n p).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hB₀)
  let b k := radianHighReferenceBlock A (dyadicCoefficientScale s k)
  have hb k : Measurable (b k) := by
    have c : Continuous (b k) := by
      unfold b radianHighReferenceBlock
      exact continuous_const.smul (hA.continuous.comp (continuous_const.smul continuous_id))
    exact c.measurable
  have hP (n : ℕ) : Measurable (narrowReferenceOrbitPartial A s n) :=
    measurable_sum _ (fun k _ => hb k)
  obtain ⟨p₀,hU⟩ := hA.continuous.norm.exists_forall_ge_of_hasCompactSupport ha.norm
  let U := ‖A p₀‖
  have U0 : 0≤U := norm_nonneg _
  have Bₖ (k : ℕ) (p : Joint) :
      ‖b k p‖≤(dyadicCoefficientScale s k)⁻¹*U*(1+‖p.2‖) := by
    let r := dyadicCoefficientScale s k
    have hr : 0<r := dyadicCoefficientScale_pos hs k
    change ‖r⁻¹ • A ((r/tau) • p)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (mul_le_mul_of_nonneg_left (hU _) (inv_nonneg.mpr hr.le)).trans
      (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (norm_nonneg _)))
  have conv := narrowCommutator_tendsto (narrowReferenceOrbitPartial A s) (narrowReferenceOrbitSymbol A s)
    hP B hcut (narrowReferenceOrbitPartial_tendsto A hSupport hs) D f g h
  refine le_of_tendsto' (continuous_enorm.continuousAt.tendsto.comp conv) fun n => ?_
  change ‖radianHighCommutatorPair (fun p => ∑ k ∈ range (n+1), b k p) (fun x => (D x).re) f g h‖ₑ ≤ _
  rw [narrowCommutator_sum_symbols _ b (fun k _ => hb k) _ (fun k _ => Bₖ k)]
  have eq : (∑ k ∈ range (n+1), radianHighCommutatorPair (b k) (fun x => (D x).re) f g h) =
      referenceUnfilteredCoefficientPairSum A D f g h (dyadicCoefficientScale s n) (range (n+1)) := by
    unfold referenceUnfilteredCoefficientPairSum
    let F k := radianHighCommutatorPair
      (radianHighReferenceBlock A (dyadicScale (dyadicCoefficientScale s n) k)) (fun x => (D x).re) f g h
    calc
      _ = ∑ k ∈ range (n+1), F (n+1-1-k) := by
        refine sum_congr rfl fun k hk => ?_
        have ks : k≤n := Nat.le_of_lt_succ (mem_range.mp hk)
        dsimp only [F]
        rw [show n+1-1-k=n-k by omega,narrowReferenceOrbit_reindex s (Nat.sub_le _ _)]
        simp only [Nat.sub_sub_self ks,b]
      _ = _ := sum_range_reflect F (n+1)
  rw [eq]
  exact bound D L hD (dyadicCoefficientScale_pos hs n) (n+1) f g h

theorem exists_narrowReferenceOrbit_radian_commutator_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4 ∧ ‖p.1‖≤(1/2)*‖p.2‖) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {s : ℝ}, 0<s → ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (narrowReferenceOrbitSymbol A s) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_narrowReferenceOrbit_radian_commutator_bound_paper false A ha hA hBand

end Burnett.A06
