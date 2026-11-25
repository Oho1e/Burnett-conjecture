import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Set MeasureTheory
open scoped ContDiff Interval

abbrev CyclicFrequency := EuclideanSpace ℝ (Fin 4)

def cyclicWeight (a : CyclicFrequency → ℝ) (p q r : CyclicFrequency) : ℝ :=
  a p + a q + a r

def cyclicExtension (a : CyclicFrequency → ℝ) (direction z θ : CyclicFrequency) : ℝ :=
  a direction - ∫ t in (0 : ℝ)..1, (fderiv ℝ a (θ + t • z)) direction

def cyclicExtensionDomain : Set (CyclicFrequency × CyclicFrequency × CyclicFrequency) :=
  {x | x.1 ≠ 0 ∧ ‖x.2.1‖ < ‖x.2.2‖}

theorem isOpen_cyclicExtensionDomain : IsOpen cyclicExtensionDomain := by
  exact (isClosed_singleton.isOpen_compl.preimage continuous_fst).inter
    (isOpen_lt continuous_snd.fst.norm continuous_snd.snd.norm)

theorem cyclic_segment_ne_zero (z θ : CyclicFrequency) (hzθ : ‖z‖ < ‖θ‖) :
    ∀ t ∈ Icc (0 : ℝ) 1, θ + t • z ≠ 0 := by
  intro t ht heq
  have hθ : θ = -(t • z) := by
    calc
      θ = θ + t • z - t • z := by abel
      _ = -(t • z) := by rw [heq, zero_sub]
  have hle : ‖θ‖ ≤ ‖z‖ := by
    calc
      ‖θ‖ = t * ‖z‖ := by rw [hθ, norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = _ := one_mul _
  exact (not_le_of_gt hzθ) hle

theorem cyclic_segment_integral_fderiv (a : CyclicFrequency → ℝ)
    (ha : ContDiffOn ℝ 1 a ({0}ᶜ : Set CyclicFrequency)) (z θ : CyclicFrequency)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, θ + t • z ≠ 0) :
    (∫ t in (0 : ℝ)..1, (fderiv ℝ a (θ + t • z)) z) = a (θ + z) - a θ := by
  have hopen : IsOpen ({0}ᶜ : Set CyclicFrequency) := isClosed_singleton.isOpen_compl
  have hmid : MapsTo (fun t : ℝ => θ + t • z) (Icc (0 : ℝ) 1)
      ({0}ᶜ : Set CyclicFrequency) := fun t ht => hseg t ht
  have hc : Continuous (fun t : ℝ => θ + t • z) := continuous_const.add
    (continuous_id.smul continuous_const)
  have hcd := (ha.continuousOn_fderiv_of_isOpen hopen le_rfl).comp hc.continuousOn hmid
  have hintegrable : IntervalIntegrable (fun t => (fderiv ℝ a (θ + t • z)) z) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hcd.clm_apply continuousOn_const
  have hderiv (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => a (θ + t • z)) ((fderiv ℝ a (θ + t • z)) z) t := by
    have hLine : HasDerivAt (fun t : ℝ => θ + t • z) z t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const z).const_add θ
    rw [uIcc_of_le zero_le_one] at ht
    have hd := ((ha.contDiffAt (hopen.mem_nhds (hmid ht))).differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt t hLine
  simpa only [zero_smul, one_smul, add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable

theorem cyclicExtension_zero (a : CyclicFrequency → ℝ) (direction θ : CyclicFrequency) :
    cyclicExtension a direction 0 θ = a direction - (fderiv ℝ a θ) direction := by
  simp [cyclicExtension, intervalIntegral.integral_const]

theorem cyclicWeight_div_norm_eq_extension (a : CyclicFrequency → ℝ)
    (hodd : ∀ x : CyclicFrequency, x ≠ 0 → a (-x) = -a x)
    (hscale : ∀ c : ℝ, 0 < c → ∀ x : CyclicFrequency, x ≠ 0 → a (c • x) = c * a x)
    (ha : ContDiffOn ℝ 1 a ({0}ᶜ : Set CyclicFrequency))
    (p q r : CyclicFrequency) (htri : p + q + r = 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖q‖⁻¹ • q + t • (‖q‖⁻¹ • p) ≠ 0) :
    cyclicWeight a p q r / ‖p‖ =
      cyclicExtension a (‖p‖⁻¹ • p) (‖q‖⁻¹ • p) (‖q‖⁻¹ • q) := by
  let lp : ℝ := ‖p‖
  let lq : ℝ := ‖q‖
  let direction : CyclicFrequency := lp⁻¹ • p
  let θ : CyclicFrequency := lq⁻¹ • q
  let z : CyclicFrequency := lq⁻¹ • p
  change cyclicWeight a p q r / lp = cyclicExtension a direction z θ
  have hp0 : 0 < lp := norm_pos_iff.mpr hp
  have hq0 : 0 < lq := norm_pos_iff.mpr hq
  have hDirectionp : lp • direction = p := smul_inv_smul₀ hp0.ne' p
  have hθq : lq • θ = q := smul_inv_smul₀ hq0.ne' q
  have hzq : lq • z = p := smul_inv_smul₀ hq0.ne' p
  have hDirection : direction ≠ 0 := smul_ne_zero (inv_ne_zero hp0.ne') hp
  have hθ : θ ≠ 0 := smul_ne_zero (inv_ne_zero hq0.ne') hq
  have hθz : θ + z ≠ 0 := by
    have h := hseg 1 (by norm_num)
    simpa only [one_smul] using h
  have hθzScale : lq • (θ + z) = p + q := by rw [smul_add, hθq, hzq, add_comm]
  have hpq : p + q ≠ 0 := hθzScale ▸ smul_ne_zero hq0.ne' hθz
  have hr : r = -(p + q) := by
    calc
      r = p + q + r - (p + q) := by abel
      _ = -(p + q) := by rw [htri, zero_sub]
  have hap : a p = lp * a direction := hDirectionp ▸ hscale lp hp0 direction hDirection
  have haq : a q = lq * a θ := hθq ▸ hscale lq hq0 θ hθ
  have har : a r = -(lq * a (θ + z)) := by
    rw [hr, hodd _ hpq, ← hθzScale, hscale lq hq0 _ hθz]
  have hzDirection : z = (lp / lq) • direction := by
    calc
      z = lq⁻¹ • (lp • direction) := by rw [hDirectionp]
      _ = _ := by rw [smul_smul, div_eq_mul_inv, mul_comm]
  have hFTC := cyclic_segment_integral_fderiv a ha z θ hseg
  have hScaled : (lp / lq) * (∫ t in (0 : ℝ)..1, (fderiv ℝ a (θ + t • z)) direction) =
      a (θ + z) - a θ := by
    rw [← intervalIntegral.integral_const_mul]
    convert hFTC using 1
    apply intervalIntegral.integral_congr
    intro t _
    calc
      (lp / lq) * (fderiv ℝ a (θ + t • z)) direction =
          (fderiv ℝ a (θ + t • z)) ((lp / lq) • direction) := by
        simpa only [smul_eq_mul] using
          ((fderiv ℝ a (θ + t • z)).map_smul (lp / lq) direction).symm
      _ = _ := congrArg (fderiv ℝ a (θ + t • z)) hzDirection.symm
  have hDiff : lq * (a (θ + z) - a θ) =
      lp * (∫ t in (0 : ℝ)..1, (fderiv ℝ a (θ + t • z)) direction) := by
    rw [← hScaled]
    field_simp
  rw [cyclicWeight, hap, haq, har, cyclicExtension]
  apply (div_eq_iff hp0.ne').mpr
  linarith only [hDiff]

theorem cyclicWeight_div_norm_eq_extension_of_low (a : CyclicFrequency → ℝ)
    (hodd : ∀ x : CyclicFrequency, x ≠ 0 → a (-x) = -a x)
    (hscale : ∀ c : ℝ, 0 < c → ∀ x : CyclicFrequency, x ≠ 0 → a (c • x) = c * a x)
    (ha : ContDiffOn ℝ 1 a ({0}ᶜ : Set CyclicFrequency))
    (p q r : CyclicFrequency) (htri : p + q + r = 0) (hp : p ≠ 0)
    (κ : ℝ) (hκ' : κ < 1 / 16) (hlow : ‖p‖ ≤ 2 * κ * ‖q‖) :
    cyclicWeight a p q r / ‖p‖ =
      cyclicExtension a (‖p‖⁻¹ • p) (‖q‖⁻¹ • p) (‖q‖⁻¹ • q) ∧
    (‖p‖⁻¹ • p, ‖q‖⁻¹ • p, ‖q‖⁻¹ • q) ∈ cyclicExtensionDomain := by
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hq : q ≠ 0 := by
    intro heq
    rw [heq, norm_zero, mul_zero] at hlow
    exact (not_le_of_gt hp0) hlow
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hpq : ‖p‖ < ‖q‖ := hlow.trans_lt
    (by simpa only [one_mul] using mul_lt_mul_of_pos_right (by linarith : 2 * κ < 1) hq0)
  have hNorm : ‖‖q‖⁻¹ • p‖ < ‖‖q‖⁻¹ • q‖ := by
    simp only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hq0.le)]
    exact mul_lt_mul_of_pos_left hpq (inv_pos.mpr hq0)
  exact ⟨cyclicWeight_div_norm_eq_extension a hodd hscale ha p q r htri hp hq
      (cyclic_segment_ne_zero _ _ hNorm),
    smul_ne_zero (inv_ne_zero hp0.ne') hp, hNorm⟩

end Burnett.Analysis.TransportWardSymbol


noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Set MeasureTheory Filter
open scoped ContDiff Topology Interval

set_option maxHeartbeats 1200000 in
private theorem hasFDerivAt_unitInterval_parametric
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : Set E) (U : Set (E × ℝ)) (hS : IsOpen S) (hU : IsOpen U)
    (hrect : S ×ˢ Icc (0 : ℝ) 1 ⊆ U) (f : E × ℝ → F)
    (hf : ContDiffOn ℝ 1 f U) (x : E) (hx : x ∈ S) :
    HasFDerivAt
      (fun y => ∫ t in Icc (0 : ℝ) 1, f (y, t))
      (∫ t in Icc (0 : ℝ) 1, (fderiv ℝ f (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let J := Icc (0 : ℝ) 1
  let D : E × ℝ → E →L[ℝ] F :=
    fun y => (fderiv ℝ f y).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : ContinuousOn D U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const
  obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp hS x hx
  let δ := radius / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hclosed : Metric.closedBall x δ ⊆ S :=
    (Metric.closedBall_subset_ball (by dsimp [δ]; linarith)).trans hball
  have hsmall : Metric.ball x δ ⊆ S := Metric.ball_subset_closedBall.trans hclosed
  have hK : IsCompact (Metric.closedBall x δ ×ˢ J) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKsub : Metric.closedBall x δ ×ˢ J ⊆ U := by
    intro y hy
    exact hrect ⟨hclosed hy.1, hy.2⟩
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hD.norm.mono hKsub)
  have hslice (y : E) (hy : y ∈ S) :
      Integrable (fun t : ℝ => f (y, t)) (volume.restrict J) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => hrect ⟨hy, ht⟩)
  have hDslice : Integrable (fun t : ℝ => D (x, t)) (volume.restrict J) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => hrect ⟨hx, ht⟩)
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun t : ℝ => f (y, t)) (volume.restrict J) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact (hslice y hy).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict J, ∀ y ∈ Metric.ball x δ, ‖D (y, t)‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht y hy
    exact hM (mem_image_of_mem _ ⟨Metric.ball_subset_closedBall hy, ht⟩)
  have hdiff : ∀ᵐ t ∂volume.restrict J, ∀ y ∈ Metric.ball x δ,
      HasFDerivAt (fun z => f (z, t)) (D (y, t)) y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht y hy
    have hyU : (y, t) ∈ U := hrect ⟨hsmall hy, ht⟩
    have hF := ((hf.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)).hasFDerivAt
    have hPair : HasFDerivAt (fun z : E => (z, t)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
      simpa using (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.const_add (0, t)
    exact hF.comp y hPair
  have hMInt : Integrable (fun _ : ℝ => M) (volume.restrict J) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume.restrict J)
    (F := fun y t => f (y, t)) (F' := fun y t => D (y, t)) (bound := fun _ => M)
    hδ hmeas (hslice x hx) hDslice.aestronglyMeasurable hbound hMInt hdiff

private theorem contDiffOn_unitInterval_parametric_nat
    (n : ℕ) {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : Set E) (U : Set (E × ℝ)) (hS : IsOpen S) (hU : IsOpen U)
    (hrect : S ×ˢ Icc (0 : ℝ) 1 ⊆ U)
    (f : E × ℝ → F) (hf : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => ∫ t in Icc (0 : ℝ) 1, f (x, t)) S := by
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    exact (hasFDerivAt_unitInterval_parametric S U hS hU hrect f
      (by simpa only [Nat.cast_zero, zero_add] using hf) x hx).continuousAt.continuousWithinAt
  | succ n ih =>
    have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (le_add_of_nonneg_left (zero_le _))
    have hd x (hx : x ∈ S) := hasFDerivAt_unitInterval_parametric S U hS hU hrect f hf1 x hx
    let D : E × ℝ → E →L[ℝ] F :=
      fun y => (fderiv ℝ f y).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) D U := by
      apply ContDiffOn.clm_comp _ contDiffOn_const
      apply hf.fderiv_of_isOpen hU
      rw [Nat.cast_succ]
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih D hD).congr (fun x hx => (hd x hx).fderiv)

theorem contDiffOn_cyclicExtension (a : CyclicFrequency → ℝ)
    (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set CyclicFrequency)) :
    ContDiffOn ℝ ∞ (fun x : CyclicFrequency × CyclicFrequency × CyclicFrequency =>
      cyclicExtension a x.1 x.2.1 x.2.2) cyclicExtensionDomain := by
  let path : (CyclicFrequency × CyclicFrequency × CyclicFrequency) × ℝ → CyclicFrequency :=
    fun x => x.1.2.2 + x.2 • x.1.2.1
  have hpath : ContDiff ℝ ∞ path := by dsimp [path]; fun_prop
  have hOpen : IsOpen ({0}ᶜ : Set CyclicFrequency) := isClosed_singleton.isOpen_compl
  let U := path ⁻¹' ({0}ᶜ : Set CyclicFrequency)
  have hU : IsOpen U := hOpen.preimage hpath.continuous
  have hrect : cyclicExtensionDomain ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    intro x hx
    exact cyclic_segment_ne_zero _ _ hx.1.2 x.2 hx.2
  let f : (CyclicFrequency × CyclicFrequency × CyclicFrequency) × ℝ → ℝ :=
    fun x => (fderiv ℝ a (path x)) x.1.1
  have hD := ((contDiffOn_infty_iff_fderiv_of_isOpen hOpen).mp ha).2
  have hf : ContDiffOn ℝ ∞ f U :=
    (hD.comp hpath.contDiffOn
      (fun _ hy => hy)).clm_apply (contDiff_fst.comp contDiff_fst).contDiffOn
  have hInt : ContDiffOn ℝ ∞
      (fun x => ∫ t in Icc (0 : ℝ) 1, f (x, t)) cyclicExtensionDomain := by
    rw [contDiffOn_infty]
    intro n
    apply contDiffOn_unitInterval_parametric_nat n _ U isOpen_cyclicExtensionDomain hU hrect f
    simpa only [Nat.cast_succ] using contDiffOn_infty.mp hf (n + 1)
  have haFirst : ContDiffOn ℝ ∞
      (fun x : CyclicFrequency × CyclicFrequency × CyclicFrequency => a x.1) cyclicExtensionDomain :=
    ha.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  apply (haFirst.sub hInt).congr
  intro x _
  rw [cyclicExtension, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

theorem cyclicExtension_iteratedFDeriv_bound_on_compact (a : CyclicFrequency → ℝ)
    (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set CyclicFrequency)) (n : ℕ)
    (K : Set (CyclicFrequency × CyclicFrequency × CyclicFrequency))
    (hK : IsCompact K) (hsub : K ⊆ cyclicExtensionDomain) :
    ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ n
      (fun y => cyclicExtension a y.1 y.2.1 y.2.2) x‖ ≤ C := by
  let f : CyclicFrequency × CyclicFrequency × CyclicFrequency → ℝ :=
    fun y => cyclicExtension a y.1 y.2.1 y.2.2
  have hDiff := contDiffOn_cyclicExtension a ha
  have hWithin := (contDiffOn_infty.mp hDiff n).continuousOn_iteratedFDerivWithin
    (le_rfl : (n : WithTop ℕ∞) ≤ n) isOpen_cyclicExtensionDomain.uniqueDiffOn
  have hGlobal : ContinuousOn (iteratedFDeriv ℝ n f) cyclicExtensionDomain :=
    hWithin.congr (fun _ hx => (iteratedFDerivWithin_of_isOpen n isOpen_cyclicExtensionDomain hx).symm)
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hGlobal.norm.mono hsub)
  exact ⟨C, fun x hx => hC (mem_image_of_mem _ hx)⟩

end Burnett.Analysis.TransportWardSymbol


noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Set
open scoped ContDiff Topology

def cyclicLowCompact (κ : ℝ) : Set (CyclicFrequency × CyclicFrequency × CyclicFrequency) :=
  Metric.sphere (0 : CyclicFrequency) 1 ×ˢ
    (Metric.closedBall (0 : CyclicFrequency) (2 * κ) ×ˢ Metric.sphere (0 : CyclicFrequency) 1)

theorem isCompact_cyclicLowCompact (κ : ℝ) : IsCompact (cyclicLowCompact κ) := by
  exact (isCompact_sphere _ _).prod ((isCompact_closedBall _ _).prod (isCompact_sphere _ _))

theorem cyclicLowCompact_subset_domain (κ : ℝ) (hκ : κ < 1 / 16) :
    cyclicLowCompact κ ⊆ cyclicExtensionDomain := by
  intro x hx
  simp only [cyclicLowCompact, Set.mem_prod, Metric.mem_sphere, Metric.mem_closedBall,
    dist_zero_right] at hx
  refine ⟨fun he => ?_, ?_⟩
  · simpa [he] using hx.1
  · rw [hx.2.2]
    exact hx.2.1.trans_lt (by linarith)

private theorem norm_cyclic_normalized (x : CyclicFrequency) (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

theorem cyclicNormalized_mem_lowCompact (p q : CyclicFrequency) (hp : p ≠ 0)
    (κ : ℝ) (hlow : ‖p‖ ≤ 2 * κ * ‖q‖) :
    (‖p‖⁻¹ • p, ‖q‖⁻¹ • p, ‖q‖⁻¹ • q) ∈ cyclicLowCompact κ := by
  have hq : q ≠ 0 := by
    intro he
    rw [he, norm_zero, mul_zero] at hlow
    exact (not_le_of_gt (norm_pos_iff.mpr hp)) hlow
  have hz : ‖‖q‖⁻¹ • p‖ ≤ 2 * κ := by
    have hq0 := norm_pos_iff.mpr hq
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hq0.le)]
    calc
      ‖q‖⁻¹ * ‖p‖ ≤ ‖q‖⁻¹ * (2 * κ * ‖q‖) :=
        mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hq0.le)
      _ = _ := by field_simp
  simpa only [cyclicLowCompact, Set.mem_prod, Metric.mem_sphere, Metric.mem_closedBall,
    dist_zero_right] using And.intro (norm_cyclic_normalized p hp) ⟨hz, norm_cyclic_normalized q hq⟩

theorem cyclicWeight_linear_bound_of_low (a : CyclicFrequency → ℝ)
    (hodd : ∀ x : CyclicFrequency, x ≠ 0 → a (-x) = -a x)
    (hscale : ∀ c : ℝ, 0 < c → ∀ x : CyclicFrequency, x ≠ 0 → a (c • x) = c * a x)
    (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set CyclicFrequency))
    (κ : ℝ) (hκ : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q r : CyclicFrequency,
      p + q + r = 0 → p ≠ 0 → ‖p‖ ≤ 2 * κ * ‖q‖ → |cyclicWeight a p q r| ≤ C * ‖p‖ := by
  have hBound := (isCompact_cyclicLowCompact κ).bddAbove_image
    ((contDiffOn_cyclicExtension a ha).continuousOn.norm.mono (cyclicLowCompact_subset_domain κ hκ))
  obtain ⟨C, hC⟩ := hBound
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p q r htri hp hlow
  have hExt := (cyclicWeight_div_norm_eq_extension_of_low a hodd hscale
    (by simpa using contDiffOn_infty.mp ha 1) p q r htri hp κ hκ hlow).1
  have hNorm : ‖cyclicWeight a p q r / ‖p‖‖ ≤ C := by
    rw [hExt]
    exact hC (mem_image_of_mem _ (cyclicNormalized_mem_lowCompact p q hp κ hlow))
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)] at hNorm
  exact (div_le_iff₀ (norm_pos_iff.mpr hp)).mp (hNorm.trans (le_max_left _ _))

end Burnett.Analysis.TransportWardSymbol
