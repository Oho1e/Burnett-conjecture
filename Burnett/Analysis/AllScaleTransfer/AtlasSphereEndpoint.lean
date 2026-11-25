import Burnett.Analysis.AllScaleTransfer.SphereEndpointRadian
import Burnett.Analysis.AllScaleTransfer.ActualAtlasBoxProfiles
import Burnett.Analysis.AllScaleTransfer.PositiveRatioTrace

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open Burnett.Analysis.LowRatio (Angles Point Window zeroRatioTraceExtension
  zeroRatioTraceExtension_jets_of_oneSidedC100)
open scoped ContDiff ENNReal Topology Nat

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private def normalizedSphereBoxPair (z : BoxSpace) : FrequencyPair :=
  (endpointDirection (firstInput z), endpointDirection (secondInput z))

private theorem endpointDirection_unit {p : E} (hp : p ≠ 0) : ‖endpointDirection p‖ = 1 :=
  (mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp))

/-- The same finite atlas on the original normalized annuli controls the
actual zero-ratio trace on the full off-axis Fourier box neighborhood.
The chart agreements refer to a single common trace. -/
theorem exists_sphereEndpoint_box_bound_of_atlas {ι : Type*} [Fintype ι]
    (V : ι → Set FrequencyPair) (U : ι → Set Angles)
    (angular : ι → FrequencyPair → Angles)
    (hV : ∀ i, IsOpen (V i)) (hU : ∀ i, IsOpen (U i))
    (hCover : ({p : E | (1 / 2 : ℝ) ≤ ‖p‖ ∧ ‖p‖ ≤ 2} ×ˢ
      {q : E | (1 / 2 : ℝ) ≤ ‖q‖ ∧ ‖q‖ ≤ 2}) ⊆ ⋃ i, V i)
    (hAngular : ∀ i, ContDiffOn ℝ ∞ (angular i) (V i))
    (hMap : ∀ i, MapsTo (angular i) (V i) (U i))
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ι → Point → ℂ) (M₀ : Joint → ℂ) (A : ℝ), 0 ≤ A →
      (∀ i, ContDiffOn ℝ 100 (M i) (U i ×ˢ Ico (0 : ℝ) b)) →
      (∀ i n, n ≤ 100 → ∀ z ∈ U i ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (M i) (U i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) →
      (∀ i pq, pq ∈ V i →
        M₀ (endpointDirection pq.1, endpointDirection pq.2) = M i (angular i pq, 0)) →
      ContDiffOn ℝ 100 (sphereEndpointBoxPullback M₀) sphereEndpointAnnuli ∧
      ∀ n ≤ 100, ∀ z ∈ sphereEndpointAnnuli,
        ‖iteratedFDeriv ℝ n (sphereEndpointBoxPullback M₀) z‖ ≤ C * A := by
  classical
  let D : Set BoxSpace := {z | firstInput z ≠ 0 ∧ secondInput z ≠ 0}
  let N := normalizedSphereBoxPair
  have f : ContDiff ℝ ∞ firstInput := boxToPair.toContinuousLinearMap.contDiff.fst
  have g : ContDiff ℝ ∞ secondInput := boxToPair.toContinuousLinearMap.contDiff.snd
  have openD : IsOpen D := (isOpen_ne_fun f.continuous continuous_const).inter
    (isOpen_ne_fun g.continuous continuous_const)
  have smoothN : ContDiffOn ℝ ∞ N D :=
    (endpointDirection_contDiffOn.comp f.contDiffOn (fun _ hz => hz.1)).prodMk
      (endpointDirection_contDiffOn.comp g.contDiffOn (fun _ hz => hz.2))
  let O (i : ι) : Set BoxSpace := D ∩ N ⁻¹' (V i)
  have openO (i : ι) : IsOpen (O i) := smoothN.continuousOn.isOpen_inter_preimage openD (hV i)
  let band : Set E := {x | (1 / 4 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 3}
  let K := boxToPair.symm '' (band ×ˢ band)
  have compactBand : IsCompact band :=
    (isCompact_closedBall (0 : E) 3).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun _ hx => mem_closedBall_zero_iff.mpr hx.2)
  have compactK : IsCompact K := (compactBand.prod compactBand).image boxToPair.symm.continuous
  have inK (z : BoxSpace) : z ∈ K ↔ (firstInput z, secondInput z) ∈ band ×ˢ band := by
    constructor
    · rintro ⟨pq,hpq,he⟩
      change boxToPair z ∈ band ×ˢ band
      rwa [← he,boxToPair.apply_symm_apply]
    · intro hz
      exact ⟨boxToPair z,hz,boxToPair.symm_apply_apply z⟩
  have K_axis : K ⊆ D := by
    intro z hz
    have h := (inK z).mp hz
    have hpos : (0 : ℝ) < 1 / 4 := by norm_num
    exact ⟨norm_pos_iff.mp (hpos.trans_le h.1.1),norm_pos_iff.mp (hpos.trans_le h.2.1)⟩
  have cover : K ⊆ ⋃ i, O i := by
    intro z hz
    have hzD := K_axis hz
    have h₁ := endpointDirection_unit hzD.1
    have h₂ := endpointDirection_unit hzD.2
    have hn : N z ∈ ({p : E | (1 / 2 : ℝ) ≤ ‖p‖ ∧ ‖p‖ ≤ 2} ×ˢ
        {q : E | (1 / 2 : ℝ) ≤ ‖q‖ ∧ ‖q‖ ≤ 2}) := by
      change ((1 / 2 : ℝ) ≤ ‖endpointDirection (firstInput z)‖ ∧ ‖endpointDirection (firstInput z)‖ ≤ 2) ∧
        ((1 / 2 : ℝ) ≤ ‖endpointDirection (secondInput z)‖ ∧ ‖endpointDirection (secondInput z)‖ ≤ 2)
      rw [h₁,h₂]
      norm_num
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hCover hn)
    exact mem_iUnion.mpr ⟨i,hzD,hi⟩
  obtain ⟨ρ,_,_,_,supportρ,sumρ,_⟩ := exists_box_chart_weights compactK O openO cover 5
  let L (i : ι) := K ∩ tsupport (ρ i)
  have compactL (i : ι) : IsCompact (L i) := compactK.inter_right (isClosed_tsupport (ρ i))
  have LO (i : ι) : L i ⊆ O i := fun _ hz => supportρ i hz.2
  have select (z : BoxSpace) (hz : z ∈ K) : ∃ i, z ∈ L i := by
    have existsMode : ∃ i, ρ i z ≠ 0 := by
      by_contra! hn
      exact zero_ne_one (by simpa only [hn,Finset.sum_const_zero] using sumρ z hz)
    obtain ⟨i,hi⟩ := existsMode
    exact ⟨i,hz,subset_tsupport _ (Function.mem_support.mpr hi)⟩
  have target_inK : sphereEndpointAnnuli ⊆ K := by
    intro z hz
    exact (inK z).mpr ⟨⟨hz.1.le,hz.2.1.le⟩,⟨hz.2.2.1.le,hz.2.2.2.le⟩⟩
  let Φ (i : ι) (z : BoxSpace) : Point := (angular i (N z),0)
  let W (i : ι) := Window (U i) (-1) 1
  have openW (i : ι) : IsOpen (W i) := (hU i).prod isOpen_Ioo
  have mapΦ (i : ι) : MapsTo (Φ i) (O i) (W i) :=
    fun _ hz => ⟨hMap i hz.2,by norm_num,by norm_num⟩
  have smoothΦ (i : ι) : ContDiffOn ℝ ∞ (Φ i) (O i) :=
    ((hAngular i).comp (smoothN.mono inter_subset_left) (fun _ hz => hz.2)).prodMk contDiffOn_const
  choose B hB jets using fun i => exists_compact_contDiffOn_jet_bound (compactL i) (openO i) (LO i) (smoothΦ i) 100
  let E₀ := 1 + ∑ i, B i
  have hE : 1 ≤ E₀ := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hE0 : 0 ≤ E₀ := zero_le_one.trans hE
  let C : ℝ := ((100 ! : ℕ) : ℝ) * E₀^100
  refine ⟨C,by positivity,?_⟩
  intro M M₀ A hA hM hJets agree
  let Z (i : ι) := zeroRatioTraceExtension (M i)
  have extData (i : ι) := zeroRatioTraceExtension_jets_of_oneSidedC100 (hU i) hb (-1) 1
    (M i) A hA (hM i) (hJets i)
  have smoothPhi100 (i : ι) : ContDiffOn ℝ 100 (Φ i) (O i) :=
    (smoothΦ i).of_le (WithTop.coe_le_coe.mpr le_top)
  have eqChart (i : ι) : EqOn (sphereEndpointBoxPullback M₀) (Z i ∘ Φ i) (O i) := by
    intro z hz
    have unit₁ := endpointDirection_unit hz.1.1
    have unit₂ := endpointDirection_unit hz.1.2
    have dir₁ : endpointDirection (N z).1 = (N z).1 := by
      rw [endpointDirection,show ‖(N z).1‖ = 1 from unit₁,inv_one,one_smul]
    have dir₂ : endpointDirection (N z).2 = (N z).2 := by
      rw [endpointDirection,show ‖(N z).2‖ = 1 from unit₂,inv_one,one_smul]
    have eq := agree i (N z) hz.2
    rw [dir₁,dir₂] at eq
    exact eq
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨i,hi⟩ := select z (target_inK hz)
    have ho := LO i hi
    have loc : ContDiffAt ℝ 100 (Z i ∘ Φ i) z :=
      ((extData i).1.comp (smoothPhi100 i) (mapΦ i)).contDiffAt ((openO i).mem_nhds ho)
    exact (loc.congr_of_eventuallyEq (by
      filter_upwards [(openO i).mem_nhds ho] with y hy
      exact eqChart i hy)).contDiffWithinAt
  · intro n hn z hz
    obtain ⟨i,hi⟩ := select z (target_inK hz)
    have ho := LO i hi
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast hn
    have bi : B i ≤ E₀ :=
      (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one)
    rw [← iteratedFDerivWithin_of_isOpen n (openO i) ho,iteratedFDerivWithin_congr (eqChart i) ho n]
    have bound := norm_iteratedFDerivWithin_comp_le (extData i).1 (smoothPhi100 i) hn'
      (openW i).uniqueDiffOn (openO i).uniqueDiffOn (mapΦ i) ho (C := A) (D := E₀)
      (fun j hj => by
        rw [iteratedFDerivWithin_of_isOpen j (openW i) (mapΦ i ho)]
        exact (extData i).2 j (hj.trans hn) _ (mapΦ i ho))
      (fun j hj hjn => by
        rw [iteratedFDerivWithin_of_isOpen j (openO i) ho]
        exact ((jets i j (hjn.trans hn) z hi).trans bi).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hE hj))
    refine bound.trans ?_
    calc
      _ ≤ ((100 ! : ℕ) : ℝ) * A * E₀^100 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hn) hA)
          (pow_le_pow_right₀ hE hn) (pow_nonneg hE0 _) (by positivity)
      _ = C*A := by unfold C; ring

/-- The original one-sided atlas data supplies the uncapped zero-ratio
Fourier estimate, uniformly for finite radial selections and the full sum. -/
theorem exists_sphereEndpoint_radian_bound_of_atlas {ι : Type*} [Fintype ι]
    (V : ι → Set FrequencyPair) (U : ι → Set Angles)
    (angular : ι → FrequencyPair → Angles)
    (hV : ∀ i, IsOpen (V i)) (hU : ∀ i, IsOpen (U i))
    (hCover : ({p : E | (1 / 2 : ℝ) ≤ ‖p‖ ∧ ‖p‖ ≤ 2} ×ˢ
      {q : E | (1 / 2 : ℝ) ≤ ‖q‖ ∧ ‖q‖ ≤ 2}) ⊆ ⋃ i, V i)
    (hAngular : ∀ i, ContDiffOn ℝ ∞ (angular i) (V i))
    (hMap : ∀ i, MapsTo (angular i) (V i) (U i))
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ι → Point → ℂ) (M₀ : Joint → ℂ) (A : ℝ), 0 ≤ A →
      (∀ i, ContDiffOn ℝ 100 (M i) (U i ×ˢ Ico (0 : ℝ) b)) →
      (∀ i n, n ≤ 100 → ∀ z ∈ U i ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (M i) (U i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) →
      (∀ i pq, pq ∈ V i →
        M₀ (endpointDirection pq.1, endpointDirection pq.2) = M i (angular i pq, 0)) →
      ∀ (gap : ℕ) (f g h : SchwartzMap E ℂ),
        let m := sphereEndpointRadianSymbol M₀
        let W := lowEndpointRadianWindows gap
        let B := C*A*‖f.toLp (ENNReal.ofReal 3) volume‖*‖g.toLp (ENNReal.ofReal 3) volume‖*
          ‖h.toLp (ENNReal.ofReal 3) volume‖
        (∀ I : Finset ℤ, ‖radianTrilinearForm (fun p => m p * ∑ j ∈ I, W j p) f g h‖ ≤ B) ∧
        HasSum (fun j : ℤ => radianTrilinearForm (fun p => m p * W j p) f g h)
          (radianTrilinearForm (fun p => m p * ∑' j, W j p) f g h) ∧
        ‖radianTrilinearForm (fun p => m p * ∑' j, W j p) f g h‖ ≤ B := by
  obtain ⟨C₀,hC₀,fromAtlas⟩ := exists_sphereEndpoint_box_bound_of_atlas V U angular hV hU hCover hAngular hMap b hb
  obtain ⟨C₁,hC₁,endpointBound⟩ := exists_sphereEndpoint_radian_bound
  refine ⟨C₁*C₀,mul_nonneg hC₁ hC₀,?_⟩
  intro M M₀ A hA smooth jets eq gap f g h
  obtain ⟨smoothBox,boxJets⟩ := fromAtlas M M₀ A hA smooth jets eq
  simpa only [mul_assoc] using endpointBound M₀ (C₀*A) (mul_nonneg hC₀ hA) smoothBox boxJets gap f g h

end Burnett.A05
