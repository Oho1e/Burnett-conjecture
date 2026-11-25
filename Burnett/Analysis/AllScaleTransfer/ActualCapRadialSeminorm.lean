import Burnett.Analysis.AllScaleTransfer.CapRadialNormJets
import Burnett.Analysis.AllScaleTransfer.RadialRatioCorrection

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.CapFourier

open Set Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

private theorem parabolicDilation_norm_le {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (u : NullFrequencyCoordinates) : ‖parabolicDilation δ u‖ ≤ ‖u‖ := by
  simp only [parabolicDilation, Prod.norm_def, norm_mul, norm_smul,
    Real.norm_of_nonneg hδ, Real.norm_of_nonneg (sq_nonneg δ)]
  exact max_le_max le_rfl (max_le_max
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hδ hδone))
    (mul_le_of_le_one_left (norm_nonneg _) hδone))

/-- The actual cap map has a uniform upper operator-norm bound on the full space. -/
theorem capFrequencyEquiv_opNorm_le {m : Form} {w : Vec} (F : NullCapChart m w)
    {δ B : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hB : 0 ≤ B)
    (hF : ‖F.toFrequency.toContinuousLinearMap‖ ≤ B) :
    ‖(capFrequencyEquiv F hδ.ne').toContinuousLinearMap‖ ≤
      B * ‖frequencyCoordinates.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg _))
  intro p
  change ‖capFrequencyEquiv F hδ.ne' p‖ ≤ _
  rw [capFrequencyEquiv_apply]
  let u := frequencyCoordinates p
  change ‖F.toFrequency (parabolicDilation δ u)‖ ≤ _
  calc
    _ ≤ ‖F.toFrequency.toContinuousLinearMap‖ * ‖parabolicDilation δ u‖ :=
      F.toFrequency.toContinuousLinearMap.le_opNorm _
    _ ≤ B * ‖u‖ := mul_le_mul hF (parabolicDilation_norm_le hδ.le hδone u) (norm_nonneg _) hB
    _ ≤ B * (‖frequencyCoordinates.toContinuousLinearMap‖ * ‖p‖) :=
      mul_le_mul_of_nonneg_left (frequencyCoordinates.toContinuousLinearMap.le_opNorm p) hB
    _ = _ := (mul_assoc _ _ _).symm

/-- The fixed cone is measured by the first null coordinate, which dilation preserves. -/
theorem capFrequencyEquiv_lower_on_axial_cone {m : Form} {w : Vec} (F : NullCapChart m w)
    {δ B axial : ℝ} (hδ : δ ≠ 0) (hB : 0 < B) (hI : ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B)
    {p : Space} (hCone : axial * ‖p‖ ≤ |(frequencyCoordinates p).1|) :
    (axial / B) * ‖p‖ ≤ ‖capFrequencyEquiv F hδ p‖ := by
  let u := parabolicDilation δ (frequencyCoordinates p)
  have hAxis : |(frequencyCoordinates p).1| ≤ ‖u‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_left _ _
  have hInv : ‖u‖ ≤ B * ‖F.toFrequency u‖ := by
    have h := F.toFrequency.symm.toContinuousLinearMap.le_opNorm (F.toFrequency u)
    change ‖F.toFrequency.symm (F.toFrequency u)‖ ≤ _ at h
    rw [F.toFrequency.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right hI (norm_nonneg _))
  rw [capFrequencyEquiv_apply, div_mul_eq_mul_div]
  change axial * ‖p‖ / B ≤ ‖F.toFrequency u‖
  apply (div_le_iff₀ hB).2
  exact (hCone.trans (hAxis.trans hInv)).trans_eq (mul_comm _ _)

/-- The actual physical ratio after factoring the two different annular scales. -/
def annularPhysicalRatio (A : Space ≃L[ℝ] Space) (r : ℝ) (s : ℕ) (pq : Space × Space) : ℝ :=
  ‖A ((r / (2 : ℝ)^s) • pq.1)‖ / ‖A (r • pq.2)‖

theorem annularPhysicalRatio_eq_gap_mul (A : Space ≃L[ℝ] Space) {r : ℝ} (hr : 0 < r) (s : ℕ) :
    annularPhysicalRatio A r s =
      fun pq => (1 / (2 : ℝ)^s) * physicalRadialRatio A.toContinuousLinearMap pq := by
  funext pq
  by_cases hq : pq.2 = 0
  · simp [annularPhysicalRatio, physicalRadialRatio, hq]
  · exact physical_ratio_scaled A hr s pq.1 pq.2 hq

/-- The annular scales are exactly the original dyadic scales with an integer high index. -/
theorem annularPhysicalRatio_eq_dyadic (A : Space ≃L[ℝ] Space) (k : ℤ) (s : ℕ) :
    annularPhysicalRatio A ((2 : ℝ)^k) s =
      fun pq => ‖A (((2 : ℝ)^(k - (s : ℤ))) • pq.1)‖ / ‖A (((2 : ℝ)^k) • pq.2)‖ := by
  funext pq
  simp only [annularPhysicalRatio, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

theorem iteratedFDeriv_annularPhysicalRatio (A : Space ≃L[ℝ] Space) {r : ℝ} (hr : 0 < r)
    (s j : ℕ) {p q : Space} (hp : p ≠ 0) (hq : q ≠ 0) :
    iteratedFDeriv ℝ j (annularPhysicalRatio A r s) (p,q) =
      (1 / (2 : ℝ)^s) • iteratedFDeriv ℝ j (physicalRadialRatio A.toContinuousLinearMap) (p,q) := by
  have hA (x : Space) (hx : x ≠ 0) : A.toContinuousLinearMap x ≠ 0 := by
    intro h
    apply hx
    exact A.injective (h.trans A.map_zero.symm)
  have hSmooth : ContDiffAt ℝ j (physicalRadialRatio A.toContinuousLinearMap) (p,q) :=
    (physicalRadialRatio_contDiffAt A.toContinuousLinearMap (hA p hp) (hA q hq)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [annularPhysicalRatio_eq_gap_mul A hr]
  exact iteratedFDeriv_const_smul_apply' (a := 1 / (2 : ℝ)^s) hSmooth

/-- Closed support of the actual enlarged cap is unchanged by annular rescaling. -/
theorem capFrequencyEquiv_enlarged_tsupport_smul_iff {m : Form} {w : Vec} (F : NullCapChart m w)
    {δ : ℝ} (hδ : δ ≠ 0) (η outer enlarged : ℝ) {r : ℝ} (hr : r ≠ 0) (p : Space) :
    capFrequencyEquiv F hδ (r • p) ∈ tsupport (enlargedCapMultiplier m δ η outer enlarged w) ↔
      capFrequencyEquiv F hδ p ∈ tsupport (enlargedCapMultiplier m δ η outer enlarged w) := by
  rw [map_smul]
  let b := enlargedCapMultiplier m δ η outer enlarged w
  let e : Space ≃ₜ Space := Homeomorph.smulOfNeZero r hr
  let x := capFrequencyEquiv F hδ p
  change x ∈ e ⁻¹' closure (Function.support b) ↔ x ∈ closure (Function.support b)
  have hs : e ⁻¹' Function.support b = Function.support b := by
    ext y
    change (b (r • y) ≠ 0) ↔ (b y ≠ 0)
    have hb : b (r • y) = b y := enlargedCapMultiplier_degreeZero m δ η outer enlarged w r hr y
    rw [hb]
  rw [e.preimage_closure, hs]

/-- A single finite-order budget for the actual chart maps. It covers both
the fixed axial cone and the closed support of the actual enlarged multiplier. -/
theorem exists_uniform_capFrequency_radial_seminorms (B tube outer enlarged axial lo hi : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hAxial : 0 < axial) (hlo : 0 < lo) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
      ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
      ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
        let A := capFrequencyEquiv F hδ.ne'
        let D : Set Space := radialJetAnnulus lo hi ∩
          ({p : Space | axial * ‖p‖ ≤ |(frequencyCoordinates p).1|} ∪
            (A ⁻¹' tsupport (enlargedCapMultiplier m δ (tube*δ^2) outer enlarged w)))
        (∀ j ≤ n, ∀ p ∈ D,
          ‖iteratedFDeriv ℝ j (capRadialFactor A.toContinuousLinearMap) p‖ ≤ C ∧
          ‖iteratedFDeriv ℝ j (fun x => (capRadialFactor A.toContinuousLinearMap x)⁻¹) p‖ ≤ C) ∧
        (∀ j ≤ n, ∀ p ∈ D, ∀ q ∈ D,
          ‖iteratedFDeriv ℝ j (physicalRadialRatio A.toContinuousLinearMap) (p,q)‖ ≤ C ∧
          ∀ (r : ℝ), 0 < r → ∀ s : ℕ,
            ‖iteratedFDeriv ℝ j (annularPhysicalRatio A r s) (p,q)‖ ≤ C / (2 : ℝ)^s) := by
  obtain ⟨Lsupport, _, hLsupport, _, hSupport⟩ :=
    exists_uniform_capFrequency_norm_compare B tube outer enlarged hB hTube hOut hOE
  let L := min Lsupport (axial / B)
  have hL : 0 < L := lt_min hLsupport (div_pos hAxial hB)
  obtain ⟨C,hC,hBudget⟩ := exists_uniform_radial_norm_jets
    (B * ‖frequencyCoordinates.toContinuousLinearMap‖) L lo hi hL hlo n
  refine ⟨C,hC,?_⟩
  intro m w F hw hF hI δ hδ hδone hSmall
  let A := capFrequencyEquiv F hδ.ne'
  let D : Set Space := radialJetAnnulus lo hi ∩
    ({p : Space | axial * ‖p‖ ≤ |(frequencyCoordinates p).1|} ∪
      (A ⁻¹' tsupport (enlargedCapMultiplier m δ (tube*δ^2) outer enlarged w)))
  have hLower (p : Space) (hp : p ∈ D) : L * ‖p‖ ≤ ‖A p‖ := by
    rcases hp.2 with hCone | hSupp
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg p)).trans
        (capFrequencyEquiv_lower_on_axial_cone F hδ.ne' hB hI hCone)
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg p)).trans
        (hSupport m w F hw hI δ hδ hSmall p hSupp).1
  obtain ⟨hSingle,hPair⟩ := hBudget A.toContinuousLinearMap
    (capFrequencyEquiv_opNorm_le F hδ hδone hB.le hF)
  change (∀ j ≤ n, ∀ p ∈ D, _ ∧ _) ∧ (∀ j ≤ n, ∀ p ∈ D, ∀ q ∈ D, _ ∧ _)
  refine ⟨fun j hj p hp => hSingle j hj p hp.1 (hLower p hp), ?_⟩
  intro j hj p hp q hq
  have hRatio := hPair j hj p hp.1 q hq.1 (hLower p hp) (hLower q hq)
  refine ⟨hRatio, ?_⟩
  intro r hr s
  have hp0 : p ≠ 0 := norm_pos_iff.mp (hlo.trans_le hp.1.1)
  have hq0 : q ≠ 0 := norm_pos_iff.mp (hlo.trans_le hq.1.1)
  rw [iteratedFDeriv_annularPhysicalRatio A hr s j hp0 hq0, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (2 : ℝ)^s)]
  exact (mul_le_mul_of_nonneg_left hRatio (by positivity)).trans_eq (by ring)

end Burnett.Analysis.CapFourier
