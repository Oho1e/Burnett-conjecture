import Burnett.Analysis.AllScaleTransfer.OriginalAtlasFormBounds
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearL3Extension

set_option autoImplicit false
set_option maxRecDepth 8500
set_option maxHeartbeats 8500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8

noncomputable section

namespace Burnett.A05

open MeasureTheory Metric Set
open Burnett.A02.FrequencySplit
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped BigOperators ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
local instance : NormedAddCommGroup RadianLp3 := Lp.instNormedAddCommGroup
local instance : NormedSpace ℂ RadianLp3 := Lp.instNormedSpace

private def originalWindowSymbol : Option AnalyticNearInfraredWindow → E → ℂ
  | none => fun _ => 1
  | some w => fun p => (w.profile ‖p‖ : ℂ)

private theorem originalWindowSymbol_spec (window : Option AnalyticNearInfraredWindow) :
    Continuous (originalWindowSymbol window) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖originalWindowSymbol window p‖ ≤ B) ∧
      ∀ (f : SchwartzMap E ℂ) (p : E), radianFourier (analyticNearWindow window f) p =
        originalWindowSymbol window p * radianFourier f p := by
  cases window with
  | none => exact ⟨continuous_const,⟨1,zero_le_one,fun _ => norm_one.le⟩,fun _ _ => (one_mul _).symm⟩
  | some w =>
    have compact : IsCompact (w.profile '' Icc (0 : ℝ) w.upper) := isCompact_Icc.image w.smooth.continuous
    have bounded : Bornology.IsBounded (w.profile '' Icc (0 : ℝ) w.upper) := compact.isBounded
    obtain ⟨B,hB⟩ : ∃ B : ℝ, ∀ t ∈ w.profile '' Icc (0 : ℝ) w.upper, ‖t‖ ≤ B := bounded.exists_norm_le
    refine ⟨Complex.continuous_ofReal.comp (w.smooth.continuous.comp continuous_norm),
      ⟨max 1 B,zero_le_one.trans (le_max_left _ _),?_⟩,?_⟩
    · intro p
      change ‖(w.profile ‖p‖ : ℂ)‖ ≤ max 1 B
      rw [Complex.norm_real]
      by_cases above : w.upper ≤ ‖p‖
      · rw [w.above _ above,norm_one]
        exact le_max_left _ _
      · exact (hB _ ⟨‖p‖,⟨norm_nonneg _,(lt_of_not_ge above).le⟩,rfl⟩).trans (le_max_right _ _)
    · exact Burnett.A07.fixedInfraredSchwartz_radianFourier w.profile w.smooth w.lower w.upper
        w.lower_pos w.below w.above

private def originalRadialSymbol (J : Finset ℤ) (ε : ℤ → ℂ) (p : E) : ℂ :=
  ∑ j ∈ J, ε j * (integerRadialWindow j p : ℂ)

private theorem originalRadialSymbol_spec (J : Finset ℤ) (ε : ℤ → ℂ) :
    Continuous (originalRadialSymbol J ε) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖originalRadialSymbol J ε p‖ ≤ B := by
  let D := SchwartzMap.seminorm ℝ 0 0 endpointHighProfile
  have hD : 0 ≤ D := apply_nonneg _ _
  have smooth : ContDiff ℝ ∞ (radialBallBump : E → ℝ) := radialBallBump.contDiff
  have lo (r : ℝ) : Continuous (radialLowCutoff r) :=
    smooth.continuous.comp (continuous_const_smul _)
  have cont (j : ℤ) : Continuous (fun p : E => (integerRadialWindow j p : ℂ)) :=
    Complex.continuous_ofReal.comp ((lo _).sub (lo _))
  refine ⟨continuous_finset_sum J (fun j _ => continuous_const.mul (cont j)),
    ⟨∑ j ∈ J, ‖ε j‖*D,Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) hD),?_⟩⟩
  intro p
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,← endpointHighProfile_eq_integerRadialWindow]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ endpointHighProfile _) (norm_nonneg _)

private theorem exists_radianFormLp3_of_slot_symbols (m : Joint → ℂ) (sym : AnalyticNearSymbol m)
    (C : ℝ) (hC : 0 ≤ C) (P : Fin 3 → E → ℂ) (cut : Fin 3 → SchwartzMap E ℂ → SchwartzMap E ℂ)
    (cont : ∀ i, Continuous (P i)) (mag : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖P i p‖ ≤ B)
    (spectra : ∀ i (f : SchwartzMap E ℂ) (p : E), radianFourier (cut i f) p = P i p * radianFourier f p)
    (bound : ∀ f g h : SchwartzMap E ℂ,
      ‖radianTrilinearForm m (cut 0 f) (cut 1 g) (cut 2 h)‖ ≤ C*(triLpMass f g h 3 3 3).toReal) :
    ∃ T : RadianTrilinearLp3, ‖T‖ ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      T (f.toLp (ENNReal.ofReal 3) volume) (g.toLp (ENNReal.ofReal 3) volume) (h.toLp (ENNReal.ofReal 3) volume) =
        radianTrilinearForm m (cut 0 f) (cut 1 g) (cut 2 h) := by
  let masked (p : Joint) := m p * (P 0 p.1 * P 1 p.2 * P 2 (-(p.1+p.2)))
  have meas : Measurable masked := sym.measurable.mul
    ((((cont 0).comp continuous_fst).mul ((cont 1).comp continuous_snd)).mul
      ((cont 2).comp (continuous_fst.add continuous_snd).neg)).measurable
  obtain ⟨A,hA,hMag⟩ := sym.bounded
  choose B hB hBmag using mag
  have mNorm (p : Joint) : ‖masked p‖ ≤ A*(B 0*B 1*B 2) := by
    simp only [masked,norm_mul]
    exact mul_le_mul (hMag p)
      (mul_le_mul (mul_le_mul (hBmag 0 _) (hBmag 1 _) (norm_nonneg _) (hB 0))
        (hBmag 2 _) (norm_nonneg _) (mul_nonneg (hB 0) (hB 1))) (by positivity) hA
  have eq (f g h : SchwartzMap E ℂ) : radianTrilinearForm masked f g h =
      radianTrilinearForm m (cut 0 f) (cut 1 g) (cut 2 h) := by
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    simp only [radianTrilinearWeight,radianWeight,Complex.ofReal_one,one_mul,spectra,masked]
    ring
  have exactBound (f g h : SchwartzMap E ℂ) : ‖radianTrilinearForm masked f g h‖ ≤
      C * ‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
        ‖h.toLp (ENNReal.ofReal 3) volume‖ := by
    rw [eq]
    simpa only [triLpMass,ENNReal.toReal_mul,SchwartzMap.norm_toLp,mul_assoc] using bound f g h
  obtain ⟨T,hT,matchT⟩ := exists_radianTrilinearForm_Lp3_extension masked meas.aestronglyMeasurable
    (A*(B 0*B 1*B 2)) mNorm C hC exactBound
  exact ⟨T,hT,fun f g h => (matchT f g h).trans (eq f g h)⟩

/-- The full windowed form and each independent finite factorwise
truncation have a continuous trilinear extension with the same bound. -/
def AnalyticNearFormLp3Extensions (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    (m : Joint → ℂ) (C : ℝ) : Prop :=
  (∃ T : RadianTrilinearLp3, ‖T‖ ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      T (f.toLp (ENNReal.ofReal 3) volume) (g.toLp (ENNReal.ofReal 3) volume) (h.toLp (ENNReal.ofReal 3) volume) =
        radianTrilinearForm m (analyticNearWindow (windows 0) f)
          (analyticNearWindow (windows 1) g) (analyticNearWindow (windows 2) h)) ∧
  ∀ (I J L : Finset ℤ) (a b c : ℤ → ℂ),
    (∀ j ∈ I, ‖a j‖ ≤ 1) → (∀ j ∈ J, ‖b j‖ ≤ 1) → (∀ j ∈ L, ‖c j‖ ≤ 1) →
    ∃ T : RadianTrilinearLp3, ‖T‖ ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      T (f.toLp (ENNReal.ofReal 3) volume) (g.toLp (ENNReal.ofReal 3) volume) (h.toLp (ENNReal.ofReal 3) volume) =
        radianTrilinearForm m
          (finiteIntegerRadialTruncation I a (analyticNearWindow (windows 0) f))
          (finiteIntegerRadialTruncation J b (analyticNearWindow (windows 1) g))
          (finiteIntegerRadialTruncation L c (analyticNearWindow (windows 2) h))

/-- Consume the exact full and finite estimates of A05. The representative
bound and the auxiliary mask bounds serve only to define the dense forms. -/
theorem AnalyticNearFormBound.exists_Lp3_extensions {windows : Fin 3 → Option AnalyticNearInfraredWindow}
    {m : Joint → ℂ} {C : ℝ} (bound : AnalyticNearFormBound windows m C)
    (sym : AnalyticNearOriginalSymbol m) (hC : 0 ≤ C) : AnalyticNearFormLp3Extensions windows m C := by
  obtain ⟨B,hB,hNorm⟩ := sym.bounded
  obtain ⟨m',sym',_,same⟩ := exists_analyticNearSymbol_of_nonzeroSignedTriads m B hB sym.continuous hNorm sym.homogeneous
  have full := exists_radianFormLp3_of_slot_symbols m' sym' C hC (fun i => originalWindowSymbol (windows i))
    (fun i => analyticNearWindow (windows i)) (fun i => (originalWindowSymbol_spec (windows i)).1)
    (fun i => (originalWindowSymbol_spec (windows i)).2.1)
    (fun i => (originalWindowSymbol_spec (windows i)).2.2)
    (fun f g h => by simpa only [same] using bound.1 f g h)
  refine ⟨?_,?_⟩
  · obtain ⟨T,hT,hTform⟩ := full
    exact ⟨T,hT,fun f g h => (hTform f g h).trans (same _ _ _)⟩
  · intro I J L a b c ha hb hc
    let sets : Fin 3 → Finset ℤ := ![I,J,L]
    let weights : Fin 3 → ℤ → ℂ := ![a,b,c]
    let P (i : Fin 3) (p : E) := originalRadialSymbol (sets i) (weights i) p * originalWindowSymbol (windows i) p
    let cut (i : Fin 3) (f : SchwartzMap E ℂ) :=
      finiteIntegerRadialTruncation (sets i) (weights i) (analyticNearWindow (windows i) f)
    have cont (i : Fin 3) : Continuous (P i) :=
      (originalRadialSymbol_spec (sets i) (weights i)).1.mul (originalWindowSymbol_spec (windows i)).1
    have mag (i : Fin 3) : ∃ A : ℝ, 0 ≤ A ∧ ∀ p, ‖P i p‖ ≤ A := by
      obtain ⟨D,hD,d⟩ := (originalRadialSymbol_spec (sets i) (weights i)).2
      obtain ⟨E₀,hE,e⟩ := (originalWindowSymbol_spec (windows i)).2.1
      refine ⟨D*E₀,mul_nonneg hD hE,?_⟩
      intro p
      dsimp only [P]
      rw [norm_mul]
      exact mul_le_mul (d p) (e p) (norm_nonneg _) hD
    have spectra (i : Fin 3) (f : SchwartzMap E ℂ) (p : E) : radianFourier (cut i f) p = P i p * radianFourier f p := by
      dsimp only [cut]
      rw [finiteIntegerRadialTruncation_radianFourier,(originalWindowSymbol_spec (windows i)).2.2]
      exact (mul_assoc _ _ _).symm
    have truncated := exists_radianFormLp3_of_slot_symbols m' sym' C hC P cut cont mag spectra
      (fun f g h => by rw [same]; exact bound.2 I J L a b c ha hb hc f g h)
    obtain ⟨T,hT,hTform⟩ := truncated
    exact ⟨T,hT,fun f g h => (hTform f g h).trans (same _ _ _)⟩

/-- The full and finite A05 forms extend on the original L³ factors
under the same atlas and cap hypotheses, with the same analytic constants. -/
theorem exists_analyticNear_original_allScale_Lp3_of_atlases
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b)
    (windows : Fin 3 → Option AnalyticNearInfraredWindow)
    {K : Set Form} (hK : IsCompact K) (hFrame : ∀ metric ∈ K, Nonempty (LorentzFrame metric))
    (hND : ∀ metric ∈ K, Nondegenerate metric)
    (inner outer enlarged : ℝ) (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ (N₀ : ℕ) (C₀ B D c₀ δ₀ : ℝ),
      0 ≤ C₀ ∧ 0 < B ∧ 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (∀ (m : Joint → ℂ), (∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) → ∀ A ≥ 0,
        AnalyticNearPositiveAtlas ϑ κ b A m →
        AnalyticNearComparableBudget N₀ A (radianFourBranchSymbol ϑ κ m 3) →
        AnalyticNearFormLp3Extensions windows m (C₀*A)) ∧
      ∀ c : ℝ, 0 < c → c ≤ c₀ →
        ∃ (R : ℝ) (N : ℕ) (C₃ : ℝ) (Cang Cnear : {q : ℝ // 3 < q} → ℝ),
          0 < R ∧ R < 1 ∧ 0 ≤ C₃ ∧ (∀ q, 0 ≤ Cang q) ∧ (∀ q, 0 ≤ Cnear q) ∧
          ∀ metric ∈ K, ∀ δ ∈ Ioc (0 : ℝ) δ₀,
            ∃ (hδ : δ ∈ Ioc (0 : ℝ) 1)
              (S : SmoothThinConeCaps metric δ (c*κ*δ^2) inner outer enlarged D)
              (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
                (enlargedCapMultiplier metric δ (c*κ*δ^2) outer enlarged γ) C₃)
              (chart : ∀ γ : ↑S.centers, NullCapChart metric γ),
              (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) ∧
              (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) ∧
              (∀ (q : {q : ℝ // 3 < q}) (v : FieldLp Unit (ENNReal.ofReal 3)),
                (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction v‖^3)^((1 : ℝ)/3) ≤
                  Cang q * (S.centers.card : ℝ)^(1/(3*(q.val-2))) * ‖v‖) ∧
              ∀ (pStar : {q : ℝ // 3 < q}) (m : Joint → ℂ),
                (∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) →
                AnalyticNearAdjacentSupport metric δ (c*κ*δ^2) inner m → ∀ A ≥ 0,
                AnalyticNearSignedCapProfiles ϑ κ b R A N hδ.1.ne' S chart m →
                AnalyticNearFormLp3Extensions windows m (Cnear pStar*A*δ^(2*(pStar.val-3)/(pStar.val-2))) := by
  obtain ⟨N₀,C₀,B,D,c₀,Δ,hC₀,hB,hD,hc₀,hΔ,hΔ₁,unscaled,caps⟩ :=
    exists_analyticNear_original_allScale_of_atlases ϑ hϑ hRange hCut hFlat κ b hκ hκsmall hb
      windows hK hFrame hND inner outer enlarged hIn hIO hOE
  obtain ⟨Nreg,cover⟩ := exists_analyticNearComparableCoverage hCut hFlat hκ hκsmall
  let δ₀ := min Δ (1/(20*B))
  have hB₀ : 0 < 20*B := by positivity
  refine ⟨max N₀ Nreg,C₀,B,D,c₀,δ₀,hC₀,hB,hD,hc₀,lt_min hΔ (one_div_pos.mpr hB₀),
    (min_le_left _ _).trans hΔ₁,?_,?_⟩
  · intro m hom A hA atlas boxes
    have sym := analyticNearOriginalSymbol_of_positiveAtlas_boxes ϑ hϑ.continuous hCut hκ hκsmall hb hA m
      hom atlas cover (boxes.restrict (le_max_right _ _))
    have form := unscaled m hom A hA atlas (boxes.restrict (le_max_left _ _))
    exact form.exists_Lp3_extensions sym (mul_nonneg hC₀ hA)
  · intro c hc hc₀'
    let tube := c*κ
    have hTube : 0 < tube := mul_pos hc hκ
    obtain ⟨R₁,N₁,C₃,Cang,Cnear,hR₁,hR₁one,hC₃,hCang,hCnear,near⟩ := caps c hc hc₀'
    obtain ⟨R₂,N₂,hR₂,hR₂one,hasSymbol⟩ := exists_analyticNearOriginalSymbol_of_signedCapProfiles ϑ
      hϑ.continuous hCut hFlat B tube outer enlarged hB hTube (hIn.trans hIO.le) hOE hκ hκsmall hb
    refine ⟨max R₁ R₂,max N₁ N₂,C₃,Cang,Cnear,hR₁.trans_le (le_max_left _ _),max_lt hR₁one hR₂one,
      hC₃,hCang,hCnear,?_⟩
    intro metric hm δ hδ₀
    obtain ⟨hδ,S,Pplus,chart,fwd,inv,angular,estimate⟩ :=
      near metric hm δ ⟨hδ₀.1,hδ₀.2.trans (min_le_left _ _)⟩
    refine ⟨hδ,S,Pplus,chart,fwd,inv,angular,?_⟩
    have hSmall : 4*B*(5*δ) ≤ 1 := by
      have e := (le_div_iff₀ hB₀).mp (hδ₀.2.trans (min_le_right Δ (1/(20*B))))
      nlinarith only [e]
    intro pStar m hom adj A hA profiles
    have sym := hasSymbol hδ.1 hSmall hIO.le S chart inv m hom adj A hA
      (profiles.restrict ϑ κ (le_max_right _ _) (le_max_right _ _) hδ.1.ne' S chart m)
    have form := estimate pStar m hom adj A hA
      (profiles.restrict ϑ κ (le_max_left _ _) (le_max_left _ _) hδ.1.ne' S chart m)
    exact form.exists_Lp3_extensions sym
      (mul_nonneg (mul_nonneg (hCnear pStar) hA) (Real.rpow_nonneg hδ.1.le _))

end Burnett.A05

#print axioms Burnett.A05.AnalyticNearFormBound.exists_Lp3_extensions
#print axioms Burnett.A05.exists_analyticNear_original_allScale_Lp3_of_atlases
