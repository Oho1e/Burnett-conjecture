import Burnett.Analysis.AllScaleTransfer.FiniteShiftRemainderNumerator
import Burnett.Analysis.AllScaleTransfer.CapRadialNormJets

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Filter Nat Burnett.Analysis Burnett.Analysis.CapFourier
open scoped ContDiff Topology

/-- Physical ratio at the normalized pair for the signed displacement k. -/
def fixedShiftPhysicalRatio (A : Frequency ≃L[ℝ] Frequency) (k : ℤ)
    (p : FrequencyPair) : ℝ :=
  (2 : ℝ)^k * physicalRadialRatio A.toContinuousLinearMap p

private theorem fixedShift_pair_jet
    {V : Set FrequencyPair} (hV : IsOpen V)
    {f : FrequencyPair → LowRatio.Angles} {g : FrequencyPair → ℝ}
    (hf : ContDiffOn ℝ 100 f V) (hg : ContDiffOn ℝ 100 g V)
    {x : FrequencyPair} (hx : x ∈ V) {j : ℕ} (hj : j ≤ 40) :
    ‖iteratedFDeriv ℝ j (fun z => (f z, g z)) x‖ =
      max ‖iteratedFDeriv ℝ j f x‖ ‖iteratedFDeriv ℝ j g x‖ := by
  have hj' : (j : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hj.trans (by decide : 40 ≤ 100))
  have h := ((hf.of_le hj').ftaylorSeriesWithin hV.uniqueDiffOn).prodMk
    ((hg.of_le hj').ftaylorSeriesWithin hV.uniqueDiffOn)
  rw [← iteratedFDerivWithin_of_isOpen j hV hx, ← iteratedFDerivWithin_of_isOpen (f := f) j hV hx,
    ← iteratedFDerivWithin_of_isOpen (f := g) j hV hx,
    ← h.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hV.uniqueDiffOn hx,
    ContinuousMultilinearMap.opNorm_prod]
  rfl

/-- Fixed normalized boxes for the original finite-shift remainder.
The radial jets are for the same A used in the physical symbol. The
fixed ratio cutoff allows the signed annuli to extend past the domain
of the one-sided original symbol. -/
theorem exists_finite_shift_remainder_boxes (I : Finset ℤ) (B : ℝ) (hB : 0 ≤ B)
    {K V : Set FrequencyPair} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hNonzero : ∀ p ∈ V, p.1 ≠ 0 ∧ p.2 ≠ 0)
    {U : Set LowRatio.Angles} (hU : IsOpen U) (angular : FrequencyPair → LowRatio.Angles)
    (hAngular : ContDiffOn ℝ ∞ angular V) (hMap : MapsTo angular V U)
    {u b : ℝ} (hu : 0 < u) (hub : u < b) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ (η : ℝ → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ r ∈ Icc 0 u, η r = 1) ∧ (∀ r, b ≤ r → η r = 0) ∧
      ∀ (A : Frequency ≃L[ℝ] Frequency),
        (∀ n ≤ 40, ∀ p ∈ V,
          ‖iteratedFDeriv ℝ n (physicalRadialRatio A.toContinuousLinearMap) p‖ ≤ B) →
        ∀ (M : LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
          ContDiffOn ℝ 100 M (U ×ˢ Ico 0 b) →
          (∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico 0 b,
            ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico 0 b) z‖ ≤ A₁₀₀) →
          ∃ G : ℤ → BoxSpace → ℂ,
            (∀ k, ContDiff ℝ 100 (G k)) ∧
            (∀ k z, boxToPair z ∉ V → G k z = 0) ∧
            (∀ k ∈ I, ∀ n ≤ 40, ∀ z, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ C * A₁₀₀) ∧
            ∀ k ζ υ, (ζ,υ) ∈ K → G k (joinedInputs ζ υ) =
              cutoffRemainderNumerator M χ η
                (angular (ζ,υ), fixedShiftPhysicalRatio A k (ζ,υ)) := by
  obtain ⟨η,Cnum,_,hCnum,oneη,zeroη,num⟩ :=
    exists_cutoffRemainderNumerator_jets hU hu hub χ hχ
  obtain ⟨β,sβ,cβ,tβ,oneβ⟩ := exists_fixed_annular_cutoff hK hV hKV
  obtain ⟨Jβ,hJβ,bβ⟩ := exists_compact_contDiffOn_jet_bound
    cβ isOpen_univ (subset_univ _) sβ.contDiffOn 40
  obtain ⟨Ja,hJa,ba⟩ := exists_compact_contDiffOn_jet_bound cβ hV tβ hAngular 40
  let L := ∑ k ∈ I, (2 : ℝ)^k
  let D := max 1 (max Ja (L * B))
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 := zero_le_one.trans hD
  let X := max 1 ‖boxToPair.toContinuousLinearMap‖
  have hX : 1 ≤ X := le_max_left _ _
  let C := (2 : ℝ)^40 * Jβ * (((40 ! : ℕ) : ℝ) * D^40 * Cnum) * X^40
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨η,C,hC,oneη,zeroη,?_⟩
  intro A bR M A₁₀₀ hA₁₀₀ sM bM
  obtain ⟨sN,bN⟩ := num M A₁₀₀ hA₁₀₀ sM bM
  let N := cutoffRemainderNumerator M χ η
  let r := physicalRadialRatio A.toContinuousLinearMap
  have rPos (p : FrequencyPair) (hp : p ∈ V) : 0 < r p := by
    exact div_pos (norm_pos_iff.mpr (fun h => (hNonzero p hp).1 (A.injective (h.trans A.map_zero.symm))))
      (norm_pos_iff.mpr (fun h => (hNonzero p hp).2 (A.injective (h.trans A.map_zero.symm))))
  have sr : ContDiffOn ℝ ∞ r V := by
    intro p hp
    have bad {x : Frequency} (h : x ≠ 0) : A x ≠ 0 :=
      fun e => h (A.injective (e.trans A.map_zero.symm))
    exact (physicalRadialRatio_contDiffAt _ (bad (hNonzero p hp).1)
      (bad (hNonzero p hp).2)).contDiffWithinAt
  let ρ := fixedShiftPhysicalRatio A
  let Θ (k : ℤ) (p : FrequencyPair) : LowRatio.Point := (angular p,ρ k p)
  let g (k : ℤ) (p : FrequencyPair) := β p • N (Θ k p)
  let G (k : ℤ) : BoxSpace → ℂ := g k ∘ boxToPair
  have hOrder : (100 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hDomain : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have sρ (k : ℤ) : ContDiffOn ℝ 100 (ρ k) V :=
    contDiffOn_const.mul (sr.of_le hOrder)
  have maps (k : ℤ) : MapsTo (Θ k) V (U ×ˢ Ioi (0 : ℝ)) :=
    fun p hp => ⟨hMap hp, mul_pos (by positivity) (rPos p hp)⟩
  have sΘ (k : ℤ) : ContDiffOn ℝ 100 (Θ k) V :=
    (hAngular.of_le hOrder).prodMk (sρ k)
  have sComp (k : ℤ) : ContDiffOn ℝ 100 (N ∘ Θ k) V :=
    sN.comp (sΘ k) (maps k)
  have supp (k : ℤ) : tsupport (g k) ⊆ tsupport β := tsupport_smul_subset_left _ _
  have sg (k : ℤ) : ContDiff ℝ 100 (g k) := by
    have sLoc : ContDiffOn ℝ 100 (g k) V :=
      ((sβ.of_le hOrder).contDiffOn).smul (sComp k)
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases h : p ∈ V
    · exact sLoc.contDiffAt (hV.mem_nhds h)
    · have hs : p ∉ tsupport (g k) := fun hx => h (tβ (supp k hx))
      exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hs)
  have bg (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40) (x : FrequencyPair) :
      ‖iteratedFDeriv ℝ n (g k) x‖ ≤ (2 : ℝ)^40 * Jβ *
        (((40 ! : ℕ) : ℝ) * D^40 * Cnum) * A₁₀₀ := by
    by_cases hx : x ∈ tsupport β
    · have hVx := tβ hx
      have hkL : (2 : ℝ)^k ≤ L := Finset.single_le_sum
        (f := fun l : ℤ => (2 : ℝ)^l) (fun l _ => zpow_nonneg (by norm_num) _) hk
      have bρ (j : ℕ) (hj : j ≤ 40) : ‖iteratedFDeriv ℝ j (ρ k) x‖ ≤ L * B := by
        have hj' : (j : WithTop ℕ∞) ≤ ∞ := by
          exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
        change ‖iteratedFDeriv ℝ j (fun y => ((2 : ℝ)^k) • r y) x‖ ≤ L * B
        rw [iteratedFDeriv_const_smul_apply' ((sr.of_le hj').contDiffAt (hV.mem_nhds hVx)),
          norm_smul, Real.norm_of_nonneg (zpow_nonneg (by norm_num) _)]
        calc
          _ ≤ (2 : ℝ)^k * B := mul_le_mul_of_nonneg_left (bR j hj x hVx) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hkL hB
      have bΘ (j : ℕ) (hj : j ≤ 40) (hPos : 1 ≤ j) :
          ‖iteratedFDeriv ℝ j (Θ k) x‖ ≤ D^j := by
        rw [fixedShift_pair_jet hV (hAngular.of_le hOrder) (sρ k) hVx hj]
        exact (max_le_max (ba j hj x hx) (bρ j hj)).trans
          ((le_max_right 1 _).trans (by
            calc
              D = D^1 := (pow_one _).symm
              _ ≤ D^j := pow_le_pow_right₀ hD hPos))
      have bComp (j : ℕ) (hj : j ≤ 40) :
          ‖iteratedFDeriv ℝ j (N ∘ Θ k) x‖ ≤ ((40 ! : ℕ) : ℝ) * D^40 * Cnum * A₁₀₀ := by
        have hj' : (j : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hj.trans (by decide : 40 ≤ 100))
        have h := norm_iteratedFDerivWithin_comp_le sN (sΘ k) hj'
          hDomain.uniqueDiffOn hV.uniqueDiffOn (maps k) hVx
          (C := Cnum * A₁₀₀) (D := D)
          (fun i hi => by
            rw [iteratedFDerivWithin_of_isOpen i hDomain (maps k hVx)]
            exact bN i (hi.trans hj) _ (maps k hVx))
          (fun i hpos hi => by
            rw [iteratedFDerivWithin_of_isOpen i hV hVx]
            exact bΘ i (hi.trans hj) hpos)
        rw [iteratedFDerivWithin_of_isOpen j hV hVx] at h
        calc
          _ ≤ ((j ! : ℕ) : ℝ) * (Cnum * A₁₀₀) * D^j := h
          _ ≤ ((40 ! : ℕ) : ℝ) * (Cnum * A₁₀₀) * D^40 :=
            mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
              (by positivity)) (pow_le_pow_right₀ hD hj) (pow_nonneg hD0 _) (by positivity)
          _ = _ := by ring
      have hb := fixedShift_norm_smul_jet_le hV ((sβ.of_le hOrder).contDiffOn)
        (sComp k) hVx hn hJβ
        (show 0 ≤ ((40 ! : ℕ) : ℝ) * D^40 * Cnum * A₁₀₀ by positivity)
        (fun j hj => bβ j (hj.trans hn) x hx) (fun j hj => bComp j (hj.trans hn))
      exact hb.trans_eq (by ring)
    · have z : iteratedFDeriv ℝ n (g k) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (supp k (tsupport_iteratedFDeriv_subset n h)))
      rw [z, norm_zero]
      positivity
  refine ⟨G,fun k => (sg k).comp boxToPair.contDiff,?_,?_,?_⟩
  · intro k x hx
    change g k (boxToPair x) = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (tβ (supp k h)))
  · intro k hk n hn x
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 100))
    change ‖iteratedFDeriv ℝ n (g k ∘ boxToPair.toContinuousLinearMap) x‖ ≤ C * A₁₀₀
    rw [boxToPair.toContinuousLinearMap.iteratedFDeriv_comp_right (sg k) x hn']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ (2 : ℝ)^40 * Jβ * (((40 ! : ℕ) : ℝ) * D^40 * Cnum) * A₁₀₀ * X^40 :=
        mul_le_mul (bg k hk n hn (boxToPair x))
          ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) n).trans (pow_le_pow_right₀ hX hn))
          (by positivity) (by positivity)
      _ = _ := by dsimp [C]; ring
  · intro k ζ υ hp
    change β (boxToPair (joinedInputs ζ υ)) • N (Θ k (boxToPair (joinedInputs ζ υ))) = _
    rw [boxToPair_joined, oneβ _ hp, one_smul]

end Burnett.A05.BoxFourier
