import Burnett.Analysis.AllScaleTransfer.ActualCapFirstLow
import Burnett.Analysis.AllScaleTransfer.ActualComparableAxialBoxBound
import Burnett.Analysis.AllScaleTransfer.RadianNormalizedFourBranches

set_option autoImplicit false
set_option maxHeartbeats 5400000
noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff

/-- The three exact physical low branches and the complementary branch on
one normalized enlarged cap. The cutoff weights and relative ratios use
the physical triad before the common parabolic pullback. -/
theorem exists_actual_cap_normalized_full_spectrum_bound
    (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (P B tube outer enlarged κ l b : ℝ) (hP : 4 < P) (hB : 0 < B)
    (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (hl : 0 < l) (hb : 7*κ/4 < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (hχOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hχZero : ∀ t, 7*κ/4 ≤ t → χ t = 0) :
    ∃ (R : ℝ) (N : ℕ) (C : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ C ∧
      ∀ (metric : Form) (v : Vec) (F : NullCapChart metric v), ‖v‖ = 1 →
      ‖F.toFrequency.toContinuousLinearMap‖ ≤ B → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
      let A := capFrequencyEquiv F hδ.ne'
      let K := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged v)
      let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
      ∀ (m : Joint → ℂ) (Bm : ℝ), Measurable m → (∀ p, ‖m p‖ ≤ Bm) →
      (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      let bases : Fin 3 → Joint → ℂ := ![m,m ∘ radianCycle.symm,m ∘ radianCycle]
      let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (bases i) 0 ∘ pairedFrequencyEquiv A
      let comparable := radianFourBranchSymbol ϑ κ m 3 ∘ pairedFrequencyEquiv A
      ∀ (M : Fin 3 → E → E → ℝ → ℂ) (B₀ D : ℝ), 0 ≤ D →
      (∀ i, Measurable (fun p : Joint => M i p.1 p.2 0)) →
      (∀ i (p : Joint), ‖M i p.1 p.2 0‖ ≤ B₀) →
      (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) →
      (∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ D) →
      ∀ G : ℤ → BoxSpace → ℂ,
      (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) P)) →
      (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ D) →
      (∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
        G k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ)) →
      ∀ (f g h : SchwartzMap E ℂ), EndpointFiniteAnnulus f → EndpointFiniteAnnulus g → EndpointFiniteAnnulus h →
      (∀ p, radianFourier f p ≠ 0 → A p ∈ K) →
      (∀ p, radianFourier g p ≠ 0 → A p ∈ K) →
      (∀ p, radianFourier h p ≠ 0 → A p ∈ K) →
      let tests : Fin 3 → (SchwartzMap E ℂ × SchwartzMap E ℂ × SchwartzMap E ℂ) :=
        ![(f,g,h),(g,h,f),(h,f,g)]
      (∀ (i : Fin 3) (p : Joint),
        radianWeight (fun _ => 1) (tests i).1 (tests i).2.1 (tests i).2.2 p ≠ 0 →
        ‖A p.1‖/‖A p.2‖ ∈ Ioo (0 : ℝ) b →
        low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖)) →
      ‖radianTrilinearForm (m ∘ pairedFrequencyEquiv A) f g h‖ ≤ C*D*(triLpMass f g h 3 3 3).toReal := by
  let u := 7*κ/4
  have hu : 0 < u := by unfold u; positivity
  have hu1 : u < 1 := by unfold u; linarith only [hκsmall]
  obtain ⟨R,CL,hR,hR1,hCL,firstLow⟩ := exists_actual_cap_firstLow_bound B tube outer enlarged l u b
    hB hTube hOut hOE hl hu hu1 hb χ hχ hχRange hχOne hχZero
  obtain ⟨N,CC,hCC,comparableBound⟩ := exists_actual_cap_radianComparable_box_bound hCut hFlat
    P B tube outer enlarged κ hP hB hTube hOut hOE hκ hκsmall
  refine ⟨R,N,3*CL+CC,hR,hR1,by positivity,?_⟩
  intro metric v F hv hF hFI δ hδ hδ1 small A K I m Bm hm bm hom bases low comp M B₀ D hD
    measZero bZero sM jM G sG bG eqG f g h ff gf hf fcap gcap hcap tests eqLow
  have Bm0 : 0 ≤ Bm := (norm_nonneg _).trans (bm 0)
  have B₀zero : 0 ≤ B₀ := (norm_nonneg _).trans (bZero 0 0)
  have baseMeas (i : Fin 3) : Measurable (bases i) := by
    fin_cases i
    · exact hm
    · exact hm.comp radianCycle.symm.measurable
    · exact hm.comp radianCycle.measurable
  have baseNorm (i : Fin 3) (x : Joint) : ‖bases i x‖ ≤ Bm := by
    fin_cases i
    · exact bm x
    · exact bm (radianCycle.symm x)
    · exact bm (radianCycle x)
  have lowMeas (i : Fin 3) : Measurable (low i) :=
    (measurable_radianFourBranchSymbol ϑ hϑ κ _ (baseMeas i) 0).comp
      (pairedFrequencyEquiv A).continuous.measurable
  have lowNorm (i : Fin 3) (p : Joint) : ‖low i p‖ ≤ Bm := by
    let x := pairedFrequencyEquiv A p
    have bound : ‖lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2))‖ ≤ 1 := by
      unfold lowSlotWeight
      exact hRange _ (by positivity)
    change ‖(lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) : ℂ) * bases i x‖ ≤ Bm
    rw [norm_mul,Complex.norm_real]
    exact (mul_le_of_le_one_left (norm_nonneg _) bound).trans (baseNorm i x)
  have lowSupport (i : Fin 3) (p : Joint) (hq : p.2 ≠ 0) (hp : low i p ≠ 0) :
      ‖A p.1‖/‖A p.2‖ ≤ u := by
    have q : A p.2 ≠ 0 := fun h => hq (A.injective (h.trans A.map_zero.symm))
    exact radianFourBranchSymbol_first_low_ratio ϑ hCut hκ hκsmall (bases i) (pairedFrequencyEquiv A p) q hp
  have lowBound (i : Fin 3) (a c d : SchwartzMap E ℂ)
      (aFin : EndpointFiniteAnnulus a) (cFin : EndpointFiniteAnnulus c)
      (acap : ∀ p, radianFourier a p ≠ 0 → A p ∈ K)
      (ccap : ∀ p, radianFourier c p ≠ 0 → A p ∈ K)
      (matchModel : ∀ p : Joint, radianWeight (fun _ => 1) a c d p ≠ 0 →
        ‖A p.1‖/‖A p.2‖ ∈ Ioo (0 : ℝ) b →
        low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖)) :
      ‖radianTrilinearForm (low i) a c d‖ ≤ (CL*D)*(triLpMass a c d 3 3 3).toReal :=
    firstLow metric v F hv hF hFI δ hδ hδ1 small (M i) D hD (sM i) (jM i)
      (low i) Bm B₀ Bm0 B₀zero (lowMeas i) (lowNorm i) (measZero i) (bZero i)
      (lowSupport i) a c d aFin cFin acap ccap matchModel
  have cSupport (p : Joint) (hp : comp p ≠ 0) :
      comparableSlotWeight ϑ κ (A p.1) (A p.2) (A (-(p.1+p.2))) ≠ 0 := by
    intro zeroWeight
    apply hp
    change (comparableSlotWeight ϑ κ (A p.1) (A p.2) (-(A p.1+A p.2)) : ℂ) * m (A p.1,A p.2) = 0
    rw [← map_add,← map_neg,zeroWeight,Complex.ofReal_zero,zero_mul]
  have cHom (t : ℝ) (ht : 0 < t) (p : Joint) : comp (t • p) = comp p := by
    change radianFourBranchSymbol ϑ κ m 3 (pairedFrequencyEquiv A (t • p)) =
      radianFourBranchSymbol ϑ κ m 3 (pairedFrequencyEquiv A p)
    rw [map_smul]
    exact radianFourBranchSymbol_homogeneous ϑ κ m hom 3 t ht (pairedFrequencyEquiv A p)
  have cMeas : AEStronglyMeasurable comp volume :=
    ((measurable_radianFourBranchSymbol ϑ hϑ κ m hm 3).comp
      (pairedFrequencyEquiv A).continuous.measurable).aestronglyMeasurable
  have allCaps (p : Joint) (hp : radianWeight (fun _ => 1) f g h p ≠ 0) :
      A p.1 ∈ K ∧ A p.2 ∈ K ∧ A (-(p.1+p.2)) ∈ K := by
    exact ⟨fcap _ (fun hz => hp (by simp only [radianWeight,hz,mul_zero,zero_mul])),
      gcap _ (fun hz => hp (by simp only [radianWeight,hz,mul_zero,zero_mul])),
      hcap _ (fun hz => hp (by simp only [radianWeight,hz,mul_zero]))⟩
  have hc := comparableBound metric v F hv hF hFI δ hδ hδ1 small
    comp cSupport cHom cMeas G D hD sG bG eqG f g h allCaps
  have result := radianTrilinearForm_normalized_bound_of_four_branches A ϑ hϑ hRange κ
    m hm Bm bm f g h (CL*D) (CL*D) (CL*D) (CC*D)
    (lowBound 0 f g h ff gf fcap gcap (eqLow 0))
    (lowBound 1 g h f gf hf gcap hcap (eqLow 1))
    (lowBound 2 h f g hf ff hcap fcap (eqLow 2))
    hc
  exact result.trans_eq (by ring)

end Burnett.A05
