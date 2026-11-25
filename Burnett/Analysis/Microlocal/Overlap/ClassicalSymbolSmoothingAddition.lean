import Burnett.Analysis.Microlocal.Overlap.CompactDisplacementKernelAction
import Burnett.Analysis.Microlocal.Overlap.CompactSmoothingKernelSymbol

/-! Absorb a compact smooth local kernel without changing the principal symbol. -/
set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Metric Set
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero exists_global_bound_of_degreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ContDiff FourierTransform InnerProductSpace

private theorem exists_bound_of_classicalFrequency (b a : E → ℂ)
    (hb : Continuous b) (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set E)) (hd : DegreeZero a)
    (R C : ℝ) (hLarge : ∀ ξ, R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖b ξ - a ξ‖ ≤ C) :
    ∃ D : ℝ, ∀ ξ, ‖b ξ‖ ≤ D := by
  obtain ⟨A, _, hA⟩ := exists_global_bound_of_degreeZero a ha hd
  obtain ⟨B, _, hB⟩ := ((isCompact_closedBall (0 : E) R).image hb).isBounded.exists_pos_norm_le
  refine ⟨max (C + A) B, fun ξ => ?_⟩
  by_cases hξ : R ≤ ‖ξ‖
  · have hDiff := (le_mul_of_one_le_left (norm_nonneg (b ξ - a ξ))
      (le_add_of_nonneg_right (norm_nonneg ξ))).trans (hLarge ξ hξ)
    calc
      ‖b ξ‖ = ‖(b ξ - a ξ) + a ξ‖ := by rw [sub_add_cancel]
      _ ≤ ‖b ξ - a ξ‖ + ‖a ξ‖ := norm_add_le _ _
      _ ≤ C + A := add_le_add hDiff (hA ξ)
      _ ≤ _ := le_max_left _ _
  · have hξB : ξ ∈ closedBall (0 : E) R := by
      simpa only [mem_closedBall, dist_zero_right] using (le_of_not_ge hξ)
    exact (hB _ (mem_image_of_mem b hξB)).trans (le_max_right _ _)

private theorem firstOrderAction_add_boundedFrequency (p q : E → E → ℂ)
    (u : SchwartzMap E ℂ) (x : E) (hp : Continuous (p x)) (hq : Continuous (q x))
    (hpBound : ∃ CP : ℝ, ∀ ξ, ‖p x ξ‖ ≤ CP) (hqBound : ∃ CQ : ℝ, ∀ ξ, ‖q x ξ‖ ≤ CQ) :
    firstOrderAction (fun y ξ => p y ξ + q y ξ) u x =
      firstOrderAction p u x + firstOrderAction q u x := by
  let F (ξ : E) := (𝓕 (u : E → ℂ)) ξ
  have hF : Integrable F := (SchwartzMap.fourierTransformCLE ℂ u).integrable
  have hPhase : Continuous (fun ξ : E => baseFourierPhase ξ x) :=
    baseFourierPhase_continuous_apply continuous_id continuous_const
  have hI (d : E → ℂ) (hd : Continuous d) (hB : ∃ CD : ℝ, ∀ ξ, ‖d ξ‖ ≤ CD) :
      Integrable (fun ξ => baseFourierPhase ξ x * (d ξ * F ξ)) :=
    (hF.bdd_mul hd.aestronglyMeasurable hB).bdd_mul hPhase.aestronglyMeasurable
      ⟨1, fun ξ => (baseFourierPhase_norm ξ x).le⟩
  simp only [firstOrderAction, Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ξ, baseFourierPhase ξ x * ((p x ξ + q x ξ) * F ξ)) = _
  simp only [add_mul, mul_add]
  exact integral_add (hI _ hp hpBound) (hI _ hq hqBound)

private theorem add_local_orderMinusOne_remainder
    (U : Set E) (hU : IsOpen U) (p a q : E → E → ℂ)
    (hp : ContDiffOn ℝ ∞ (uncurry p) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (hq : ContDiff ℝ ∞ (uncurry q)) (hQ : OrderMinusOneBounds q)
    (L : Set E) (hLU : L ⊆ U) (R : ℝ)
    (hR : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => p y ξ - a y ξ) x‖ ≤ C) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ ξ : E, max 1 R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => (p y ξ + q y ξ) - a y ξ) x‖ ≤ C := by
  intro n
  obtain ⟨C, hC, hCbound⟩ := hR n
  obtain ⟨D, hD, hDbound⟩ := hQ n
  refine ⟨C + D, add_nonneg hC hD, fun x hx ξ hξ => ?_⟩
  have hξ₀ : ξ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hξ))
  let e (y : E) : E × E := (y, ξ)
  have he : ContDiff ℝ ∞ e := contDiff_id.prodMk contDiff_const
  have hPsec : ContDiffOn ℝ ∞ (fun y => p y ξ) U := hp.comp he.contDiffOn (fun _ hy => ⟨hy, mem_univ _⟩)
  have hAsec : ContDiffOn ℝ ∞ (fun y => a y ξ) U := ha.comp he.contDiffOn (fun _ hy => ⟨hy, hξ₀⟩)
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hPD : ContDiffAt ℝ n (fun y => p y ξ - a y ξ) x :=
    ((hPsec.sub hAsec).contDiffAt (hU.mem_nhds (hLU hx))).of_le hn
  have hQD : ContDiffAt ℝ n (fun y => q y ξ) x := ((hq.comp he).contDiffAt (x := x)).of_le hn
  have hEq : (fun y => (p y ξ + q y ξ) - a y ξ) = (fun y => p y ξ - a y ξ) + (fun y => q y ξ) := by
    funext y
    change p y ξ + q y ξ - a y ξ = (p y ξ - a y ξ) + q y ξ
    ring
  rw [hEq, iteratedFDeriv_add_apply hPD hQD]
  let P := iteratedFDeriv ℝ n (fun y => p y ξ - a y ξ) x
  let Q := iteratedFDeriv ℝ n (fun y => q y ξ) x
  calc
    (1 + ‖ξ‖) * ‖P + Q‖ ≤ (1 + ‖ξ‖) * (‖P‖ + ‖Q‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le P Q) (by positivity)
    _ = (1 + ‖ξ‖) * ‖P‖ + (1 + ‖ξ‖) * ‖Q‖ := mul_add _ _ _
    _ ≤ _ := add_le_add (hCbound x hx ξ ((le_max_right _ _).trans hξ)) (hDbound x ξ)

private theorem bounded_classical_frequency_at
    (U : Set E) (p a : E → E → ℂ)
    (hp : ContDiffOn ℝ ∞ (uncurry p) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (hd : ∀ x ∈ U, ∀ s : ℝ, 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ)
    (x : E) (hx : x ∈ U) (R C : ℝ)
    (hC : ∀ ξ : E, R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖p x ξ - a x ξ‖ ≤ C) :
    Continuous (p x) ∧ ∃ D : ℝ, ∀ ξ, ‖p x ξ‖ ≤ D := by
  let e (ξ : E) : E × E := (x, ξ)
  have he : ContDiff ℝ ∞ e := contDiff_const.prodMk contDiff_id
  have hPsec : ContDiff ℝ ∞ (p x) := contDiffOn_univ.mp (hp.comp he.contDiffOn fun _ hy => ⟨hx, hy⟩)
  have hAsec : ContDiffOn ℝ ∞ (a x) ({0}ᶜ : Set E) := ha.comp he.contDiffOn fun _ hy => ⟨hx, hy⟩
  have hDegree : DegreeZero (a x) := by
    intro s hs ξ
    by_cases hξ : ξ = 0
    · rw [hξ, smul_zero]
    · exact hd x hx s hs ξ hξ
  exact ⟨hPsec.continuous, exists_bound_of_classicalFrequency (p x) (a x) hPsec.continuous hAsec hDegree R C hC⟩

private theorem firstOrderAction_add_classical_and_orderMinusOne_at
    (U : Set E) (p a q : E → E → ℂ)
    (hp : ContDiffOn ℝ ∞ (uncurry p) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (hd : ∀ x ∈ U, ∀ s : ℝ, 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ)
    (hq : ContDiff ℝ ∞ (uncurry q)) (hQ : OrderMinusOneBounds q)
    (u : SchwartzMap E ℂ) (x : E) (hx : x ∈ U)
    (R C : ℝ)
    (hC : ∀ ξ, R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖p x ξ - a x ξ‖ ≤ C) :
    firstOrderAction (fun y ξ => p y ξ + q y ξ) u x =
      firstOrderAction p u x + firstOrderAction q u x := by
  obtain ⟨hPcont, hPBound⟩ := bounded_classical_frequency_at U p a hp ha hd x hx R C hC
  have hQcont : Continuous (q x) :=
    hq.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨D, _, hD⟩ := hQ 0
  have hQBound : ∃ CD : ℝ, ∀ ξ, ‖q x ξ‖ ≤ CD := by
    refine ⟨D, fun ξ => ?_⟩
    have h := hD x ξ
    rw [norm_iteratedFDeriv_zero] at h
    exact (le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg ξ))).trans h
  exact firstOrderAction_add_boundedFrequency p q u x hPcont hQcont hPBound hQBound

private theorem firstOrderAction_displacementKernelLeftSymbol_compactSmoothKernel
    (k : E → E → ℂ) (S T : Set E) (hS : IsCompact S) (hT : IsCompact T)
    (hk : ContDiff ℝ ∞ (uncurry k)) (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T)
    (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (displacementKernelLeftSymbol (fun y z => k y (y - z))) u x =
      ∫ y, k x y * u y := by
  have hOutside (v w : E) (hvw : v ∉ S ∨ w ∉ T) : k v w = 0 := by
    change (uncurry k) (v, w) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hMem
    exact hvw.elim (fun hv => hv (hSupp hMem).1) (fun hw => hw (hSupp hMem).2)
  unfold displacementKernelLeftSymbol
  exact firstOrderAction_compactSmoothKernel k S T hS hT hk hOutside u x

/-- A local classical left action plus an actual compact smoothing term admits
one full symbol on the open chart. Its principal part stays the original one. -/
theorem classicalFullSymbol_add_compactSmoothKernel
    (U : Set E) (hU : IsOpen U) (p a k : E → E → ℂ)
    (hp : ContDiffOn ℝ ∞ (uncurry p) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (hd : ∀ x ∈ U, ∀ s : ℝ, 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ)
    (hOrder : ∀ L : Set E, IsCompact L → L ⊆ U → ∃ R : ℝ, ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ L, ∀ ξ : E, R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => p y ξ - a y ξ) x‖ ≤ C)
    (S T : Set E) (hS : IsCompact S) (hT : IsCompact T) (hk : ContDiff ℝ ∞ (uncurry k))
    (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T) :
    let q := displacementKernelLeftSymbol (fun x z => k x (x-z))
    let b (x ξ : E) := p x ξ + q x ξ
    ContDiffOn ℝ ∞ (uncurry b) (U ×ˢ univ) ∧
      (∀ L : Set E, IsCompact L → L ⊆ U → ∃ R : ℝ, ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ L, ∀ ξ : E, R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C) ∧
      ∀ (u : SchwartzMap E ℂ) x, x ∈ U →
        firstOrderAction b u x = firstOrderAction p u x + ∫ y, k x y * u y := by
  intro q b
  have hSymbol := compactSmoothKernel_displacementSymbol_properties hS hT hk hSupp
  have hq : ContDiff ℝ ∞ (uncurry q) := hSymbol.2.1
  have hQ : OrderMinusOneBounds q := hSymbol.2.2
  refine ⟨?_, ?_, ?_⟩
  · change ContDiffOn ℝ ∞ (uncurry p + uncurry q) (U ×ˢ univ)
    exact hp.add hq.contDiffOn
  · intro L hL hLU
    obtain ⟨R, hR⟩ := hOrder L hL hLU
    refine ⟨max 1 R, ?_⟩
    change ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ ξ : E, max 1 R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => (p y ξ + q y ξ) - a y ξ) x‖ ≤ C
    exact add_local_orderMinusOne_remainder U hU p a q hp ha hq hQ L hLU R hR
  · intro u x hx
    have hxU : ({x} : Set E) ⊆ U := singleton_subset_iff.mpr hx
    obtain ⟨R, hR⟩ := hOrder {x} isCompact_singleton hxU
    obtain ⟨C, _, hCb⟩ := hR 0
    have hC (ξ : E) (hξ : R ≤ ‖ξ‖) : (1 + ‖ξ‖) * ‖p x ξ - a x ξ‖ ≤ C := by
      simpa only [norm_iteratedFDeriv_zero] using hCb x (mem_singleton x) ξ hξ
    have hSum := firstOrderAction_add_classical_and_orderMinusOne_at U p a q hp ha hd hq hQ u x hx R C hC
    have hAct : firstOrderAction q u x = ∫ y, k x y * u y :=
      firstOrderAction_displacementKernelLeftSymbol_compactSmoothKernel k S T hS hT hk hSupp u x
    change firstOrderAction (fun y ξ => p y ξ + q y ξ) u x = firstOrderAction p u x + ∫ y, k x y * u y
    exact hSum.trans (congrArg (fun z : ℂ => firstOrderAction p u x + z) hAct)

end Burnett.Microlocal.Overlap
